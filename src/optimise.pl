/*
An optional pass that makes the IR smaller, as statements dominate the output; the result is
ordinary IR. A clausal step cited only by full applications in clausal steps is inlined if copying
it costs less than stating it, Uses × (Size − Skeleton) < Size + size of its clause (see plan/4); a
step proving S = T, where S and T are the same once defined terms are unfolded, is proved by refl.

Each remaining term is normalised in one top-down pass, in an environment from names to values: a
term or a fresh binder, v(T), or a closure c(M, Env), normalised where it is used, so the pass is
linear. It reduces
  - β: a hypothesis argument is dropped if unused, substituted if cheap or used once, else kept;
  - η: λ h, F ... h → F ..., for a hypothesis or step F;
  - sym (sym E) → E, sym refl → refl, and sym (rewrite (λ X. L = R) E M) → rewrite (λ X. R = L) E
    (sym M), so that sym is pushed down to the hypotheses;
  - rewrite (λ X. A) E M → M, if A does not mention X or E is refl.
Fresh binders are Prolog variables, numbered at the end (close:number_binders/1); a step's own
binders keep their names, as its type mentions them.
*/
:- module(optimise, [optimise/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(utils).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(close).

% the steps are optimised again if a definition is inlined, as its step is then proved by refl
optimise :-
  optimise_steps,
  ( inline_definitions -> optimise_steps ; true ).

optimise_steps :-
  findall(Name, ir_step(Name, _, _), Names),
  use_counts(Uses),
  empty_assoc(Empty),
  foldl(plan(Uses), Names, Empty, Inlined),
  findall(ir_step(Name, Conclusion, Justification),
          ( member(Name, Names),
            \+ get_assoc(Name, Inlined, _),
            ir_step(Name, Conclusion, Justification0),
            optimised(Inlined, Name, Conclusion, Justification0, Justification) ),
          Steps),
  live(Names, Steps, Live),
  forget(ir_step(_, _, _)),
  each(( member(Step, Steps), Step = ir_step(Name, _, _), get_assoc(Name, Live, _) ), record(Step)).

% the steps that the roots (the last refutation, and the conjecture) still cite, once inlined steps
% cite nothing, and refl proves what it can; and every definition, as it defines its symbol. A step may
% be proved but not cited, as by a step that names it as a parent but does not need it
live(Names, Steps, Live) :-
  findall(Name, ( member(Name, Names), ir_step(Name, clause([], []), _) ), Refutations),
  findall(Name, ( member(Name, Names), ir_step(Name, _, conjecture(_, _, _)) ), Conjectures),
  ( last(Refutations, R) -> Roots = [R|Conjectures] ; Roots = Conjectures ),
  empty_assoc(Empty),
  foldl(reached(Steps), Roots, Empty, Live0),
  findall(Name, member(ir_step(Name, _, definition(_, _, _)), Steps), Ds),
  findall(Name, member(ir_step(Name, _, skolem_def(_, _, _)), Steps), Ss),
  append(Ds, Ss, Defs),
  foldl(reached(Steps), Defs, Live0, Live).

reached(_, Name, Live, Live) :- get_assoc(Name, Live, _), !.
reached(Steps, Name, Live0, Live) :-
  put_assoc(Name, Live0, true, Live1),
  (   memberchk(ir_step(Name, _, J), Steps)
  ->  findall(P, reference(J, P), Ps),
      foldl(reached(Steps), Ps, Live1, Live)
  ;   Live = Live1
  ).

/********************************************************************************
 * inlining function definitions
 ********************************************************************************/

% a function definition is inlined where copying its body costs less than stating it, as for a step:
% Uses × (Size − 1) < Size + 2, for its body with the definitions before it inlined (a body cites only
% definitions before it). Its symbol is then gone, and its step is T = T, proved by refl
inline_definitions :-
  findall(F/N-(Bs-Body),
          ( ir_step(_, clause(_, _), definition(F, Bs, Body)), introduced(F, definition), length(Bs, N) ),
          Definitions),
  symbol_uses(Definitions, Uses),
  empty_assoc(Empty),
  foldl(inlined_definition(Uses), Definitions, Empty, Inlined),
  \+ empty_assoc(Inlined),
  findall(ir_step(Name, Conclusion, Justification),
          ( ir_step(Name, Conclusion0, Justification0),
            restated(Inlined, Conclusion0, Justification0, Conclusion, Justification) ),
          Steps),
  forget(ir_step(_, _, _)),
  each(member(Step, Steps), record(Step)),
  each(( gen_assoc(F/_, Inlined, _), symbol(F, Ps, Args, Sort) ), forget(symbol(F, Ps, Args, Sort))).

% the occurrences of each defined symbol: in a definition, only in its body, as its conclusion restates it
symbol_uses(Definitions, Uses) :-
  findall(F-0, member(F-_, Definitions), Zeros),
  list_to_assoc(Zeros, Uses0),
  findall(F/N,
          ( ir_step(_, Conclusion, Justification),
            ( Justification = definition(_, _, T) -> true ; T = Conclusion-Justification ),
            subterm(T, U), ( atom(U) ; compound(U) ), functor(U, F, N), get_assoc(F/N, Uses0, _) ),
          Occurrences),
  foldl(count_symbol, Occurrences, Uses0, Uses).

count_symbol(F, Uses0, Uses) :- get_assoc(F, Uses0, N0), N is N0 + 1, put_assoc(F, Uses0, N, Uses).

inlined_definition(Uses, F-(Bs-Body0), Inlined0, Inlined) :-
  inlined_term(Inlined0, Body0, Body),
  term_size(Body, Size),
  get_assoc(F, Uses, N),
  ( N * (Size - 1) < Size + 2 -> put_assoc(F, Inlined0, Bs-Body, Inlined) ; Inlined = Inlined0 ).

% the term T0, or any IR around it, with each inlined symbol replaced by its body (already inlined
% itself); only defined symbols are inlined, which are not the names of steps or hypotheses
inlined_term(_, T, T) :- var(T), !.
inlined_term(Inlined, T0, T) :-
  ( atom(T0) ; compound(T0) ),
  functor(T0, F, N),
  get_assoc(F/N, Inlined, Bs-Body), !,
  T0 =.. [_|As0],
  maplist(inlined_term(Inlined), As0, As),
  binder_variables(Bs, Xs),
  substitute_all(Xs, As, Body, T).
inlined_term(Inlined, T0, T) :-
  compound(T0), !,
  map_arguments(inlined_term(Inlined), T0, T).
inlined_term(_, T, T).

% an inlined definition's step states T = T, and is proved by refl
restated(Inlined, Conclusion0, definition(F, Bs, _), Conclusion, proof(M)) :-
  length(Bs, N), get_assoc(F/N, Inlined, _), !,
  inlined_term(Inlined, Conclusion0, Conclusion),
  reflexive_term(Conclusion, M).
restated(Inlined, Conclusion0, Justification0, Conclusion, Justification) :-
  inlined_term(Inlined, Conclusion0, Conclusion),
  inlined_term(Inlined, Justification0, Justification).

/********************************************************************************
 * which steps are inlined
 ********************************************************************************/

% Uses maps each step to the number of its citations, or to bad if one cannot inline it
use_counts(Uses) :-
  findall(Name-Use, ( ir_step(Host, Conclusion, Justification), citation(Host, Conclusion, Justification, Name, Use) ), Citations),
  empty_assoc(Empty),
  foldl(count_use, Citations, Empty, Uses).

count_use(Name-Use, Uses0, Uses) :-
  ( get_assoc(Name, Uses0, N0) -> true ; N0 = 0 ),
  ( ( Use == bad ; N0 == bad ) -> N = bad ; N is N0 + 1 ),
  put_assoc(Name, Uses0, N, Uses).

% a citation is good if it is a full application in the term of a clausal step
citation(Host, Conclusion, proof(_), Name, Use) :- !,
  step_term(Host, Conclusion, M),
  cited(M, Name, As),
  ( clausal(Host, Conclusion), full(Name, As) -> Use = good ; Use = bad ).
citation(_, _, Justification, Name, bad) :- reference(Justification, Name).

clausal(Name, clause(_, _)) :- \+ formula_step(Name).

full(Name, As) :- ir_step(Name, clause(Bs, Ls), _), length(Bs, M), length(Ls, N), length(As, K), K =:= M + N.

% the steps cited in a proof term, with their arguments (a first-order term cites none)
cited('$lam'(_, _, M), Name, As) :- !, cited(M, Name, As).
cited(M, Name, As) :- M = _ @ _, !,
  spine(M, F, As0),
  ( named_step(F), Name = F, As = As0 ; compound(F), cited(F, Name, As) ; member(A, As0), cited(A, Name, As) ).
cited(F, F, []) :- named_step(F).

% Inlined maps each inlined step to its size, with the steps it inlines: those for which copying
% costs less than stating them
plan(Uses, Name, Inlined0, Inlined) :-
  step_term(Name, Conclusion, M),
  clausal(Name, Conclusion),
  get_assoc(Name, Uses, N),
  N \== bad, !,
  (   reflexivity(Conclusion)
  ->  put_assoc(Name, Inlined0, 0, Inlined)
  ;   inlined_size(Inlined0, M, Size),
      clause_type(Conclusion, T),
      term_size(T, TypeSize),
      skeleton_size(Name, Conclusion, M, Skeleton),
      (   N * (Size - Skeleton) < Size + TypeSize
      ->  put_assoc(Name, Inlined0, Size, Inlined)
      ;   Inlined = Inlined0
      )
  ).

plan(_, _, Inlined, Inlined).

% the size of a citation of the step, applied to its binders, which its arguments replace: only if each
% binder occurs at most once in its term M, so that inlining copies no argument; else nothing is saved
skeleton_size(Name, clause(Bs, Ls), M, Size) :-
  binder_variables(Bs, Xs),
  spine_binders(M, Ys),
  spine_body(M, B),
  \+ ( member(Y, Ys), occurrences(B, Y, K), K > 1 ), !,
  length(Xs, K),
  findall('$VAR'(I), ( nth0(J, Ls, _), I is K + J ), Hs),
  append(Xs, Hs, As),
  curried(Name, As, Citation),
  term_size(Citation, Size).
skeleton_size(_, _, _, 0).

% the binders of the λs around a step's term
spine_binders('$lam'(X, _, M), [X|Xs]) :- !, spine_binders(M, Xs).
spine_binders(_, []).

occurrences(T, X, N) :- counted(X, T, 0, N).

% folded over T, not by subterm/2, which backtracks through every level of a curried application
counted(X, T, N0, N) :- T == X, !, N is N0 + 1.
counted(X, T, N0, N) :- compound(T), !, T =.. [_|As], foldl(counted(X), As, N0, N).
counted(_, _, N, N).

% the term of a step: its proof, or refl for an equation whose sides are the same once defined terms
% are unfolded, under the λs of its binders
step_term(Name, Conclusion, M) :-
  ir_step(Name, Conclusion, proof(M0)),
  ( reflexivity(Conclusion) -> reflexive_term(Conclusion, M) ; M = M0 ).

reflexivity(clause(_, [L])) :- terms_unfolded(L, '$='(_, S, T)), S == T.

reflexive_term(clause(Bs, [L]), M) :-
  length(Bs, N),
  lams(Bs, '$lam'('$VAR'(N), '$proof'(~L), '$VAR'(N) @ '$refl'), M).

lams([], M, M).
lams([X:S|Bs], M0, '$lam'(X, S, M)) :- lams(Bs, M0, M).

% the size of the body of a step's term, under the λs of its binders, which inlining removes, with
% the steps it inlines
inlined_size(Inlined, M, Size) :-
  spine_body(M, B),
  term_size(B, Size0),
  findall(K, ( cited(M, P, _), get_assoc(P, Inlined, K) ), Ks),
  sum_list(Ks, Size1),
  Size is Size0 + Size1.

spine_body('$lam'(_, _, M), B) :- !, spine_body(M, B).
spine_body(M, M).

/********************************************************************************
 * normalisation
 ********************************************************************************/

% a failure is a bug, and the steps it inlines are gone, so it is an error
optimised(Inlined, Name, Conclusion, proof(_), proof(M)) :- !,
  step_term(Name, Conclusion, M0),
  ( host(Inlined, M0, M) -> number_binders(M) ; throw(optimisation_failed(Name)) ).
optimised(_, _, _, Justification, Justification).

% the λs of a step's own binders are kept, with their names, as its type mentions its eigenvariables
host(Inlined, M0, M) :-
  hypothesis_uses(M0, Uses),
  empty_assoc(Empty),
  own_lams(env(Inlined, Empty, Uses), M0, M).

own_lams(Env, '$lam'(X, A, M0), '$lam'(X, A1, M)) :- !,
  substituted(Env, A, A1),
  bind(Env, X, v(X), Env1),
  own_lams(Env1, M0, M).
own_lams(Env, M0, M) :- normal(Env, M0, M).

% Env is env(Inlined, Bindings, Uses), with Uses those of the term being normalised. A variable is
% bound to v(V), a normal value: a binder's new name, or the term of an eigenvariable; or to
% c(M, Env), a closure: the proof of a hypothesis, normalised where it is used
bind(env(I, B0, U), X, V, env(I, B, U)) :- put_assoc(X, B0, V, B).

binding(env(_, B, _), X, V) :- get_assoc(X, B, V).

use(env(_, _, U), X, Use) :- ( get_assoc(X, U, Use) -> true ; Use = 0 ).

% the term with its eigenvariables replaced by their values (free ones are kept, by name)
substituted(Env, '$VAR'(N), T) :- integer(N), !, ( binding(Env, '$VAR'(N), v(T)) -> true ; T = '$VAR'(N) ).
% the motive of a rewrite binds a fresh variable
substituted(Env, '$abs'(X:S0, A0), '$abs'(Y:S, A)) :- !,
  substituted(Env, S0, S),
  bind(Env, X, v(Y), Env1),
  substituted(Env1, A0, A).
substituted(Env, T0, T) :- compound(T0), !, map_arguments(substituted(Env), T0, T).
substituted(_, T, T).

normal(Env, '$lam'(X, A, M0), M) :- !,
  substituted(Env, A, A1),
  bind(Env, X, v(Y), Env1),
  normal(Env1, M0, M1),
  ( proof_annotation(A) -> eta(Y, A1, M1, M) ; M = '$lam'(Y, A1, M1) ).
normal(Env, M0, M) :- M0 = _ @ _, !,
  spine(M0, F, As),
  arguments(Env, As, Cs),
  applied(Env, F, Cs, M).
normal(Env, F, M) :- applied(Env, F, [], M).

% the arguments As in Env: a proof is a closure c(M, Env), and a first-order term is normal, v(T),
% with its eigenvariables replaced; a variable is its value (a free one is kept, by name). Not by
% findall, which would copy the binders of Env
arguments(Env, As, Cs) :- maplist(argument(Env), As, Cs).

argument(Env, X, C) :- X = '$VAR'(_), !, ( binding(Env, X, C) -> true ; C = v(X) ).
argument(Env, M, c(M, Env)) :- proof_argument(M), !.
argument(Env, T0, v(T)) :- substituted(Env, T0, T).

forced(c(M0, Env), M) :- normal(Env, M0, M).
forced(v(T), T).

% F, in Env, applied to the arguments Cs (closures or normal values)
applied(Env, F, Cs, M) :-
  F = '$VAR'(_), !,
  binding(Env, F, V),
  (   V = v(Y)
  ->  maplist(forced, Cs, Ms), curried(Y, Ms, M)
  ;   V = c(M0, Env0), applied_term(Env0, M0, Cs, M)
  ).
applied(Env, F, Cs, M) :-
  Env = env(Inlined, _, _),
  get_assoc(F, Inlined, _), !,
  step_term(F, _, M0),
  hypothesis_uses(M0, Uses),
  empty_assoc(Empty),
  reduced(env(Inlined, Empty, Uses), M0, Cs, M).
applied(Env, F, Cs, M) :- compound(F), !, applied_term(Env, F, Cs, M).
applied(_, F, Cs, M) :-
  atom(F),
  maplist(forced, Cs, Ms),
  built(F, Ms, M).

% normal terms may be hypotheses, which are variables, so they are matched with care
built('$sym', [E0], E) :- nonvar(E0), E0 = Sym @ E, Sym == '$sym', !.
built('$sym', [E], E) :- E == '$refl', !.
built('$sym', [E0], M) :-
  rewrite_parts(E0, Motive0, E, M0), nonvar(Motive0), Motive0 = '$abs'(X, '$='(A, L, R)), !,
  built('$sym', [M0], M1),
  curried('$rewrite', ['$abs'(X, '$='(A, R, L)), E, M1], M).
% a rewrite whose motive does not mention its variable, or by refl, is its proof
built('$rewrite', ['$abs'(Y:_, A), E, M0|Ms], M) :- ( \+ occurs(Y, A) ; E == '$refl' ), !, curried(M0, Ms, M).
built(F, Ms, M) :- curried(F, Ms, M).

% the term M0 of a substituted hypothesis, at the head of an application, whose arguments, if it is
% an application, come before Cs
applied_term(Env, M0, [], M) :- !, normal(Env, M0, M).
applied_term(Env, M0, Cs, M) :- M0 = _ @ _, !,
  spine(M0, G, As),
  arguments(Env, As, Cs0),
  append(Cs0, Cs, Cs1),
  applied(Env, G, Cs1, M).
applied_term(Env, '$lam'(X, A, M0), Cs, M) :- !, reduced(Env, '$lam'(X, A, M0), Cs, M).
applied_term(Env, F, Cs, M) :- applied(Env, F, Cs, M).

% β-reduction: the binders of the λs take the arguments, in order
reduced(Env, '$lam'(X, A, M0), [C|Cs], M) :- \+ proof_annotation(A), !,
  forced(C, T),
  bind(Env, X, v(T), Env1),
  reduced(Env1, M0, Cs, M).
reduced(Env, '$lam'(X, A, M0), [C|Cs], M) :- !,
  use(Env, X, Use),
  (   ( Use == 0 ; A == '$inferred' ; C = v(_) ; C = c(V0, Env0), substitutable(Env0, V0, Use) )
  ->  bind(Env, X, C, Env1), reduced(Env1, M0, Cs, M)
  ;   substituted(Env, A, A1),
      forced(C, V),
      bind(Env, X, v(Y), Env1),
      reduced(Env1, M0, Cs, N),
      M = '$lam'(Y, A1, N) @ V
  ).
reduced(Env, M0, Cs, M) :- applied_term(Env, M0, Cs, M).

% a value may replace a hypothesis used Uses times if it is cheap or used once, as any term may be a
% head, even where the checker infers its type: the binder's type may unfold the value's, but only
% function terms, or a defined atom at its top, which the checker unfolds there
substitutable(Env, V, _) :- cheap(Env, V), !.
substitutable(_, _, 1).

% a hypothesis or a constant (not an inlined step), applied to terms only (or to variables that are
% not closures), so copying it is cheap
cheap(Env, F) :- F = '$VAR'(_), !, binding(Env, F, V), ( V = c(V0, Env0) -> cheap(Env0, V0) ; true ).
cheap(Env, M) :- M = _ @ _, !,
  spine(M, F, As),
  maplist(cheap_argument(Env), As),
  cheap(Env, F).
cheap(env(Inlined, _, _), F) :- atom(F), \+ get_assoc(F, Inlined, _).

cheap_argument(Env, X) :- X = '$VAR'(_), !, \+ binding(Env, X, c(_, _)).
cheap_argument(_, T) :- \+ proof_argument(T).

% η: λ h, F ... h is F ..., if h does not occur in F ...; but for a rule or built-in, whose type
% depends on its arguments
eta(Y, _, M0, M) :-
  nonvar(M0),
  M0 = G @ X,
  X == Y,
  spine(G, F, _),
  ( hypothesis(F) ; atom(F), \+ head_type(F, _) ),
  \+ occurs(Y, G), !,
  M = G.
eta(Y, A, M, '$lam'(Y, A, M)).

% a hypothesis of a normal term: a fresh binder, or one of the step's own, which keeps its name
hypothesis(Y) :- var(Y), !.
hypothesis('$VAR'(_)).

% the number of uses of each hypothesis of a term
hypothesis_uses(M, Uses) :-
  phrase(uses(M), Occurrences),
  msort(Occurrences, Sorted),
  empty_assoc(Empty),
  foldl(add_use, Sorted, Empty, Uses).

uses('$lam'(_, _, M)) --> !, uses(M).
uses(M @ N) --> !, uses(M), uses(N).
uses(F) --> ( { F = '$VAR'(_) } -> [F] ; [] ).

add_use(X, Uses0, Uses) :-
  ( get_assoc(X, Uses0, N0) -> true ; N0 = 0 ),
  N is N0 + 1,
  put_assoc(X, Uses0, N, Uses).

