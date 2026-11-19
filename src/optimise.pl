/*
An optional pass over the IR (see ir.pl), between reconstruction and the back end, that makes proofs
smaller: some clausal steps are inlined where they are cited, so their statements are not printed,
and obvious redundancies are simplified away. The result is ordinary IR, so every back end (and the
checker) reads it as before.

A step is inlined if it is a clause proved by a term, not a step between formulas, and is cited only
by full applications (all its terms and hypotheses) in the proof terms of clausal steps (not between
formulas), and its term (with what it inlines, under the λs of its binders) is small enough that
copying it where it is cited costs less than stating it: each use grows by Size - Skeleton, where the
skeleton is the citation itself, applied to the step's binders, if each binder occurs at most once in
the term (so no argument is copied; else it is 0), and inlining saves the term and its clause, so
Uses * (Size - Skeleton) < Size + size of the clause. A step that just forwards to another
(λ x h. f x h) costs nothing.
A step that proves an equation S = T whose sides are the same once defined terms are unfolded is
proved by λ xs h. h refl instead (whatever it cites), and is always inlined, as K refl is no larger
than the citation it replaces.

Each remaining proof term is normalised in one pass, top-down, in an environment that maps the names
bound in the original term to their values: an eigenvariable to a term, a hypothesis to a fresh
binder, or to a closure c(M, Env), a term to be normalised where it is used. So an inlined step is a
β-redex that is reduced by binding its binders, and a substituted hypothesis is normalised once, at
its single use, which keeps the pass linear. Then

  - β: an inlined step, or a λ at the head of an application (a redex, or substituted there), binds
    its binders to the arguments; a hypothesis argument is dropped if unused, and substituted if
    cheap (a hypothesis or constant, applied to terms only) or used once (anywhere, as any term
    may be a head), else it stays a redex; '$nex' arguments stay, as the IR states the type of
    '$nex' only in the λ of its redex;
  - η: λ h, F ... h → F ..., for a hypothesis h, where F is a hypothesis or a step;
  - sym (sym E) → E, sym refl → refl, and sym of a rewrite of an equation L = R is the rewrite of
    sym of its proof, by R = L, so that sym is pushed down to the hypotheses;
  - a rewrite whose motive does not mention its variable, or by reflexivity, is its proof.

Fresh binders are Prolog variables (an eigenvariable is '$VAR'(N), N unbound), numbered at the end:
the eigenvariables of a clause's own binders keep their names, as its type mentions them.
*/
:- module(optimise, [optimise/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(utils).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(close).

optimise :-
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
  cited(M, Name, Ts, Ms),
  ( clausal(Host, Conclusion), full(Name, Ts, Ms) -> Use = good ; Use = bad ).
citation(_, _, Justification, Name, bad) :- reference(Justification, Name).

clausal(Name, clause(_, _)) :- \+ formula_step(Name).

full(Name, Ts, Ms) :- ir_step(Name, clause(Bs, Ls), _), same_length(Bs, Ts), same_length(Ls, Ms).

% the steps cited in a proof term, with their arguments
cited(lam(_, _, M), Name, Ts, Ms) :- !, cited(M, Name, Ts, Ms).
cited(rewrite(_, _, E, M), Name, Ts, Ms) :- !, ( cited(E, Name, Ts, Ms) ; cited(M, Name, Ts, Ms) ).
cited(app(F, Ts0, Ms0), Name, Ts, Ms) :- !,
  ( step_name(F), Name = F, Ts = Ts0, Ms = Ms0 ; compound(F), cited(F, Name, Ts, Ms) ; member(M, Ms0), cited(M, Name, Ts, Ms) ).
cited(F, F, [], []) :- step_name(F).

step_name(F) :- atom(F), ir_step(F, _, _), !.

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
  findall(h(I), nth0(I, Ls, _), Hs),
  term_size(app(Name, Xs, Hs), Size).
skeleton_size(_, _, _, 0).

% the binders of the λs around a step's term
spine_binders(lam(X, _, M), [X|Xs]) :- !, spine_binders(M, Xs).
spine_binders(_, []).

occurrences(T, X, N) :- findall(x, ( subterm(T, U), U == X ), Us), length(Us, N).

% the term of a step: its proof, or refl for an equation whose sides are the same once defined terms
% are unfolded, under the λs of its binders
step_term(Name, Conclusion, M) :-
  ir_step(Name, Conclusion, proof(M0)),
  ( reflexivity(Conclusion) -> reflexive_term(Conclusion, M) ; M = M0 ).

reflexivity(clause(_, [L])) :- terms_unfolded(L, '$='(_, S, T)), S == T.

reflexive_term(clause(Bs, [L]), M) :- lams(Bs, lam(h(0), ~L, app(h(0), [], [app('$refl', [], [])])), M).

lams([], M, M).
lams([X:S|Bs], M0, lam(X, S, M)) :- lams(Bs, M0, M).

% the size of the body of a step's term, under the λs of its binders, which inlining removes, with
% the steps it inlines
inlined_size(Inlined, M, Size) :-
  spine_body(M, B),
  term_size(B, Size0),
  findall(K, ( cited(M, P, _, _), get_assoc(P, Inlined, K) ), Ks),
  sum_list(Ks, Size1),
  Size is Size0 + Size1.

spine_body(lam(_, _, M), B) :- !, spine_body(M, B).
spine_body(M, M).

term_size(T, N) :- compound(T), !, T =.. [_|Ts], foldl(add_size, Ts, 1, N).
term_size(_, 1).

add_size(T, N0, N) :- term_size(T, K), N is N0 + K.

/********************************************************************************
 * normalisation
 ********************************************************************************/

% a failure is a bug, and the steps it inlines are gone, so it is an error
optimised(Inlined, Name, Conclusion, proof(_), proof(M)) :- !,
  step_term(Name, Conclusion, M0),
  (   host(Inlined, M0, M1)
  ->  first_fresh(Conclusion, K),
      number_eigenvariables(M1, K, _),
      name_binders(M1, 0, _),
      M = M1
  ;   throw(optimisation_failed(Name))
  ).
optimised(_, _, _, Justification, Justification).

% eigenvariables are numbered after those of the conclusion, which keep their names
first_fresh(Conclusion, K) :-
  findall(N, ( subterm(Conclusion, '$VAR'(N)), integer(N) ), Ns),
  max_list([-1|Ns], Max),
  K is Max + 1.

% the λs of a clause's own binders are kept, with their names for its eigenvariables
host(Inlined, M0, M) :-
  hypothesis_uses(M0, Uses),
  empty_assoc(Empty),
  spine(env(Inlined, Empty, Uses), M0, M).

spine(Env, lam(X, A, M0), lam(Y, A1, M)) :- !,
  substituted(Env, A, A1),
  ( X = '$VAR'(_) -> Y = X, bind(Env, X, X, Env1) ; bind(Env, X, v(Y), Env1) ),
  spine(Env1, M0, M).
spine(Env, M0, M) :- normal(Env, M0, M).

% Env is env(Inlined, Bindings, Uses), with Uses those of the term being normalised
bind(env(I, B0, U), X, V, env(I, B, U)) :- put_assoc(X, B0, V, B).

binding(env(_, B, _), X, V) :- get_assoc(X, B, V).

use(env(_, _, U), X, Use) :- ( get_assoc(X, U, Use) -> true ; Use = 0 ).

% the term with its eigenvariables replaced by their values (free ones are kept, by name)
substituted(Env, '$VAR'(N), T) :- integer(N), !, ( binding(Env, '$VAR'(N), T) -> true ; T = '$VAR'(N) ).
substituted(Env, T0, T) :- compound(T0), !, T0 =.. [F|As0], maplist(substituted(Env), As0, As), T =.. [F|As].
substituted(_, T, T).

normal(Env, lam(X, A, M0), M) :- !,
  substituted(Env, A, A1),
  (   X = '$VAR'(_)
  ->  Y = '$VAR'(_), bind(Env, X, Y, Env1), normal(Env1, M0, M1), M = lam(Y, A1, M1)
  ;   bind(Env, X, v(Y), Env1), normal(Env1, M0, M1), eta(Y, A1, M1, M)
  ).
normal(Env, rewrite(X:S0, A0, E0, M0), M) :- !,
  Y = '$VAR'(_),
  substituted(Env, S0, S),
  bind(Env, X, Y, Env1),
  substituted(Env1, A0, A),
  normal(Env, E0, E),
  normal(Env, M0, M1),
  ( ( \+ occurs(Y, A) ; nonvar(E), E = app('$refl', _, _) ) -> M = M1 ; M = rewrite(Y:S, A, E, M1) ).
normal(Env, app(F, Ts0, Ms), M) :- !,
  maplist(substituted(Env), Ts0, Ts),
  closures(Env, Ms, Cs),
  applied(Env, F, Ts, Cs, M).
normal(Env, F, M) :- applied(Env, F, [], [], M).

% not by findall, which would copy the binders of Env
closures(Env, Ms, Cs) :- maplist(closure(Env), Ms, Cs).

closure(Env, M, c(M, Env)).

forced(c(M0, Env), M) :- normal(Env, M0, M).

% F, in Env, applied to the terms Ts (normal) and the proofs Cs (closures)
applied(Env, F, Ts, Cs, M) :-
  F = h(_), !,
  binding(Env, F, V),
  (   V = v(Y)
  ->  maplist(forced, Cs, Ms), application(Y, Ts, Ms, M)
  ;   V = c(M0, Env0), applied_term(Env0, M0, Ts, Cs, M)
  ).
applied(Env, F, Ts, Cs, M) :-
  Env = env(Inlined, _, _),
  get_assoc(F, Inlined, _), !,
  step_term(F, _, M0),
  hypothesis_uses(M0, Uses),
  empty_assoc(Empty),
  reduced(env(Inlined, Empty, Uses), M0, Ts, Cs, M).
applied(Env, F, Ts, Cs, M) :- compound(F), !, applied_term(Env, F, Ts, Cs, M).
applied(_, F, Ts, Cs, M) :-
  atom(F),
  maplist(forced, Cs, Ms),
  built(F, Ts, Ms, M).

% a hypothesis alone is bare, but a step or a built-in is applied
application(Y, [], [], Y) :- var(Y), !.
application(Y, Ts, Ms, app(Y, Ts, Ms)).

% normal terms may be hypotheses, which are variables, so they are matched with care
built('$sym', [], [E0], E) :- nonvar(E0), E0 = app('$sym', [], [E]), !.
built('$sym', [], [E], E) :- nonvar(E), E = app('$refl', [], []), !.
built('$sym', [], [E0], rewrite(X, '$='(A, R, L), E, M)) :-
  nonvar(E0), E0 = rewrite(X, '$='(A, L, R), E, M0), !,
  built('$sym', [], [M0], M).
built(F, Ts, Ms, app(F, Ts, Ms)).

% the term M0 of a substituted hypothesis, at the head of an application
applied_term(Env, M0, [], [], M) :- !, normal(Env, M0, M).
applied_term(Env, app(G, Ts0, Ms0), Ts, Cs, M) :- ( Ms0 == [] ; Ts == [] ), !,
  maplist(substituted(Env), Ts0, Ts1),
  closures(Env, Ms0, Cs0),
  (   Ms0 == []
  ->  append(Ts1, Ts, Ts2), applied(Env, G, Ts2, Cs, M)
  ;   Ts == [],
      append(Cs0, Cs, Cs1), applied(Env, G, Ts1, Cs1, M)
  ).
applied_term(Env, lam(X, A, M0), Ts, Cs, M) :- !, reduced(Env, lam(X, A, M0), Ts, Cs, M).
% ...or else it stays at the head, as a proof applied to proofs is not merged with terms
applied_term(Env, M0, Ts, Cs, app(M, Ts, Ms)) :- ( M0 = app(_, _, _) ; M0 = rewrite(_, _, _, _) ), !,
  normal(Env, M0, M),
  maplist(forced, Cs, Ms).
applied_term(Env, F, Ts, Cs, M) :- applied(Env, F, Ts, Cs, M).

% β-reduction: the binders of the λs take the arguments, terms first
reduced(Env, lam(X, _, M0), [T|Ts], Cs, M) :- !,
  X = '$VAR'(_),
  bind(Env, X, T, Env1),
  reduced(Env1, M0, Ts, Cs, M).
reduced(Env, lam(X, A, M0), [], [C|Cs], M) :- !,
  use(Env, X, Use),
  C = c(V0, Env0),
  (   ( Use == 0 ; A == '$inferred' ; substitutable(Env0, V0, Use) )
  ->  bind(Env, X, C, Env1), reduced(Env1, M0, [], Cs, M)
  ;   substituted(Env, A, A1),
      forced(C, V),
      bind(Env, X, v(Y), Env1),
      reduced(Env1, M0, [], Cs, N),
      M = app(lam(Y, A1, N), [], [V])
  ).
reduced(Env, M0, Ts, Cs, M) :- applied_term(Env, M0, Ts, Cs, M).

% a value may replace a hypothesis used Uses times if it is cheap or used once, as any term may be a
% head, even where the checker infers its type: the binder's type may unfold the value's, but only
% function terms, or a defined atom at its top, which the checker unfolds there
substitutable(_, app('$nex', _, _), _) :- !, fail.
substitutable(Env, V, _) :- cheap(Env, V), !.
substitutable(_, _, 1).

% a hypothesis or a constant (not an inlined step), applied to terms only, so copying it is cheap
cheap(Env, F) :- F = h(_), !, binding(Env, F, V), ( V = c(V0, Env0) -> cheap(Env0, V0) ; true ).
cheap(Env, app(F, _, [])) :- !, cheap(Env, F).
cheap(env(Inlined, _, _), F) :- atom(F), \+ get_assoc(F, Inlined, _).

% η: λ h, F ... h is F ..., if h does not occur in F ...; but for a rule or built-in, whose type
% depends on its arguments
eta(Y, _, M0, M) :-
  nonvar(M0),
  M0 = app(F, Ts, Ms),
  ( var(F) ; atom(F), \+ head_type(F, _) ),
  append(Ms1, [X], Ms),
  X == Y,
  \+ occurs(Y, F-Ts-Ms1), !,
  application(F, Ts, Ms1, M).
eta(Y, A, M, lam(Y, A, M)).

% the number of uses of each hypothesis of a term
hypothesis_uses(M, Uses) :-
  phrase(uses(M), Occurrences),
  msort(Occurrences, Sorted),
  empty_assoc(Empty),
  foldl(add_use, Sorted, Empty, Uses).

uses(lam(_, _, M)) --> !, uses(M).
uses(rewrite(_, _, E, M)) --> !, uses(E), uses(M).
uses(app(F, _, Ms)) --> !, uses(F), foldl(uses, Ms).
uses(F) --> ( { F = h(_) } -> [F] ; [] ).

add_use(X, Uses0, Uses) :-
  ( get_assoc(X, Uses0, N0) -> true ; N0 = 0 ),
  N is N0 + 1,
  put_assoc(X, Uses0, N, Uses).

% the eigenvariables bound in the term are numbered from N0, in order; a hypothesis is still a variable
number_eigenvariables(V, N, N) :- var(V), !.
number_eigenvariables(lam(X, _, M), N0, N) :- !, number_binder(X, N0, N1), number_eigenvariables(M, N1, N).
number_eigenvariables(rewrite(X:_, _, E, M), N0, N) :- !,
  number_binder(X, N0, N1), number_eigenvariables(E, N1, N2), number_eigenvariables(M, N2, N).
number_eigenvariables(app(F, _, Ms), N0, N) :- !, foldl(number_eigenvariables, Ms, N0, N1), number_eigenvariables(F, N1, N).
number_eigenvariables(_, N, N).

number_binder(X, N0, N) :- nonvar(X), X = '$VAR'(I), var(I), !, I = N0, N is N0 + 1.
number_binder(_, N, N).
