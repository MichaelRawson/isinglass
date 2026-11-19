/*
An optional pass over the IR (see ir.pl), between reconstruction and the back end, that makes proofs
smaller: some clausal steps are inlined where they are cited, so their statements are not printed,
and obvious redundancies are simplified away. The result is ordinary IR, so every back end (and the
checker) reads it as before.

A step is inlined if it is a clause proved by a term, not a step between formulas, and is cited only
by full applications (all its terms and hypotheses) in the proof terms of clausal steps (not between
formulas), and either once, or its term (with what it inlines, under the λs of its binders) is small
enough that copying it costs less than stating its clause: (Uses - 1) * Size < size of the clause.

Each remaining proof term is normalised in one pass, top-down, in an environment that maps the names
bound in the original term to their values: an eigenvariable to a term, a hypothesis to a fresh
binder, or to a closure c(M, Env), a term to be normalised where it is used. So an inlined step is a
β-redex that is reduced by binding its binders, and a substituted hypothesis is normalised once, at
its single use, which keeps the pass linear. Then

  - β: an inlined step, or a λ at the head of an application (a redex, or substituted there), binds
    its binders to the arguments; a hypothesis argument is dropped if unused, and substituted if
    cheap (a hypothesis or constant, applied to terms only) or used once (where its use can take
    it: a proof applied to proofs is not then applied to terms, and a redex or rewrite is not at a
    head), else it stays a redex; '$nex' arguments stay, as the IR states the type of '$nex' only
    in the λ of its redex;
  - η: λ h, F ... h → F ..., for a hypothesis h, where F is a hypothesis or a step;
  - sym (sym E) → E, and sym E → refl for a trivial equation S = S;
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
  forget(ir_step(_, _, _)),
  each(member(Step, Steps), record(Step)).

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
citation(Host, Conclusion, proof(M), Name, Use) :- !,
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
  ir_step(Name, Conclusion, proof(M)),
  clausal(Name, Conclusion),
  get_assoc(Name, Uses, N),
  N \== bad, !,
  inlined_size(Inlined0, M, Size),
  clause_type(Conclusion, T),
  term_size(T, TypeSize),
  ( (N - 1) * Size < TypeSize -> put_assoc(Name, Inlined0, Size, Inlined) ; Inlined = Inlined0 ).
plan(_, _, Inlined, Inlined).

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
optimised(Inlined, Name, Conclusion, proof(M0), proof(M)) :- !,
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

use(env(_, _, U), X, Use) :- ( get_assoc(X, U, Use) -> true ; Use = u(0, false, false, false) ).

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
  ir_step(F, _, proof(M0)),
  hypothesis_uses(M0, Uses),
  empty_assoc(Empty),
  reduced(env(Inlined, Empty, Uses), M0, Ts, Cs, M).
applied(Env, F, Ts, Cs, M) :- F = lam(_, _, _), !, reduced(Env, F, Ts, Cs, M).
applied(_, F, Ts, Cs, M) :-
  atom(F),
  maplist(forced, Cs, Ms),
  built(F, Ts, Ms, M).

% a hypothesis alone is bare, but a step or a built-in is applied
application(Y, [], [], Y) :- var(Y), !.
application(Y, Ts, Ms, app(Y, Ts, Ms)).

% normal terms may be hypotheses, which are variables, so they are matched with care; the type of a
% symmetric equation may be inferred, so it is replaced only by a term whose type can be (inferable/1)
built('$sym', [], [E0], E) :- nonvar(E0), E0 = app('$sym', [], [E]), inferable(E), !.
built(F, Ts, Ms, app(F, Ts, Ms)).

inferable(M) :- ( var(M) -> true ; M = app(_, _, _) ).

% the term M0 of a substituted hypothesis, at the head of an application
applied_term(Env, M0, [], [], M) :- !, normal(Env, M0, M).
applied_term(Env, app(G, Ts0, Ms0), Ts, Cs, M) :- !,
  maplist(substituted(Env), Ts0, Ts1),
  closures(Env, Ms0, Cs0),
  (   Ms0 == []
  ->  append(Ts1, Ts, Ts2), applied(Env, G, Ts2, Cs, M)
  ;   Ts == [],
      append(Cs0, Cs, Cs1), applied(Env, G, Ts1, Cs1, M)
  ).
applied_term(Env, lam(X, A, M0), Ts, Cs, M) :- !, reduced(Env, lam(X, A, M0), Ts, Cs, M).
applied_term(Env, F, Ts, Cs, M) :- applied(Env, F, Ts, Cs, M).

% β-reduction: the binders of the λs take the arguments, terms first
reduced(Env, lam(X, _, M0), [T|Ts], Cs, M) :- !,
  X = '$VAR'(_),
  bind(Env, X, T, Env1),
  reduced(Env1, M0, Ts, Cs, M).
reduced(Env, lam(X, A, M0), [], [C|Cs], M) :- !,
  use(Env, X, Use),
  C = c(V0, Env0),
  (   ( Use = u(0, _, _, _) ; A == '$inferred' ; substitutable(Env0, V0, Use) )
  ->  bind(Env, X, C, Env1), reduced(Env1, M0, [], Cs, M)
  ;   substituted(Env, A, A1),
      forced(C, V),
      bind(Env, X, v(Y), Env1),
      reduced(Env1, M0, [], Cs, N),
      M = app(lam(Y, A1, N), [], [V])
  ).
reduced(Env, M0, Ts, Cs, M) :- applied_term(Env, M0, Ts, Cs, M).

% a value may replace a hypothesis used as Use (see hypothesis_uses): where its use can take it
% a hypothesis whose type is inferred is not replaced, as its binder's type may unfold the value's
substitutable(_, app('$nex', _, _), _) :- !, fail.
substitutable(_, _, u(_, _, _, true)) :- !, fail.
substitutable(Env, V, _) :- cheap(Env, V), !.
substitutable(_, V, u(1, Head, Terms, _)) :-
  (   V = app(_, _, Ms) -> ( Ms == [] -> true ; Terms == false )
  ;   V = lam(_, _, _) -> true
  ;   Head == false
  ).

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

% the uses of each hypothesis of a term, as u(Count, Head, Terms, Inferred): Head if it is applied,
% Terms if to terms, and Inferred if where the checker infers a type (an equation to rewrite by, or the
% formula of an expansion rule), from the hypothesis' type as its binder states it
hypothesis_uses(M, Uses) :-
  phrase(uses(false, M), Occurrences),
  msort(Occurrences, Sorted),
  empty_assoc(Empty),
  foldl(add_use, Sorted, Empty, Uses).

uses(_, lam(_, _, M)) --> !, uses(false, M).
uses(_, rewrite(_, _, E, M)) --> !, uses(true, E), uses(false, M).
uses(Inferred, app(F, Ts, Ms)) --> !,
  use(F, Ts, Ms, Inferred),
  ( { atom(F), inferred_premise(F), Ms = [M|Ms1] } -> uses(true, M), foldl(uses(false), Ms1) ; foldl(uses(false), Ms) ),
  ( { compound(F), F \= h(_) } -> uses(false, F) ; [] ).
uses(Inferred, F) --> use(F, [], [], Inferred).

use(F, Ts, Ms, Inferred) --> { F = h(_) }, !,
  { ( Ts == [], Ms == [] -> Head = false ; Head = true ), ( Ts == [] -> Terms = false ; Terms = true ) },
  [F-u(Head, Terms, Inferred)].
use(_, _, _, _) --> [].

add_use(X-u(Head, Terms, Inferred), Uses0, Uses) :-
  ( get_assoc(X, Uses0, u(N0, H0, T0, I0)) -> true ; N0 = 0, H0 = false, T0 = false, I0 = false ),
  N is N0 + 1,
  either(H0, Head, H),
  either(T0, Terms, T),
  either(I0, Inferred, I),
  put_assoc(X, Uses0, u(N, H, T, I), Uses).

either(false, false, false) :- !.
either(_, _, true).

% the eigenvariables bound in the term are numbered from N0, in order; a hypothesis is still a variable
number_eigenvariables(V, N, N) :- var(V), !.
number_eigenvariables(lam(X, _, M), N0, N) :- !, number_binder(X, N0, N1), number_eigenvariables(M, N1, N).
number_eigenvariables(rewrite(X:_, _, E, M), N0, N) :- !,
  number_binder(X, N0, N1), number_eigenvariables(E, N1, N2), number_eigenvariables(M, N2, N).
number_eigenvariables(app(F, _, Ms), N0, N) :- !, foldl(number_eigenvariables, Ms, N0, N1), number_eigenvariables(F, N1, N).
number_eigenvariables(_, N, N).

number_binder(X, N0, N) :- nonvar(X), X = '$VAR'(I), var(I), !, I = N0, N is N0 + 1.
number_binder(_, N, N).
