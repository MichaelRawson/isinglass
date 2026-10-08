/*
Type checker back end: each proof term of the IR (see db.pl) is checked against the type of its
conclusion, in order, citing only steps already checked. Output is nothing; a step that fails
to check is reported, and is a bug in the search.

Terms and their types are ground. The only Prolog variables bound in checking are the quantifier
binders of fresh instances of steps, split definitions and built-ins, which are bound to ground
terms (instantiation) or to eigenvariables (an unfolded split definition, under λs).
*/
:- module(checker, [emit/0]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

emit :-
  findall(Name, ir_step(Name, _, _), Names),
  empty_assoc(Empty),
  foldl(checked, Names, Empty, _).

% Steps is an assoc of the steps checked so far, so a proof cannot cite itself or a later step
checked(Name, Steps, Steps1) :-
  ir_step(Name, Conclusion, Justification),
  (   justified(Justification, Conclusion, Steps)
  ->  put_assoc(Name, Steps, true, Steps1)
  ;   format(user_error, "error: ~w does not check~n", [Name]),
      fail
  ).

justified(proof(M), Conclusion, Steps) :- !,
  clause_type(Conclusion, T),
  ground(T),
  ground(M),
  empty_assoc(Gamma),
  check(Steps, Gamma, M, T).
justified(_, _, _).

% M : T, where M and T are ground, but for the binders of an unfolded split definition, which the
% λs name; heads are closed instances, so their types are ground once instantiated
% Gamma is an assoc mapping hypotheses to their types, and eigenvariables to '$i'
check(Steps, Gamma, lam(X, A, M), T0) :- !,
  unfold(T0, T),
  (   T = '!'([Y|Ys], B)
  ->  eigenvariable(X),
      \+ occurs(X, Gamma),
      X = Y,
      A = '$i',
      ( Ys == [] -> T1 = B ; T1 = '!'(Ys, B) ),
      put_assoc(X, Gamma, A, Gamma1),
      check(Steps, Gamma1, M, T1)
  ;   T = (A => B),
      hypothesis(X),
      put_assoc(X, Gamma, A, Gamma1),
      check(Steps, Gamma1, M, B)
  ).
check(Steps, Gamma, let(X, F, M, M1), T) :- !,
  hypothesis(X),
  check(Steps, Gamma, M, F),
  put_assoc(X, Gamma, F, Gamma1),
  check(Steps, Gamma1, M1, T).
check(Steps, Gamma, M, T) :-
  type(Steps, Gamma, M, T1),
  T1 == T.

% the type of an application is determined by its head, so is ground
type(Steps, Gamma, app(F, Ts, Ms), T) :- !,
  head(Steps, Gamma, F, T0),
  terms(Gamma, Ts),
  instantiate(Ts, T0, T1),
  ground(T1),
  arguments(Ms, Steps, Gamma, T1, T).
type(_, Gamma, X, T) :- hypothesis(X), get_assoc(X, Gamma, T).

% the type of a head: steps, split definitions and built-ins are fresh instances
head(_, Gamma, X, T) :- hypothesis(X), !, get_assoc(X, Gamma, T).
head(_, _, Name, T) :- atom(Name), builtin(Name, T), !.
head(Steps, _, Name, T) :-
  atom(Name),
  get_assoc(Name, Steps, true),
  step(Name, Clause, _),
  Clause = clause(_, _),
  clause_type(Clause, T).

builtin('$sym', '!'([X, Y], ((X = Y) => (Y = X)))).

% first-order terms are in scope: every variable is an eigenvariable of Gamma
terms(_, []).
terms(Gamma, [T|Ts]) :- term(Gamma, T), terms(Gamma, Ts).

term(Gamma, '$VAR'(N)) :- !, get_assoc('$VAR'(N), Gamma, '$i').
term(Gamma, T) :- T =.. [_|Ts], terms(Gamma, Ts).

% instantiation is unification, so T0 must be a fresh instance: a hypothesis of quantified type
% (not yet possible) would need substitution instead
instantiate([], T, T) :- !.
instantiate(Ts, T0, T) :- unfold(T0, '!'(Ts, T)).

arguments([], _, _, T, T).
arguments([M|Ms], Steps, Gamma, T0, T) :-
  unfold(T0, (A => B)),
  check(Steps, Gamma, M, A),
  arguments(Ms, Steps, Gamma, B, T).

% weak head normal form: negation is implication, and split symbols are their definitions
% types are compared syntactically (T1 == T above), not up to unfolding: enough for clauses
unfold(~A, (A => '$false')) :- !.
unfold(S, T) :- atom(S), split_def(S, Clause), !, closed(Clause), clause_type(Clause, T).
unfold(T, T).

closed(clause(Xs, Ls)) :- \+ \+ ( number_vars(Xs, 0, _), ground(Ls) ).

hypothesis(h(N)) :- integer(N).
eigenvariable('$VAR'(N)) :- integer(N).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.
