/*
Type checker back end: each proof term of the IR (see ir.pl) is checked against the type of its
conclusion, in order, citing only steps already checked. Output is nothing; a step that fails
to check is reported, and is a bug in the search.

First-order terms are checked against the signature (signature.pl): instances are well sorted, and
so are the sorts of eigenvariables and the motives of rewrites. The types of steps are taken to be
well sorted, as the prover gives them.

Terms and their types are ground. The only Prolog variables bound in checking are the quantifier
binders of fresh instances of steps, split definitions and built-ins, which are bound to ground
terms (instantiation) or to eigenvariables (an unfolded split definition, under λs).
*/
:- module(checker, [emit_checker/0]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(signature).

emit_checker :-
  findall(Name, ir_step(Name, _, _), Names),
  empty_assoc(Empty),
  foldl(checked, Names, Empty, _).

% Steps is an assoc of the steps checked so far, so a proof cannot cite itself or a later step
checked(Name, Steps, Steps1) :-
  ir_step(Name, Conclusion, Justification),
  (   justified(Justification, Conclusion, Steps)
  ->  put_assoc(Name, Steps, true, Steps1)
  ;   warn(['error: ', Name, ' does not check']),
      fail
  ).

justified(proof(M), Conclusion, Steps) :- !,
  clause_type(Conclusion, T),
  ground(T),
  ground(M),
  empty_assoc(Gamma),
  check(Steps, Gamma, M, T).
% G, refuting the hypothesis ~G
justified(conjecture(_, Negated, Refutation), formula(G), Steps) :- !,
  get_assoc(Negated, Steps, true),
  ir_step(Negated, formula(N), negated_conjecture(_)),
  N == ~G,
  get_assoc(Refutation, Steps, true),
  ir_step(Refutation, clause([], []), _).
justified(_, _, _).

% M : T, where M and T are ground, but for the binders of an unfolded split definition, which the
% λs name; heads are closed instances, so their types are ground once instantiated
% Gamma is an assoc mapping hypotheses to their types, and eigenvariables to their sorts
check(Steps, Gamma, lam(X, A, M), T0) :- !,
  unfold(T0, T),
  (   T = '!'([Y:S|Ys], B)
  ->  eigenvariable(X),
      \+ occurs(X, Gamma),
      X = Y,
      A = S,
      valid_sort(Gamma, S),
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
% E : S = U and M : A[X:=S] give A[X:=U], where X : Sort is bound in the motive A only
check(Steps, Gamma, rewrite(X:Sort, A, E, M), T) :- !,
  eigenvariable(X),
  \+ get_assoc(X, Gamma, _),
  type(Steps, Gamma, E, '$='(Sort, S, U)),
  put_assoc(X, Gamma, Sort, Gamma1),
  well_sorted(Gamma1, A),
  substitute(X, S, A, AS),
  check(Steps, Gamma, M, AS),
  substitute(X, U, A, AU),
  AU == T.
check(Steps, Gamma, M, T) :-
  type(Steps, Gamma, M, T1),
  T1 == T.

% the type of an application is determined by its head, so is ground
type(Steps, Gamma, app(F, Ts, Ms), T) :- !,
  head(Steps, Gamma, F, T0),
  instantiate(Gamma, Ts, T0, T1),
  ground(T1),
  arguments(Ms, Steps, Gamma, T1, T).
type(_, Gamma, X, T) :- hypothesis(X), get_assoc(X, Gamma, T).

% the type of a head: steps, split definitions and built-ins are fresh instances
head(_, Gamma, X, T) :- hypothesis(X), !, get_assoc(X, Gamma, T).
head(_, _, Name, T) :- atom(Name), builtin_type(Name, T), !.
head(Steps, _, Name, T) :-
  atom(Name),
  get_assoc(Name, Steps, true),
  step(Name, Clause, _),
  Clause = clause(_, _),
  clause_type(Clause, T).

% instantiation is unification, so T0 must be a fresh instance: a hypothesis of quantified type
% (not yet possible) would need substitution instead; each term is of the sort of its binder,
% which depends on the terms before it
instantiate(_, [], T, T) :- !.
instantiate(Gamma, Ts, T0, T) :- unfold(T0, '!'(Bs, T)), instances(Bs, Gamma, Ts).

instances([], _, []).
instances([X:S|Bs], Gamma, [T|Ts]) :- X = T, sorted(Gamma, T, S), instances(Bs, Gamma, Ts).

% first-order term T is of sort S, which is ground; every variable is an eigenvariable of Gamma
sorted(Gamma, '$VAR'(N), S) :- !, get_assoc('$VAR'(N), Gamma, S0), S0 == S.
sorted(Gamma, T, S) :-
  ground(S),
  instance(T, Types, Us, Ss, S0),
  maplist(sorted_type(Gamma), Types),
  S0 == S,
  maplist(sorted(Gamma), Us, Ss).

sorted_type(Gamma, T) :- sorted(Gamma, T, '$tType').

% a sort is '$tType', or a term of sort '$tType'
valid_sort(_, S) :- S == '$tType', !.
valid_sort(Gamma, S) :- sorted(Gamma, S, '$tType').

% formula F is well sorted, with its atoms of sort '$o'
well_sorted(Gamma, F) :- connective(F, Gs), !, maplist(well_sorted(Gamma), Gs).
well_sorted(Gamma, A) :- sorted(Gamma, A, '$o').

arguments([], _, _, T, T).
arguments([M|Ms], Steps, Gamma, T0, T) :-
  unfold(T0, (A => B)),
  check(Steps, Gamma, M, A),
  arguments(Ms, Steps, Gamma, B, T).

% weak head normal form: negation is implication, and split symbols are their definitions
% types are compared syntactically (T1 == T above), not up to unfolding: enough for clauses
unfold(~A, (A => '$false')) :- !.
unfold(S, T) :- atom(S), split(S, Clause), !, closed(Clause), clause_type(Clause, T).
unfold(T, T).

closed(clause(Bs, Ls)) :- \+ \+ ( binder_variables(Bs, Xs), number_vars(Xs, 0, _), ground(Ls) ).

hypothesis(h(N)) :- integer(N).
eigenvariable('$VAR'(N)) :- integer(N).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.
