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

Formulas are types too, compared up to the names of their bound variables: these are named
canonically (see logic.pl), in the types of steps and in the annotations of terms, and a
quantified hypothesis is instantiated by substitution. The expansion rules (ir.pl) are
typed by ir:rule_type/3.
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
  step_type(Conclusion, T0),
  ground(T0),
  ground(M),
  conclusion_type(Conclusion, T0, T),
  empty_assoc(Gamma),
  check(Steps, Gamma, M, T).
% G, refuting the hypothesis ~G
justified(conjecture(_, Negated, Refutation), formula(G), Steps) :- !,
  get_assoc(Negated, Steps, true),
  ir_step(Negated, formula(N), negated_conjecture(_)),
  N == ~G,
  get_assoc(Refutation, Steps, true),
  ir_step(Refutation, clause([], []), _).
% the choice axiom of a Skolem symbol, defined once, by a well-sorted δ formula of its arguments only
justified(skolem_def(Sk, Bs, F), formula(A), Steps) :- !,
  introduced(Sk, _),
  \+ ( ir_step(Name, _, skolem_def(Sk, _, _)), get_assoc(Name, Steps, true) ),
  argument_binders(Sk, Bs, Sort),
  empty_assoc(Empty),
  foldl(argument, Bs, Empty, Gamma),
  canonical(F, F1),
  F1 == F,
  well_sorted(Gamma, F),
  ( Rule = '$ex' ; Rule = '$nall' ),
  rule_type(Rule, F, ('!'([_:S], _) => _)), !,
  S == Sort,
  choice_axiom(Sk, Bs, F, A0),
  canonical(A0, A1),
  A1 == A.
% a function symbol, defined once, by a well-sorted term of its arguments only, and its step is the
% unit clause of its definition, either way round
justified(definition(Symbol, Bs, Body), clause(Cs, [Eq]), Steps) :- !,
  defined_once(Symbol, Bs, Body, Steps, Sort, Gamma, Term),
  msort(Bs, Sorted), msort(Cs, Sorted),
  sorted(Gamma, Body, Sort),
  ( Eq == '$='(Sort, Term, Body) ; Eq == '$='(Sort, Body, Term) ), !.
% ...and a predicate, by a well-sorted formula, and its step is ![Bs] : (Symbol(Xs) <=> Body)
justified(definition(Symbol, Bs, Body), formula(F), Steps) :- !,
  defined_once(Symbol, Bs, Body, Steps, '$o', Gamma, Term),
  canonical(Body, Body1),
  Body1 == Body,
  well_sorted(Gamma, Body),
  ( Bs == [] -> F0 = (Term <=> Body) ; F0 = '!'(Bs, (Term <=> Body)) ),
  canonical(F0, F1),
  F1 == F.
justified(_, _, _).

% Symbol is introduced by definition, and not yet defined, and the symbols of Body are not defined
% later, so definitions unfold; Term is Symbol(Xs), for its binders Bs, in Gamma
defined_once(Symbol, Bs, Body, Steps, Sort, Gamma, Term) :-
  introduced(Symbol, definition),
  \+ ( ir_step(Name, _, definition(Symbol, _, _)), get_assoc(Name, Steps, true) ),
  argument_binders(Symbol, Bs, Sort),
  \+ ( subterm(Body, T), functor(T, F, _), ir_step(Name, _, definition(F, _, _)), \+ get_assoc(Name, Steps, true) ),
  empty_assoc(Empty),
  foldl(argument, Bs, Empty, Gamma),
  binder_variables(Bs, Xs),
  Term =.. [Symbol|Xs].

% the binders Bs of Sk(Xs) are distinct eigenvariables, of the sorts of its arguments, and Sk is of Sort
argument_binders(Sk, Bs, Sort) :-
  binder_variables(Bs, Xs),
  maplist(eigenvariable, Xs),
  sort(Xs, Ys),
  same_length(Xs, Ys),
  symbol(Sk, Ps, Args, Sort),
  append(Ps, _, Xs),
  findall('$tType', member(_, Ps), Ts),
  append(Ts, Args, Sorts),
  binder_sorts(Bs, Sorts).

binder_sorts([], []).
binder_sorts([_:S|Bs], [S0|Ss]) :- S == S0, binder_sorts(Bs, Ss).

argument(X:S, Gamma, Gamma1) :- valid_sort(Gamma, S), put_assoc(X, Gamma, S, Gamma1).

% the binders of a clause are its eigenvariables, by name, and its literals have no others
conclusion_type(clause(_, _), T, T).
conclusion_type(formula(_), T0, T) :- canonical(T0, T).

% M : T, where M and T are ground; heads are closed instances, so their types are ground once
% instantiated. Types are canonical (see logic.pl), so they are compared syntactically, and
% annotations are made so
% Gamma is an assoc mapping hypotheses to their types, and eigenvariables to their sorts
check(Steps, Gamma, lam(X, A, M), T0) :- !,
  unfold(T0, T),
  (   T = '!'([Y:S|Bs], B)
  ->  eigenvariable(X),
      \+ get_assoc(X, Gamma, _),
      A == S,
      valid_sort(Gamma, S),
      instantiated(Y, X, Bs, B, T1),
      put_assoc(X, Gamma, S, Gamma1),
      check(Steps, Gamma1, M, T1)
  ;   T = (A1 => B),
      hypothesis(X),
      ( A == '$inferred' -> true ; A == A1 -> true ; canonical(A, A2), A2 == A1 ),
      put_assoc(X, Gamma, A1, Gamma1),
      check(Steps, Gamma1, M, B)
  ).
check(Steps, Gamma, let(X, F0, M, M1), T) :- !,
  hypothesis(X),
  canonical(F0, F),
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
  convertible(T1, T).

% types are the same, or the same once defined predicates are unfolded (see ir.pl)
convertible(T1, T) :- T1 == T, !.
convertible(T1, T) :- expanded(T1, U), expanded(T, U1), U == U1.

% the type of an application is determined by its head, or for an expansion rule (see ir.pl) by
% the type of its first argument
type(Steps, Gamma, app(Rule, [], [M|Ms]), T) :-
  atom(Rule),
  rule_type(Rule, _, _), !,
  type(Steps, Gamma, M, T0),
  rule_type(Rule, T0, T1),
  arguments(Ms, Steps, Gamma, T1, T).
type(Steps, Gamma, app(F, Ts, Ms), T) :- !,
  head(Steps, Gamma, F, T0),
  instantiate(Gamma, Ts, T0, T1),
  % a clause is ground by now, and has no bound variables
  ( F \== '$dne', ground(T1) -> T2 = T1 ; canonical(T1, T2), ground(T2) ),
  arguments(Ms, Steps, Gamma, T2, T).
type(_, Gamma, X, T) :- hypothesis(X), get_assoc(X, Gamma, T).

% the type of a head: steps and built-ins are fresh instances
head(_, Gamma, X, T) :- hypothesis(X), !, get_assoc(X, Gamma, T).
head(_, _, Name, T) :- atom(Name), builtin_type(Name, T), !.
head(Steps, _, Name, T) :-
  atom(Name),
  get_assoc(Name, Steps, true),
  step(Name, Conclusion, _),
  step_type(Conclusion, T).

% each term is of the sort of its binder, which depends on the terms before it
instantiate(_, [], T, T) :- !.
instantiate(Gamma, [U|Us], T0, T) :-
  unfold(T0, '!'([X:S|Bs], F)),
  sorted(Gamma, U, S),
  instantiated(X, U, Bs, F, T1),
  instantiate(Gamma, Us, T1, T).

% '!'([X:_|Bs], F) with U for X: X is a variable in a fresh instance, where instantiation is
% unification, or U itself, an eigenvariable named after the binder of its clause, or else it is
% canonical, and substituted. U is ground and has no bound variables (it is an eigenvariable, or
% well sorted), so none is captured
instantiated(X, U, Bs, F, T) :- var(X), !, X = U, quantified(Bs, F, T).
instantiated(X, U, Bs, F, T) :- X == U, !, quantified(Bs, F, T).
instantiated('$BOUND'(H), U, Bs0, F0, T) :-
  substitute('$BOUND'(H), U, Bs0-F0, Bs-F),
  quantified(Bs, F, T).

quantified([], F, F) :- !.
quantified(Bs, F, '!'(Bs, F)).

% first-order term T is of sort S, which is ground; every variable is an eigenvariable of Gamma
sorted(Gamma, '$VAR'(N), S) :- !, get_assoc('$VAR'(N), Gamma, S0), S0 == S.
sorted(Gamma, '$BOUND'(H), S) :- !, get_assoc('$BOUND'(H), Gamma, S0), S0 == S.
sorted(Gamma, F0, S) :- S == '$o', connective(F0, _), !, canonical(F0, F), well_sorted(Gamma, F).
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

% canonical formula F is well sorted, with its atoms of sort '$o'
well_sorted(Gamma, F) :-
  F =.. [Q, Bs, G],
  ( Q == '!' ; Q == '?' ), !,
  foldl(binder, Bs, Gamma, Gamma1),
  well_sorted(Gamma1, G).
well_sorted(Gamma, F) :- connective(F, Gs), !, maplist(well_sorted(Gamma), Gs).
well_sorted(Gamma, A) :- sorted(Gamma, A, '$o').

binder('$BOUND'(H):S, Gamma, Gamma1) :-
  valid_sort(Gamma, S),
  put_assoc('$BOUND'(H), Gamma, S, Gamma1).

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
