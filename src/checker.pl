/*
Type checker back end: each proof term of the IR (ir.pl) is checked against the type of its
conclusion, citing only steps checked before it; a failure is a bug in reconstruction. Terms are
checked against the signature, and the types of steps are taken to be well sorted.

Terms and types are ground, but for the Prolog variables of fresh instances of steps and built-ins,
which instantiation and type inference bind. A β-redex is checked by binding: an eigenvariable is
substituted by its term, and a hypothesis takes the type of its λ, against which its proof is
checked. Every binder is fresh.
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
  unchecked(Name, Justification),
  (   justified(Justification, Conclusion, Steps)
  ->  put_assoc(Name, Steps, true, Steps1)
  ;   warn(['error: ', Name, ' does not check']),
      fail
  ).

% an unreconstructed step is accepted, as a partial proof, but not silently
unchecked(Name, todo(Record, _)) :- !,
  todo_rule(Record, Rule),
  warn(['warning: ', Name, ' (', Rule, ') is not checked']).
unchecked(_, _).

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
% the choice axiom of a Skolem symbol, defined once, by a well-sorted ? formula of its arguments only
justified(skolem_def(Sk, Bs, F), formula(A), Steps) :- !,
  introduced(Sk, _),
  \+ ( ir_step(Name, _, skolem_def(Sk, _, _)), get_assoc(Name, Steps, true) ),
  argument_binders(Sk, Bs, Sort),
  empty_assoc(Empty),
  foldl(argument, Bs, Empty, Gamma),
  canonical(F, F1),
  F1 == F,
  well_sorted(Gamma, F),
  F = '?'(_:S, _),
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
  quantify('!', Bs, (Term <=> Body), F0),
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
  maplist(variable, Xs),
  sort(Xs, Ys),
  same_length(Xs, Ys),
  symbol_binders(Sk, Xs, Bs1, Sort),
  Bs1 == Bs.

argument(X:S, Gamma, Gamma1) :- valid_sort(Gamma, S), put_assoc(X, Gamma, S, Gamma1).

% the binders of a clause are its eigenvariables, by name, and its literals have no others
conclusion_type(clause(_, _), T, T).
conclusion_type(formula(_), T0, T) :- canonical_type(T0, T).

% a proof type with its formula canonical
canonical_type('$proof'(F0), '$proof'(F)) :- canonical(F0, F).

% M : T, where T may have parameters of built-ins still to infer; Gamma maps hypotheses to their proof
% types, and eigenvariables to their sorts
check(Steps, Gamma, '$lam'(X, A, M), '$proof'(F0)) :- !,
  nonvar(F0),
  unfold(F0, F),
  fresh(Gamma, X),
  abstraction(Gamma, F, X, A, T, B),
  put_assoc(X, Gamma, T, Gamma1),
  check(Steps, Gamma1, M, '$proof'(B)).
check(Steps, Gamma, M0, T) :-
  redex(M0), !,
  reduced(Steps, Gamma, M0, Gamma1, M),
  check(Steps, Gamma1, M, T).
check(Steps, Gamma, M, T) :- M = _ @ _, !, spine(M, F, As), application(Steps, Gamma, F, As, T).
% a step or a built-in alone, whose parameters T may bind
check(Steps, Gamma, F, T) :- atom(F), !, application(Steps, Gamma, F, [], T).
check(Steps, Gamma, M, T) :-
  type(Steps, Gamma, M, T1),
  matches(T1, T).

% '$proof'(F) is Π X : T. '$proof'(B), for the λ binder X annotated A: a sort, which must be that of
% the quantifier, or a proof type, which may unfold the expected one (as a redex would) and binds its
% parameters, or '$inferred'
abstraction(Gamma, '!'(Y:S, B0), X, A, S, B) :-
  A == S,
  valid_sort(Gamma, S),
  instantiated(Y, X, B0, B).
abstraction(_, (A1 => B), _, A, '$proof'(A3), B) :-
  (   A == '$inferred'
  ->  A3 = A1
  ;   A = '$proof'(A2),
      ( A2 == A1 -> A3 = A1 ; canonical(A2, A3), formula_matches(A3, A1) )
  ),
  ground(A3).

% proof type T1 is T, a variable if it is to be inferred, by their formulas
matches('$proof'(F1), '$proof'(F)) :- formula_matches(F1, F).

% F1 is F: if both are ground, up to unfolding, and otherwise by unification, which binds the
% parameters of either, as it is or with a defined atom at the top of F1 unfolded (as the binder of a
% value substituted for a hypothesis may have stated it, see optimise.pl), or else F1 is an instance
% of F unfolded
formula_matches(F1, F) :- ground(F1), ground(F), !, convertible(F1, F).
formula_matches(F1, F) :- F1 = F, !.
formula_matches(F1, F) :- nonvar(F1), unfold(F1, U), U = F, !.
formula_matches(F1, F) :- ground(F), expanded(F, U), U = F1, ground(F1).

% types are the same, or the same once defined predicates and function terms are unfolded (see ir.pl)
convertible(T1, T) :- T1 == T, !.
convertible(T1, T) :- expanded(T1, U), expanded(T, U1), U == U1, !.
% ~F is F => '$false', and a split symbol its definition, at any arrow (as after η-reduction, optimise.pl)
convertible(T1, T) :-
  unfold(T1, (A1 => B1)), unfold(T, (A => B)), !,
  convertible(A, A1),
  convertible(B1, B).

% the type T of M, inferred: ground but for the parameters of a built-in that nothing has bound
type(Steps, Gamma, M0, T) :-
  redex(M0), !,
  reduced(Steps, Gamma, M0, Gamma1, M),
  type(Steps, Gamma1, M, T).
type(Steps, Gamma, M, T) :- M = _ @ _, !, spine(M, F, As), application(Steps, Gamma, F, As, T).
% a head alone: a hypothesis, a step or a built-in
type(Steps, Gamma, F, T) :- application(Steps, Gamma, F, [], T).

% F applied to As is of type T: each term instantiates a '!' of the head's type, and each proof is
% checked against its premise. A built-in's parameters are bound by unifying its result with T (a
% variable if T is inferred), and then each premise with its proof's type, in order (but for a
% built-in with a motive, motive_head/1)
application(Steps, Gamma, F, As, T) :-
  head(Steps, Gamma, F, T0),
  arguments(Gamma, As, T0, Ps0, R0),
  % a clause is ground by now, and has no bound variables; a quantified hypothesis instantiated by
  % fewer terms than it has binders is canonical again
  (   ( ground(Ps0-R0) ; atom(F), head_type(F, _) )
  ->  Ps = Ps0, R = R0
  ;   maplist(canonical_premise, Ps0, Ps), canonical_type(R0, R), ground(Ps-R)
  ),
  (   motive_head(F)
  ->  maplist(checked_premise(Steps, Gamma), Ps),
      matches(R, T)
  ;   matches(R, T),
      maplist(checked_premise(Steps, Gamma), Ps)
  ),
  ground(T).

% a built-in with a motive, '$rewrite': its result, A[X:=U], is a substitution, which unification
% cannot match up to unfolding, so its premises infer U first, and the result is then ground
motive_head(F) :- atom(F), head_type(F, '$proof'('!'(_:S, _))), arrow_sort(S).

% the proofs of the arguments As of a head of type T0, each M-A for its premise A, and the type R of
% the application; each term is of the sort of its binder, which depends on the terms before it
arguments(_, [], R, [], R).
arguments(Gamma, [U|As], '$proof'(F0), Ps0, R) :-
  nonvar(F0),
  unfold(F0, F),
  argument(Gamma, F, U, Ps0, Ps, T),
  arguments(Gamma, As, T, Ps, R).

argument(Gamma, '!'(X:S, F), U, Ps, Ps, '$proof'(F1)) :- !,
  sorted(Gamma, U, S),
  instantiated(X, U, F, F0),
  ( arrow_sort(S) -> applied_motives(F0, F1) ; F1 = F0 ).
argument(_, (A => F), M, [M-'$proof'(A)|Ps], Ps, '$proof'(F)).

canonical_premise(M-A0, M-A) :- canonical_type(A0, A).

checked_premise(Steps, Gamma, M-A) :- check(Steps, Gamma, M, A).

% β-reduction by binding: the λs of a redex M0 take its arguments in order, and M is the rest of its
% body, applied to any arguments left over, in Gamma with the hypotheses bound
redex(M) :- M = _ @ _, spine(M, L, _), nonvar(L), L = '$lam'(_, _, _).

reduced(Steps, Gamma0, M0, Gamma, M) :-
  spine(M0, L, [W|As]), nonvar(L), L = '$lam'(X, A, B0), !,
  fresh(Gamma0, X),
  bound(Steps, Gamma0, X, A, W, B0, Gamma1, B),
  curried(B, As, M1),
  reduced(Steps, Gamma1, M1, Gamma, M).
reduced(_, Gamma, M, Gamma, M).

% an eigenvariable X : S takes the term W, which is substituted into the body; a hypothesis X : A
% takes the proof W, checked against A, which X then has
bound(Steps, Gamma0, X, A0, W, B0, Gamma, B) :-
  nonvar(A0), A0 = '$proof'(_), !,
  canonical_type(A0, A),
  check(Steps, Gamma0, W, A),
  put_assoc(X, Gamma0, A, Gamma),
  B = B0.
bound(_, Gamma, X, S, U, B0, Gamma, B) :-
  sorted(Gamma, U, S),
  substitute(X, U, B0, B).

% the type of a head: steps and built-ins are fresh instances, and a term is typed as any other
head(_, Gamma, X, T) :- variable(X), !, hypothesis(Gamma, X, T).
head(_, _, Name, T) :- atom(Name), head_type(Name, T), !.
head(Steps, _, Name, T) :-
  atom(Name),
  get_assoc(Name, Steps, true),
  step(Name, Conclusion, _),
  step_type(Conclusion, T).

% '!'(X:_, F) instantiated by U: by unification in a fresh instance, as it is if X is U (an eigenvariable
% of a clause), and otherwise by substitution for the canonical X, which captures nothing as U is ground
instantiated(X, U, F, F) :- var(X), !, X = U.
instantiated(X, U, F, F) :- X == U, !.
instantiated('$BOUND'(H), U, F0, F) :- substitute('$BOUND'(H), U, F0, F).

% first-order term T is of sort S, which is ground; every variable is an eigenvariable of Gamma. A
% motive, the one term that is not first-order, is of an arrow sort S > '$o', which its binder X : S
% gives, if a parameter of '$rewrite' left it open, and its body is a well-sorted formula with X : S
sorted(Gamma, '$abs'(X:S, A), Arrow) :- !,
  Arrow = '$>'(S0, '$o'),
  S0 = S,
  fresh(Gamma, X),
  valid_sort(Gamma, S),
  put_assoc(X, Gamma, S, Gamma1),
  canonical(A, A1),
  A1 == A,
  well_sorted(Gamma1, A).
sorted(Gamma, X, S) :- ( X = '$VAR'(_) ; X = '$BOUND'(_) ), !, get_assoc(X, Gamma, S0), S0 == S.
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
  quantifier(F, _, B, G), !,
  binder(B, Gamma, Gamma1),
  well_sorted(Gamma1, G).
well_sorted(Gamma, F) :- connective(F, Gs), !, maplist(well_sorted(Gamma), Gs).
well_sorted(Gamma, A) :- sorted(Gamma, A, '$o').

binder('$BOUND'(H):S, Gamma, Gamma1) :-
  valid_sort(Gamma, S),
  put_assoc('$BOUND'(H), Gamma, S, Gamma1).

% weak head normal form of a formula: negation is implication, and a defined atom (a split, say) is its
% definition, as a redex or annotation would otherwise state it (optimise.pl removes some)
unfold(~A, (A => '$false')) :- !.
unfold(A, T) :- defined_atom(A, F0), !, opened(F0, F1), canonical(F1, F), unfold(F, T).
unfold(T, T).

% a variable of the term: a hypothesis or an eigenvariable, as Gamma says (by a proof type or a sort)
variable('$VAR'(N)) :- integer(N).

% a binder is a variable not already in scope, so that none is shadowed
fresh(Gamma, X) :- variable(X), \+ get_assoc(X, Gamma, _).

hypothesis(Gamma, X, T) :- get_assoc(X, Gamma, T), T = '$proof'(_).
