/*
Reconstruct steps into ir_step/3 facts by searching for proof terms (see ir.pl for the IR).

The search procedures below are given hypotheses Hs, a list of X-T pairs where X : T is a
variable, and build a term of type ⊥, which is then abstracted over the conclusion (checker.pl
type-checks it). Each λ is annotated with its binder's type when it is built. During search,
binders are Prolog variables, and are named h(N) afterwards.
Clauses are stored with Prolog variables (db.pl), so retrieving a premise gives a fresh instance.
The conclusion is made rigid by numbering its variables, and premise instances are found by
unification with it, Prolog's backtracking performing the search.
*/
:- module(reconstruct, [reconstruct/0]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(rup).
:- use_module(close).

% reconstruct everything required for the last refutation
reconstruct :-
  forall(step(_, _, split_def(Symbol, Clause)), assertz(split(Symbol, Clause))),
  findall(Name, step(Name, clause([], []), _), Refutations),
  last(Refutations, Refutation),
  prove(Refutation).

prove(Name) :- ir_step(Name, _, _), !.
prove(Name) :-
  step(Name, Conclusion, How),
  rigid(Conclusion, Fresh),
  justify(How, Conclusion, Fresh, Justification),
  assertz(ir_step(Name, Conclusion, Justification)).

% number the variables of a conclusion, in binder order; Fresh is the next index
rigid(clause(Xs, _), Fresh) :- number_vars(Xs, 0, Fresh).
rigid(formula(F), Fresh) :- term_variables(F, Vs), number_vars(Vs, 0, Fresh).

justify(input(Role, Source), _, _, input(Role, Source)).
justify(split_def(Symbol, Clause), _, _, split_def(Symbol, Clause)).
justify(todo(Record, Parents), _, _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Fresh, Justification) :-
  maplist(prove, Parents),
  search(Tactic, Parents, Conclusion, Fresh, Justification).

% the tactic finds a term of type ⊥ from hypotheses for the literals, abstracted over the conclusion
search(Tactic, Parents, clause(Xs, Ls), Fresh, proof(M)) :-
  hypotheses(Ls, Hs),
  once(call(Tactic, Fresh, Hs, Parents, Body)), !,
  binders(Xs, Hs, Binders),
  lambdas(Binders, Body, M),
  close_term(M).
% ...or it fails, and the step is left to do
search(Tactic, Parents, Conclusion, _, todo(Tactic, Parents)) :-
  format(user_error, "warning: ~w failed to reconstruct ~w~n", [Tactic, Conclusion]).

% a hypothesis V : ~L for each literal L
hypotheses([], []).
hypotheses([L|Ls], [_-(~L)|Hs]) :- hypotheses(Ls, Hs).

% binders X-T for the eigenvariables Xs, then the hypotheses Hs
binders(Xs, Hs, Binders) :- maplist(individual, Xs, Is), append(Is, Hs, Binders).

individual(X, X-'$i').

lambdas([], M, M).
lambdas([X-T|Xs], M, lam(X, T, N)) :- lambdas(Xs, M, N).

/********************************************************************************
 * literal matching
 ********************************************************************************/

% a hypothesis refutes premise literal L, as M : ~L
matches(Hs, L, M) :-
  member(X-T, Hs),
  refutes(T, X, L, M).

% refutes(T, X, L, M): X : T refutes L as M, modulo symmetry of equality
refutes(~K, X, L, X) :- unify_with_occurs_check(K, L).
refutes(~K, X, L, M) :- flip(K, F), unify_with_occurs_check(F, L), flipped(L, X, M).
refutes(A, X, ~B, lam(K, ~B, app(K, [], [X]))) :- A \= ~_, unify_with_occurs_check(A, B).
refutes(S = T, X, ~B, lam(K, ~B, app(K, [], [app('$sym', [S, T], [X])]))) :- unify_with_occurs_check(T = S, B).

% X refutes L with the equation the other way round
flipped(S = T, X, lam(E, S = T, app(X, [], [app('$sym', [S, T], [E])]))).
flipped(~(S = T), X, lam(K, ~(S = T), app(X, [], [lam(E, T = S, app(K, [], [app('$sym', [T, S], [E])]))]))).

% a fresh instance of a premise clause, with variables Ts
premise(Name, Ts, Ls) :- step(Name, clause(Ts, Ls), _).

/********************************************************************************
 * search procedures: tactic(Fresh, Hypotheses, Parents, M)
 * Fresh is the next available '$VAR' index, for eigenvariables
 ********************************************************************************/

% the conclusion is an instance of the premise, modulo symmetry, factoring and duplicates
variant(_, Hs, [Premise], app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(matches(Hs), Ls, Ms).

% binary resolution: literals of the major premise are either in the conclusion,
% or refuted by (an instance of) the minor premise
% only positive literals are refuted by the minor: one resolved literal is positive, and either premise
% may be the major, so this is complete, and avoids an exponential search on wide negative clauses
resolve(_, Hs, Premises, app(Major, Ts, Ms)) :-
  select(Major, Premises, [Minor]),
  premise(Major, Ts, Ks),
  maplist(resolve_literal(Hs, Minor), Ks, Ms).

resolve_literal(Hs, _, K, M) :- matches(Hs, K, M).
resolve_literal(Hs, Minor, K, lam(X, K, app(Minor, Ts, Ms))) :-
  K \= ~_,
  premise(Minor, Ts, Ls),
  maplist(matches([X-K|Hs]), Ls, Ms).

% reverse unit propagation (see rup.pl) over ground premises: premises with variables are ignored,
% which is enough for Vampire's rat, over AVATAR's propositional clauses
rup(_, Hs, Premises, M) :-
  findall(P-Ls, (member(P, Premises), premise(P, [], Ls)), Clauses),
  rup(Hs, Clauses, M).

% AVATAR component clause: C | ~split, where split is defined as C
avatar_component(_, Hs, [_], app(H, [], [lam(D, Split, app(D, Ts, Ms))])) :-
  select(H-(~(~Split)), Hs, Others),
  split(Split, clause(Ts, Ls)),
  maplist(matches(Others), Ls, Ms).
% ...or ~L | split, where split is defined as L: the definition is proved from two hypotheses,
% Y : ~T and X : T
avatar_component(Fresh, Hs, [_], app(H, [], [Intro])) :-
  select(H-(~Split), Hs, Others),
  intro(Split, Fresh, _, Others, All, app(Y, [], [X]), Intro),
  member(Y-(~T), All),
  member(X-U, All),
  U == T.

% Intro proves the definition of Split by M, with eigenvariables from Fresh0 and hypotheses for its literals
intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro) :-
  split(Split, clause(Xs, Ls)),
  number_vars(Xs, Fresh0, Fresh),
  hypotheses(Ls, Gs),
  append(Gs, Hs, Hs1),
  binders(Xs, Gs, Binders),
  lambdas(Binders, M, Intro).

% AVATAR split clause: split_1 | ... | split_n from the premise C_1 | ... | C_n
avatar_split(Fresh, Hs, [Premise|_], M) :-
  splits(Hs, Fresh, Hs, [], Premise, M).

splits([], _, Hs, Ds, Premise, app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(split_literal(Hs, Ds), Ls, Ms).
splits([H-(~(~Split))|Rest], Fresh, Hs, Ds, Premise, M) :-
  split(Split, Clause),
  splits(Rest, Fresh, Hs, [H-Split-Clause|Ds], Premise, M).
splits([H-(~Split)|Rest], Fresh0, Hs, Ds, Premise, app(H, [], [Intro])) :-
  intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro),
  splits(Rest, Fresh, Hs1, Ds, Premise, M).

% a premise literal is refuted by a hypothesis, or by a ground unit definition, from H : ~~split
split_literal(Hs, _, L, M) :- matches(Hs, L, M).
split_literal(_, Ds, L, lam(X, L, app(H, [], [lam(D, Split, app(D, [], [M]))]))) :-
  member(H-Split-clause([], [K]), Ds),
  matches([X-L], K, M).
