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
rigid(clause(Bs, _), Fresh) :- binder_variables(Bs, Xs), number_vars(Xs, 0, Fresh).
rigid(formula(F), Fresh) :- term_variables(F, Vs), number_vars(Vs, 0, Fresh).

justify(input(Role, Source), _, _, input(Role, Source)).
justify(split_def(Symbol, Clause), _, _, split_def(Symbol, Clause)).
justify(todo(Record, Parents), _, _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Fresh, Justification) :-
  maplist(prove, Parents),
  search(Tactic, Parents, Conclusion, Fresh, Justification).

% the tactic finds a term of type ⊥ from hypotheses for the literals, abstracted over the conclusion
search(Tactic, Parents, clause(Bs, Ls), Fresh, proof(M)) :-
  hypotheses(Ls, Hs),
  once(call(Tactic, Fresh, Hs, Parents, Body)), !,
  binders(Bs, Hs, Binders),
  lambdas(Binders, Body, M),
  close_term(M).
% ...or it fails, and the step is left to do
search(Tactic, Parents, Conclusion, _, todo(Tactic, Parents)) :-
  format(user_error, "warning: ~w failed to reconstruct ~w~n", [Tactic, Conclusion]).

% a hypothesis V : ~L for each literal L
hypotheses([], []).
hypotheses([L|Ls], [_-(~L)|Hs]) :- hypotheses(Ls, Hs).

% binders X-T: eigenvariables X-Sort for the clause's binders Bs, then the hypotheses Hs
binders(Bs, Hs, Binders) :- maplist(eigenvariable, Bs, Is), append(Is, Hs, Binders).

eigenvariable(X:S, X-S).

lambdas([], M, M).
lambdas([X-T|Xs], M, lam(X, T, N)) :- lambdas(Xs, M, N).

/********************************************************************************
 * literal matching
 ********************************************************************************/

% a hypothesis refutes premise literal L, as M : ~L, or L is a trivial inequality S != S
matches(Hs, L, M) :-
  member(X-T, Hs),
  refutes(T, X, L, M).
matches(_, ~(S = T), lam(K, ~(S = S), app(K, [], [app('$refl', [S], [])]))) :-
  unify_with_occurs_check(S, T).

% refutes(T, X, L, M): X : T refutes L as M, modulo symmetry of equality
refutes(~K, X, L, X) :- unify_with_occurs_check(K, L).
refutes(~K, X, L, M) :- flip(K, F), unify_with_occurs_check(F, L), flipped(L, X, M).
refutes(A, X, ~B, lam(K, ~B, app(K, [], [X]))) :- A \= ~_, unify_with_occurs_check(A, B).
refutes(S = T, X, ~B, lam(K, ~B, app(K, [], [app('$sym', [S, T], [X])]))) :- unify_with_occurs_check(T = S, B).

% X refutes L with the equation the other way round
flipped(S = T, X, lam(E, S = T, app(X, [], [app('$sym', [S, T], [E])]))).
flipped(~(S = T), X, lam(K, ~(S = T), app(X, [], [lam(E, T = S, app(K, [], [app('$sym', [T, S], [E])]))]))).

% a fresh instance of a premise clause, with variables Ts
premise(Name, Ts, Ls) :- step(Name, clause(Bs, Ls), _), binder_variables(Bs, Ts).

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

% paramodulation: literals of the Into premise are either in the conclusion, or rewritten by an
% equation of (an instance of) the From premise, the rest of which is in the conclusion
paramodulate(Fresh, Hs, Premises, app(Into, Ts, Ms)) :-
  select(Into, Premises, [From]),
  premise(Into, Ts, Ks),
  maplist(paramodulate_literal(Fresh, Hs, From), Ks, Ms).

paramodulate_literal(_, Hs, _, K, M) :- matches(Hs, K, M).
paramodulate_literal(Fresh, Hs, From, K, lam(Y, K, app(From, Ts, Ms))) :-
  premise(From, Ts, Ls),
  append(Before, [A = B|After], Ls),
  rewrite_literal(Fresh, Hs, K, Y, E, A = B, Body),
  maplist(matches(Hs), Before, Ms0),
  maplist(matches(Hs), After, Ms1),
  append(Ms0, [lam(E, A = B, Body)|Ms1], Ms).

% equality factoring: as paramodulation, but the equation is a hypothesis for a literal A != B
equality_factor(Fresh, Hs, [Premise], app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ks),
  maplist(factor_literal(Fresh, Hs), Ks, Ms).

factor_literal(_, Hs, K, M) :- matches(Hs, K, M).
factor_literal(Fresh, Hs, K, lam(Y, K, app(H, [], [lam(E, A = B, Body)]))) :-
  member(H-(~(~(A = B))), Hs),
  rewrite_literal(Fresh, Hs, K, Y, E, A = B, Body).

% Body : ⊥ from Y : K and E : A = B: K rewritten one way or the other is refuted by a hypothesis
rewrite_literal(Fresh, Hs, K, Y, E, A = B, Body) :-
  orientation(A = B, E, L, R, Equation),
  member(X-(~K1), Hs),
  ( Target = K1 ; flip(K1, Target) ),
  rewritten(K, Target, L, R, '$VAR'(Fresh), Motive),
  refutes(~K1, X, Target, M),
  applied(M, rewrite('$VAR'(Fresh), Motive, Equation, Y), Body).

orientation(A = B, E, A, B, E).
orientation(A = B, E, B, A, app('$sym', [A, B], [E])).

% M : ~T applied to W : T; a λ is β-reduced to a let, so that heads stay variables or constants
applied(M, W, app(M, [], [W])) :- var(M), !.
applied(lam(V, T, B), W, let(V, T, W, B)).

% literal K becomes K1 by rewriting L to R at some occurrences, which are Z in Motive
rewritten(~A, ~A1, L, R, Z, ~Motive) :- !, rewritten_atom(A, A1, L, R, Z, Motive).
rewritten(A, A1, L, R, Z, Motive) :- A1 \= ~_, rewritten_atom(A, A1, L, R, Z, Motive).

rewritten_atom(A, A1, L, R, Z, Motive) :-
  nonvar(A),
  A1 =.. [P|Us1],
  A =.. [P|Us],
  maplist(rewritten_term(L, R, Z), Us, Us1, Vs),
  Motive =.. [P|Vs].

rewritten_term(_, _, _, U, U1, U) :- U == U1, !.
rewritten_term(L, R, Z, U, U1, Z) :-
  unify_with_occurs_check(U, L),
  unify_with_occurs_check(U1, R).
rewritten_term(_, _, _, U, U1, U1) :- var(U), unify_with_occurs_check(U, U1).
rewritten_term(L, R, Z, U, U1, V) :-
  nonvar(U),
  compound(U1),
  U1 =.. [F|Us1],
  U =.. [F|Us],
  maplist(rewritten_term(L, R, Z), Us, Us1, Vs),
  V =.. [F|Vs].

% reverse unit propagation (see rup.pl) over ground premises: premises with variables are ignored,
% which is enough for Vampire's rat, over AVATAR's propositional clauses
rup(_, Hs, Premises, M) :-
  findall(P-Ls, (member(P, Premises), premise(P, [], Ls)), Clauses),
  rup(Hs, Clauses, M).

% AVATAR component clause: C | ~split, where split is defined as C
avatar_component(_, Hs, [_], app(H, [], [lam(D, Split, app(D, Ts, Ms))])) :-
  select(H-(~(~Split)), Hs, Others),
  split(Split, clause(Bs, Ls)),
  binder_variables(Bs, Ts),
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
  split(Split, clause(Bs, Ls)),
  binder_variables(Bs, Xs),
  number_vars(Xs, Fresh0, Fresh),
  hypotheses(Ls, Gs),
  append(Gs, Hs, Hs1),
  binders(Bs, Gs, Binders),
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
