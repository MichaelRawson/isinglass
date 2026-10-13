/*
Refuting a formula by a hypothesis, and the proof terms that this builds (see ir.pl), shared by the
tactics of reconstruct.pl and descent.pl. Hypotheses Hs are a list of X-T pairs, where X : T.
*/
:- module(matching, [matches/3, refutes/4, flipped/3, applied/3, lambdas/3]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).

% a hypothesis refutes premise literal L, as M : ~L, or L is a trivial inequality S != S
matches(Hs, L, M) :-
  member(X-T, Hs),
  refutes(T, X, L, M).
matches(_, ~'$='(A, S, T), lam(K, ~'$='(A, S, S), app(K, [], [app('$refl', [A, S], [])]))) :-
  unify_with_occurs_check(S, T).

% refutes(T, X, L, M): X : T refutes L as M, modulo symmetry of equality
refutes(~K, X, L, X) :- unify_with_occurs_check(K, L).
refutes(~K, X, L, M) :- flip(K, F), unify_with_occurs_check(F, L), flipped(L, X, M).
refutes(A, X, ~B, lam(K, ~B, app(K, [], [X]))) :- A \= ~_, unify_with_occurs_check(A, B).
refutes('$='(A, S, T), X, ~B, lam(K, ~B, app(K, [], [app('$sym', [A, S, T], [X])]))) :-
  unify_with_occurs_check('$='(A, T, S), B).

% X refutes L with the equation the other way round
flipped('$='(A, S, T), X, lam(E, '$='(A, S, T), app(X, [], [app('$sym', [A, S, T], [E])]))).
flipped(~'$='(A, S, T), X, lam(K, ~'$='(A, S, T), app(X, [], [lam(E, '$='(A, T, S), app(K, [], [app('$sym', [A, T, S], [E])]))]))).

% M : ~T applied to W : T; a λ is β-reduced, to a let unless W is a hypothesis, so that heads stay
% variables or constants
applied(M, W, app(M, [], [W])) :- var(M), !.
applied(lam(V, _, B), W, B) :- var(W), !, V = W.
applied(lam(V, T, B), W, let(V, T, W, B)).

% M abstracted over binders X-T
lambdas([], M, M).
lambdas([X-T|Xs], M, lam(X, T, N)) :- lambdas(Xs, M, N).
