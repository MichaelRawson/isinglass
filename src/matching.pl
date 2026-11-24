/*
Refuting a formula by a hypothesis, and the proof terms that this builds (see ir.pl), shared by the
tactics of reconstruct.pl and transform.pl. Hypotheses Hs are a list of X-T pairs, where X : T.
*/
:- module(matching, [matches/3, refutes/4, flipped/3, applied/3, lambdas/3]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).

% a hypothesis refutes premise literal L, as M : ~L, or L is a trivial inequality S != S
matches(Hs, L, M) :-
  member(X-T, Hs),
  refutes(T, X, L, M).
matches(_, ~'$='(A, S, T), '$lam'(K, '$proof'(~'$='(A, S, S)), K @ '$refl')) :-
  unify_with_occurs_check(S, T).

% refutes(T, X, L, M): X : T refutes L as M, modulo symmetry of equality
refutes(~K, X, L, X) :- unify_with_occurs_check(K, L).
refutes(~K, X, L, M) :- flip(K, F), unify_with_occurs_check(F, L), flipped(L, X, M).
refutes(A, X, ~B, '$lam'(K, '$proof'(~B), K @ X)) :- A \= ~_, unify_with_occurs_check(A, B).
refutes('$='(A, S, T), X, ~B, '$lam'(K, '$proof'(~B), K @ ('$sym' @ X))) :-
  unify_with_occurs_check('$='(A, T, S), B).

% X refutes L with the equation the other way round
flipped('$='(A, S, T), X, '$lam'(E, '$proof'('$='(A, S, T)), X @ ('$sym' @ E))).
flipped(~'$='(A, S, T), X, '$lam'(K, '$proof'(~'$='(A, S, T)), X @ '$lam'(E, '$proof'('$='(A, T, S)), K @ ('$sym' @ E)))).

% M : ~T applied to W : T; a λ applied to a hypothesis W is β-reduced
applied(M, W, B) :- nonvar(M), M = '$lam'(V, _, B), var(W), !, V = W.
applied(M, W, M @ W).

% M abstracted over binders X-T
lambdas([], M, M).
lambdas([X-T|Xs], M, '$lam'(X, T, N)) :- lambdas(Xs, M, N).
