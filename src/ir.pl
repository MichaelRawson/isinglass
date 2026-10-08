/*
The intermediate representation (IR) of proofs, and its checker.

  ir_step(Name, Conclusion, Justification)        (db.pl)

  Conclusion    ::= clause(Xs, Literals) | formula(F)
  Justification ::= input(Role, Source)
                  | split_def(Symbol, Clause)       Symbol is defined as Clause (AVATAR)
                  | refute(R)                       see below
                  | todo(Record, Parents)           not (yet) reconstructed

No particular logic is fixed. A refutation R derives an abstract ⊥ under hypotheses;
for a conclusion clause with literals L_0, ..., L_n-1, hypothesis h(I) is ¬L_I.
Here ¬L is "L implies ⊥", so for negative literals ~A, ¬~A is ¬¬A, not A.
Classically ⊥ is falsity, but in the A-translation ⊥ is the conjecture G.
Split symbols are interpreted as (the hypothetical reading of) their defining clause.
Every argument carries the literal L that it refutes, as arg(L, A).

  R   ::= use(P, Ts, [arg(L, A)])  instantiate premise clause P with terms Ts, refuting each literal L
        | let(H, L, arg(L, A), R)  H : ¬L is A (a lemma)
        | contra(H, K, arg(K', A)) H : ¬K, and A refutes its complement K', so proves K
  P   ::= Name                     a step
        | def(H, Split)            the definition of Split, from H : ¬~Split
  A   ::= hyp(H)                   a proof of ¬L is a hypothesis
        | sym(F, H)                ...modulo symmetry of equality: H : ¬F, F the flipped L
        | assume(H, R)             assume the complement of L is false (H : ¬L'), derive ⊥
        | intro(Xs, Hs, R)         L is ~Split: prove the definition of Split for eigenvariables Xs,
                                   with hypotheses Hs refuting its literals

A definition is used through a hypothesis H : ¬~Split, i.e. ¬¬Split, rather than Split itself.
This is constructive: the definition reads as Π xs, ¬L_0 → ... → ⊥, which ends in ⊥, so it is
¬¬-stable in minimal logic: from n : ¬¬D, λ xs hs, n (λ d, d xs hs) proves D.
Dually, intro refutes ~Split by proving Split, which implies ¬¬Split. A literal ~Split may also be
refuted propositionally by assume, which treats Split as an atom (as RUP does).

Tactics produce sketches, refutations without the annotations (see reconstruct.pl):

  S   ::= use(Name | H, Ts, [Arg]) | let(H, L, Arg, S) | contra(H, Arg)
  Arg ::= hyp(H) | sym(H) | assume(H, S) | intro(Xs, Hs, S)

elaborate/3 checks a sketch and annotates it, producing the IR.
*/
:- module(ir, [elaborate/3]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% Sketch refutes the conclusion clause, as R
elaborate(clause(_, Ls), S, R) :-
  hypotheses(Ls, 0, Hs),
  list_to_assoc(Hs, Gamma),
  refutation(Gamma, S, R).

hypotheses([], _, []).
hypotheses([L|Ls], N, [h(N)-neg(L)|Hs]) :- M is N + 1, hypotheses(Ls, M, Hs).

% Gamma is an assoc mapping H to neg(L) (H : ¬L)
refutation(Gamma, use(P, Ts, Args), use(Q, Ts, Es)) :-
  ground(Ts),
  premise(Gamma, P, Q, clause(Ts, Ls)),
  maplist(argument(Gamma), Ls, Args, Es).
refutation(Gamma, let(H, L, Arg, S), let(H, L, E, R)) :-
  argument(Gamma, L, Arg, E),
  put_assoc(H, Gamma, neg(L), Gamma1),
  refutation(Gamma1, S, R).
refutation(Gamma, contra(H, Arg), contra(H, K, E)) :-
  get_assoc(H, Gamma, neg(K)),
  complement(K, C),
  argument(Gamma, C, Arg, E).

% premise(Gamma, P, Q, Clause): a fresh instance of premise clause P, annotated as Q
premise(_, Name, Name, Clause) :- atom(Name), !, step(Name, Clause, _), Clause = clause(_, _).
premise(Gamma, H, def(H, Split), Clause) :- get_assoc(H, Gamma, neg(~Split)), split_def(Split, Clause).

% argument(Gamma, L, Arg, arg(L, A)): Arg is a proof of ¬L, annotated as A
argument(Gamma, L, Arg, arg(L, A)) :- refutes(Gamma, L, Arg, A).

refutes(Gamma, L, hyp(H), hyp(H)) :-
  get_assoc(H, Gamma, neg(K)),
  K == L.
refutes(Gamma, L, sym(H), sym(F, H)) :-
  flip(L, F),
  refutes(Gamma, F, hyp(H), _).
refutes(Gamma, L, assume(H, S), assume(H, R)) :-
  complement(L, C),
  put_assoc(H, Gamma, neg(C), Gamma1),
  refutation(Gamma1, S, R).
refutes(Gamma, ~Split, intro(Xs, Hs, S), intro(Xs, Hs, R)) :-
  eigenvariables(Xs, Gamma),
  split_def(Split, clause(Xs, Ls)),
  pair_hypotheses(Hs, Ls, Gamma, Gamma1),
  refutation(Gamma1, S, R).

% eigenvariables must be distinct and fresh
eigenvariables(Xs, Gamma) :-
  sort(Xs, Sorted),
  same_length(Xs, Sorted),
  forall(member(X, Xs), X = '$VAR'(_)),
  forall(member(X, Xs), \+ occurs(X, Gamma)).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.

pair_hypotheses([], [], Gamma, Gamma).
pair_hypotheses([H|Hs], [L|Ls], Gamma0, Gamma) :-
  put_assoc(H, Gamma0, neg(L), Gamma1),
  pair_hypotheses(Hs, Ls, Gamma1, Gamma).
