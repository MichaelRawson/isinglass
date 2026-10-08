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
        | contra(H, K, Pos)        H : ¬K applied to Pos, a proof of K
  A   ::= hyp(H)                   a proof of ¬L is a hypothesis
        | sym(F, A)                ...modulo symmetry of equality: A refutes F, the flipped L
        | assume(H, R)             assume the complement of L is false (H : ¬L'), derive ⊥
        | unfold(D, Clause, R)     L is a split symbol: assume its definition D : Clause, derive ⊥
  Pos ::= arg(A0, A)               if K is ~A0, a proof of K is a refutation A of A0
        | intro(Xs, Hs, R)         if K is a split symbol, a proof of its definition for eigenvariables Xs

P is either the name of a step or a definition D introduced by unfold/3.

Tactics produce sketches, refutations without the annotations (see reconstruct.pl):

  S   ::= use(P, Ts, [Arg]) | let(H, L, Arg, S) | contra(H, Pos)
  Arg ::= hyp(H) | sym(Arg) | assume(H, S) | unfold(D, S)
  Pos ::= Arg | intro(Xs, Hs, S)

elaborate/3 checks a sketch and annotates it, producing the IR.
check_all/0 re-checks the stored IR, by erasing and re-elaborating each refutation.
*/
:- module(ir, [elaborate/3, check_all/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% check every step, reporting all incorrect ones
check_all :-
  findall(Name, (ir_step(Name, Conclusion, refute(R)), \+ checks(Conclusion, R)), Incorrect),
  \+ ( member(Name, Incorrect),
       \+ format(user_error, "error: step ~w is incorrect~n", [Name]) ),
  Incorrect == [].

checks(Conclusion, R) :-
  erase(R, S),
  elaborate(Conclusion, S, R1), !,
  R1 == R.

% elaborate(Conclusion, Sketch, R): Sketch refutes the conclusion clause, as R
elaborate(clause(_, Ls), S, R) :-
  hypotheses(Ls, 0, Hs),
  list_to_assoc(Hs, Gamma),
  refutation(Gamma, S, R).

hypotheses([], _, []).
hypotheses([L|Ls], N, [h(N)-neg(L)|Hs]) :- M is N + 1, hypotheses(Ls, M, Hs).

% Gamma is an assoc mapping H to neg(L) (H : ¬L) and D to def(Clause) (D : Clause)
refutation(Gamma, use(P, Ts, Args), use(P, Ts, Es)) :-
  ground(Ts),
  premise(Gamma, P, Clause),
  instance(Clause, Ts, Ls),
  maplist(argument(Gamma), Ls, Args, Es).
refutation(Gamma, let(H, L, Arg, S), let(H, L, E, R)) :-
  argument(Gamma, L, Arg, E),
  put_assoc(H, Gamma, neg(L), Gamma1),
  refutation(Gamma1, S, R).
refutation(Gamma, contra(H, Pos), contra(H, K, E)) :-
  get_assoc(H, Gamma, neg(K)),
  positive(Gamma, K, Pos, E).

premise(Gamma, D, Clause) :- get_assoc(D, Gamma, def(Clause)), !.
premise(_, Name, Clause) :- atom(Name), ir_step(Name, Clause, _), Clause = clause(_, _).

% argument(Gamma, L, Arg, arg(L, A)): Arg is a proof of ¬L, annotated as A
argument(Gamma, L, Arg, arg(L, A)) :- refutes(Gamma, L, Arg, A).

refutes(Gamma, L, hyp(H), hyp(H)) :-
  get_assoc(H, Gamma, neg(K)),
  K == L.
refutes(Gamma, L, sym(Arg), sym(F, A)) :-
  flip(L, F),
  refutes(Gamma, F, Arg, A).
refutes(Gamma, L, assume(H, S), assume(H, R)) :-
  complement(L, C),
  put_assoc(H, Gamma, neg(C), Gamma1),
  refutation(Gamma1, S, R).
refutes(Gamma, Split, unfold(D, S), unfold(D, Clause, R)) :-
  split_def(Split, Clause),
  put_assoc(D, Gamma, def(Clause), Gamma1),
  refutation(Gamma1, S, R).

% positive(Gamma, K, Pos, E): Pos is a proof of K, annotated as E
positive(Gamma, ~A, Arg, E) :- argument(Gamma, A, Arg, E).
positive(Gamma, Split, intro(Xs, Hs, S), intro(Xs, Hs, R)) :-
  split_def(Split, Clause),
  eigenvariables(Xs, Gamma),
  instance(Clause, Xs, Ls),
  pair_hypotheses(Hs, Ls, Gamma, Gamma1),
  refutation(Gamma1, S, R).

% eigenvariables must be distinct and fresh
eigenvariables(Xs, Gamma) :-
  sort(Xs, Sorted),
  same_length(Xs, Sorted),
  \+ ( member(X, Xs), \+ X = '$VAR'(_) ),
  \+ ( member(X, Xs), occurs(X, Gamma) ).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.

pair_hypotheses([], [], Gamma, Gamma).
pair_hypotheses([H|Hs], [L|Ls], Gamma0, Gamma) :-
  put_assoc(H, Gamma0, neg(L), Gamma1),
  pair_hypotheses(Hs, Ls, Gamma1, Gamma).

% erase(R, S): the sketch of refutation R
erase(use(P, Ts, Es), use(P, Ts, Args)) :- maplist(erase_argument, Es, Args).
erase(let(H, L, E, R), let(H, L, Arg, S)) :- erase_argument(E, Arg), erase(R, S).
erase(contra(H, _, intro(Xs, Hs, R)), contra(H, intro(Xs, Hs, S))) :- !, erase(R, S).
erase(contra(H, _, E), contra(H, Arg)) :- erase_argument(E, Arg).

erase_argument(arg(_, A), Arg) :- erase_annotated(A, Arg).

erase_annotated(hyp(H), hyp(H)).
erase_annotated(sym(_, A), sym(Arg)) :- erase_annotated(A, Arg).
erase_annotated(assume(H, R), assume(H, S)) :- erase(R, S).
erase_annotated(unfold(D, _, R), unfold(D, S)) :- erase(R, S).
