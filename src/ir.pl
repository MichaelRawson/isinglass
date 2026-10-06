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

  R   ::= use(P, Ts, Args)    instantiate premise clause P with terms Ts, refute each literal with Args
        | let(H, L, Arg, R)   H : ¬L is Arg (a lemma)
        | contra(H, Pos)      H : ¬K applied to Pos, a proof of K
  Arg ::= hyp(H)              a proof of ¬L is a hypothesis
        | sym(Arg)            ...modulo symmetry of equality
        | assume(H, R)        assume the complement of L is false (H : ¬L'), derive ⊥
        | unfold(D, R)        L is a split symbol: assume its definition D, derive ⊥
  Pos ::= Arg                 if K is ~A, a proof of K is a proof of ¬A
        | intro(Xs, Hs, R)    if K is a split symbol, a proof of its definition for eigenvariables Xs

P is either the name of a step or a definition D introduced by unfold/2.

elaborate/2 checks a justification and produces an elaborated version that is
easier for back ends to print, in which every argument carries the literal it refutes:

  E   ::= use(P, Ts, [arg(L, A)]) | let(H, L, arg(L, A), E) | contra(H, K, Pos)
  A   ::= hyp(H) | sym(L, A) | assume(H, E) | unfold(D, Clause, E)
  Pos ::= arg(L, A) | intro(Xs, [H-L], E)

where in sym(L, A), A refutes L, so sym(L, A) refutes the flipped L.
*/
:- module(ir, [elaborate/2, check_all/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% check every step, reporting all incorrect ones
check_all :-
  findall(Name, (ir_step(Name, _, _), \+ elaborate(Name, _)), Incorrect),
  \+ ( member(Name, Incorrect),
       \+ format(user_error, "error: step ~w is incorrect~n", [Name]) ),
  Incorrect == [].

% elaborate(Name, Elaborated)
elaborate(Name, E) :-
  ir_step(Name, Conclusion, Justification),
  elaborate(Justification, Conclusion, E), !.

elaborate(input(Role, Source), _, input(Role, Source)).
elaborate(split_def(Symbol, Clause), _, split_def(Symbol, Clause)).
elaborate(todo(Record, Parents), _, todo(Record, Parents)).
elaborate(refute(R), clause(_, Ls), refute(Hs, E)) :-
  hypotheses(Ls, 0, Hs),
  list_to_assoc(Hs, Gamma),
  refutation(Gamma, R, E).

hypotheses([], _, []).
hypotheses([L|Ls], N, [h(N)-neg(L)|Hs]) :- M is N + 1, hypotheses(Ls, M, Hs).

% Gamma is an assoc mapping H to neg(L) (H : ¬L) and D to def(Clause) (D : Clause)
refutation(Gamma, use(P, Ts, Args), use(P, Ts, Es)) :-
  ground(Ts),
  premise(Gamma, P, Clause),
  instance(Clause, Ts, Ls),
  maplist(argument(Gamma), Ls, Args, Es).
refutation(Gamma, let(H, L, Arg, R), let(H, L, E, ER)) :-
  argument(Gamma, L, Arg, E),
  put_assoc(H, Gamma, neg(L), Gamma1),
  refutation(Gamma1, R, ER).
refutation(Gamma, contra(H, Pos), contra(H, K, E)) :-
  get_assoc(H, Gamma, neg(K)),
  positive(Gamma, K, Pos, E).

premise(Gamma, D, Clause) :- get_assoc(D, Gamma, def(Clause)), !.
premise(_, Name, Clause) :- atom(Name), ir_step(Name, Clause, _), Clause = clause(_, _).

% argument(Gamma, L, Arg, arg(L, A)): Arg is a proof of ¬L
argument(Gamma, L, Arg, arg(L, A)) :- refutes(Gamma, L, Arg, A).

refutes(Gamma, L, hyp(H), hyp(H)) :-
  get_assoc(H, Gamma, neg(K)),
  K == L.
refutes(Gamma, L, sym(Arg), sym(F, A)) :-
  flip(L, F),
  refutes(Gamma, F, Arg, A).
refutes(Gamma, L, assume(H, R), assume(H, E)) :-
  complement(L, C),
  put_assoc(H, Gamma, neg(C), Gamma1),
  refutation(Gamma1, R, E).
refutes(Gamma, Split, unfold(D, R), unfold(D, Clause, E)) :-
  split_def(Split, Clause),
  put_assoc(D, Gamma, def(Clause), Gamma1),
  refutation(Gamma1, R, E).

% positive(Gamma, K, Pos, E): Pos is a proof of K
positive(Gamma, ~A, Arg, E) :- argument(Gamma, A, Arg, E).
positive(Gamma, Split, intro(Xs, Hs, R), intro(Xs, HLs, E)) :-
  split_def(Split, Clause),
  eigenvariables(Xs, Gamma),
  instance(Clause, Xs, Ls),
  pair_hypotheses(Hs, Ls, Gamma, Gamma1, HLs),
  refutation(Gamma1, R, E).

% eigenvariables must be distinct and fresh
eigenvariables(Xs, Gamma) :-
  sort(Xs, Sorted),
  same_length(Xs, Sorted),
  \+ ( member(X, Xs), \+ X = '$VAR'(_) ),
  \+ ( member(X, Xs), occurs(X, Gamma) ).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.

pair_hypotheses([], [], Gamma, Gamma, []).
pair_hypotheses([H|Hs], [L|Ls], Gamma0, Gamma, [H-L|HLs]) :-
  put_assoc(H, Gamma0, neg(L), Gamma1),
  pair_hypotheses(Hs, Ls, Gamma1, Gamma, HLs).
