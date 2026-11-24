/*
Reverse unit propagation (RUP), building proof terms of the IR (see ir.pl).

  rup(Hs, Clauses, M)

Hs are hypotheses X-(~L), one for each literal L of the clause to be proved: "L is false".
Clauses are ground premises P-Ls, where P : ~L_0 -> ... -> ~L_n-1 -> ⊥ is a step. M : ⊥ is found
by unit propagation from the hypotheses, as in a SAT solver without decisions or backtracking.

The assignment False maps each literal known to be false to its refutation, of type ~L. It starts
as the hypotheses, and the queue holds the literals made false but not yet propagated, as X-(~L)
like the hypotheses. Every clause is checked once at the start, and then propagating a literal
checks the clauses that contain it:

  - every literal false: a conflict, refuted by P applied to Ms, where Ms refute its literals;
  - all but one literal L false, and L not already true: a unit. L is made true, by making its
    complement C false: the lemma '$lam'(G, ~C, M') @ '$lam'(X, C, P Ms) proves ~C from P,
    with X : C refuting L (see assumption/3), and G-(~C) is added to False and queued;
  - otherwise, the clause is skipped: it is checked again only when one of its literals is made
    false.

The proof term is a chain of lemmas ending in the conflict. Propagation is confluent, so it
commits to each unit found, and fails only if the queue empties without a conflict. The queue is
first in, first out. Clauses are checked against False, rather than having false literals chopped
out of them: updating each clause's literals cost more than looking literals up (about 25% of the
whole run on SWV424-1.200). Every lemma is used in Vampire's rat proofs, whose premise lists are
minimal; premises with redundant units would give unused lemmas.
*/
:- module(rup, [rup/3]).
:- use_module(library(lists)).
:- use_module(ir).
:- use_module(library(assoc)).
:- use_module(ops).
:- op(200, yfx, @). % as exported by ops, which Trealla ignores
:- use_module(logic).

rup(Hs, Clauses, M) :-
  empty_assoc(Empty),
  foldl(occurrences, Clauses, Empty, Occurrences),
  foldl(false, Hs, Empty, False),
  check(Clauses, Occurrences, [], False, M).

% the clauses in which each literal occurs
occurrences(P-Ls, Occurrences0, Occurrences) :-
  sort(Ls, Us),
  foldl(occurrence(P-Ls), Us, Occurrences0, Occurrences).

occurrence(Clause, L, Occurrences0, Occurrences) :-
  ( get_assoc(L, Occurrences0, Cs) -> true ; Cs = [] ),
  put_assoc(L, Occurrences0, [Clause|Cs], Occurrences).

false(X-(~L), False0, False) :- put_assoc(L, False0, X, False).

% propagate(Queue, Occurrences, False, M): fails if the queue empties without conflict
propagate([_-(~L)|Queue], Occurrences, False, M) :-
  ( get_assoc(L, Occurrences, Clauses) -> true ; Clauses = [] ),
  check(Clauses, Occurrences, Queue, False, M).

% check the clauses for a conflict or a new unit, then carry on propagating
check([], Occurrences, Queue, False, M) :- propagate(Queue, Occurrences, False, M).
check([P-Ls|Clauses], Occurrences, Queue, False, M) :-
  (   unit(False, Ls, Unit, Ms), new(Unit, False)
  ->  checked(Unit, P, Ms, Clauses, Occurrences, Queue, False, M)
  ;   check(Clauses, Occurrences, Queue, False, M)
  ).

% every literal is false (conflict), or all but one, L-M with M : ~L to be found
unit(_, [], conflict, []).
unit(False, [L|Ls], Unit, [M|Ms]) :- get_assoc(L, False, M), !, unit(False, Ls, Unit, Ms).
unit(False, [L|Ls], L-M, [M|Ms]) :- falsified(False, Ls, Ms).

falsified(_, [], []).
falsified(False, [L|Ls], [M|Ms]) :- get_assoc(L, False, M), falsified(False, Ls, Ms).

% a conflict, or a unit whose literal is not already true (its complement false)
new(conflict, _).
new(L-_, False) :- complement(L, C), \+ get_assoc(C, False, _).

% a conflict refutes the clause; a unit L makes its complement C false, as a lemma G : ~C
checked(conflict, P, Ms, _, _, _, _, M) :- curried(P, Ms, M).
checked(L-A, P, Ms, Clauses, Occurrences, Queue, False, '$lam'(G, '$proof'(~C), M) @ '$lam'(X, '$proof'(C), N)) :-
  curried(P, Ms, N),
  complement(L, C),
  assumption(C, X, A),
  false(G-(~C), False, False1),
  append(Queue, [G-(~C)], Queue1),
  check(Clauses, Occurrences, Queue1, False1, M).

% X : C refutes the complement of C, as M: X itself if C is negative, ~~-introduction otherwise
assumption(~_, X, X) :- !.
assumption(C, X, '$lam'(K, '$proof'(~C), K @ X)).
