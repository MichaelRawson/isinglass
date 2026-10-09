/*
Printing helpers shared by the back ends: output is built by DCGs over code lists, one top-level
nonterminal at a time, and written with write/1.
*/
:- module(printing, [out/1, atom//1, number//1, codes//1]).

% G is a nonterminal of the calling module
:- meta_predicate(out(2)).

out(G) :- phrase(G, Cs), atom_codes(A, Cs), write(A).

atom(A) --> { atom_codes(A, Cs) }, codes(Cs).
number(N) --> { number_codes(N, Cs) }, codes(Cs).

codes([]) --> [].
codes([C|Cs]) --> [C], codes(Cs).
