/*
Portable helpers that Prolog systems provide differently, or not at all. Names avoid clashing with
built-in and library predicates, since a module cannot choose a definition per system (no :- if).
*/
:- module(utils, [each/2, warn/1, final/2, range/3, included_excluded/4, bag_sort/2, named/3, step_name/2, definition_name/2]).

% forall/2, which is built in to SWI and Trealla, but in library(iso_ext) in Scryer
:- meta_predicate(each(0, 0)).
each(Condition, Action) :- \+ ( Condition, \+ Action ).

% write the items of a list to user_error, as a line: format/2,3 and its strings are not portable
warn(Items) :- warn_(Items), nl(user_error).

warn_([]).
warn_([Item|Items]) :- ( atom(Item), named(_, Bare, Item) -> true ; Bare = Item ), write(user_error, Bare), warn_(Items).

% The names of steps, of definitions and of inputs are atoms with a reserved prefix, so that they are
% apart from symbols (TPTP names them in another namespace), from built-ins, and from each other:
% Name is Bare (an atom or an integer) of Kind (step, definition or input), in either direction
named(Kind, Bare, Name) :- atom(Name), !, name_prefix(Kind, Prefix), atom_concat(Prefix, Bare, Name).
named(Kind, Bare, Name) :-
  name_prefix(Kind, Prefix),
  ( number(Bare) -> number_codes(Bare, Cs), atom_codes(A, Cs) ; A = Bare ),
  atom_concat(Prefix, A, Name).

name_prefix(step, '$step:').
name_prefix(definition, '$def:').
name_prefix(input, '$input:').

% the step of a prover's statement Bare, and the step that defines Symbol
step_name(Bare, Name) :- named(step, Bare, Name).
definition_name(Symbol, Name) :- named(definition, Symbol, Name).

% the last element of a list (last/2, which Scryer's library(lists) lacks)
final([X], X) :- !.
final([_|Xs], X) :- final(Xs, X).

% the elements of a list that satisfy Condition, and those that do not, in order (partition/4, which
% Scryer and Trealla lack)
:- meta_predicate(included_excluded(1, ?, ?, ?)).
included_excluded(_, [], [], []).
included_excluded(Condition, [X|Xs], Included, Excluded) :-
  (   call(Condition, X)
  ->  Included = [X|Included1], Excluded = Excluded1
  ;   Included = Included1, Excluded = [X|Excluded1]
  ),
  included_excluded(Condition, Xs, Included1, Excluded1).

% a list sorted in the standard order, keeping duplicates (msort/2, which Scryer lacks), as keysort/2
% is stable
bag_sort(Xs, Sorted) :- keyed(Xs, Pairs), keysort(Pairs, SortedPairs), keyed(Sorted, SortedPairs).

keyed([], []).
keyed([X|Xs], [X-x|Pairs]) :- keyed(Xs, Pairs).

% the integers Low, Low + 1, ..., High - 1 (empty if Low >= High)
range(Low, High, []) :- Low >= High, !.
range(Low, High, [Low|Ns]) :- Next is Low + 1, range(Next, High, Ns).
