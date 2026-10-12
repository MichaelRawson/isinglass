/*
Portable helpers that Prolog systems provide differently, or not at all. Names avoid clashing with
built-in and library predicates, since a module cannot choose a definition per system (no :- if).
*/
:- module(utils, [each/2, warn/1, final/2, range/3, list//1]).

% forall/2, which is built in to SWI and Trealla, but in library(iso_ext) in Scryer
:- meta_predicate(each(0, 0)).
each(Condition, Action) :- \+ ( Condition, \+ Action ).

% write the items of a list to user_error, as a line: format/2,3 and its strings are not portable
warn(Items) :- warn_(Items), nl(user_error).

warn_([]).
warn_([Item|Items]) :- write(user_error, Item), warn_(Items).

% the last element of a list (last/2, which Scryer's library(lists) lacks)
final([X], X) :- !.
final([_|Xs], X) :- final(Xs, X).

% the integers Low, Low + 1, ..., High - 1 (empty if Low >= High)
range(Low, High, []) :- Low >= High, !.
range(Low, High, [Low|Ns]) :- Next is Low + 1, range(Next, High, Ns).

% the elements of a list, in a grammar body: a variable body needs library(dcgs) in Scryer
list([]) --> [].
list([X|Xs]) --> [X], list(Xs).
