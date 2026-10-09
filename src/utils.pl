/*
Portable helpers that Prolog systems provide differently, or not at all. Names avoid clashing with
built-in and library predicates, since a module cannot choose a definition per system (no :- if).
forall/2 is built in to SWI, but in library(iso_ext) in Scryer: an import for Scryer, later.
*/
:- module(utils, [range/3]).

% the integers Low, Low + 1, ..., High - 1 (empty if Low >= High)
range(Low, High, []) :- Low >= High, !.
range(Low, High, [Low|Ns]) :- Next is Low + 1, range(Next, High, Ns).
