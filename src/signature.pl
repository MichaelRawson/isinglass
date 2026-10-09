% the default signature, shared by front ends
:- module(signature, [default_signature/0, overloaded/1]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(logic).
:- use_module(db).

% untyped symbols get the default sorts
default_signature :-
  findall(P-S, (step(_, C, _), conclusion_symbol(C, P, S)), Ss),
  sort(Ss, Symbols),
  maplist(default_symbol, Symbols).

conclusion_symbol(clause(_, Ls), P, S) :- member(L, Ls), formula_symbol(L, P, S).
conclusion_symbol(formula(F), P, S) :- formula_symbol(F, P, S).

default_sort(function, '$i').
default_sort(predicate, '$o').

% functions sort before predicates, so a name used as both is a function
default_symbol(_-(F/N)) :- length(As, N), symbol(F, As, _), !.
default_symbol(P-(F/N)) :-
  default_sort(P, Sort),
  length(Args, N),
  maplist(=('$i'), Args),
  assertz(symbol(F, Args, Sort)).

% the name F is also used with an arity other than N, so a back end must tell them apart
overloaded(F/N) :- symbol(F, As, _), \+ length(As, N), !.
