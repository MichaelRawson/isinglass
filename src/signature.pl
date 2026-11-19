/*
The signature, shared by front ends and back ends: symbol(Name, Params, Args, Sort) facts (db.pl).

Types are terms of the pseudo-sort '$tType', as in TF1: a type constructor such as list is declared
symbol(list, [], ['$tType'], '$tType'), and a polymorphic symbol takes its type arguments first,
as f(Types..., Terms...), with Params the Prolog variables that they instantiate. So every lookup
is a fresh instance, and instantiation is unification. Built-in symbols are not in the database.
Untyped symbols get the default sorts, '$i' and '$o'.
*/
:- module(signature, [
  declare/1,
  default_signature/0,
  overloaded/1,
  instance/5,
  term_sort/3,
  typed/3,
  type_arity/2
]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% a type declaration, as read by load.pl
declare(type(Name, Params, Args, Sort)) :- record(symbol(Name, Params, Args, Sort)).

% built-in symbols: equality, the sorts of individuals and propositions, and an arbitrary inhabitant
% of a sort (see close.pl)
builtin('$=', [S], [S, S], '$o').
builtin('$i', [], [], '$tType').
builtin('$o', [], [], '$tType').
builtin('$inhabited', [S], [], S).

% the symbol F of arity N, counting type arguments: built in, or of the database
signature_symbol(F/N, Ps, Ss, Sort) :-
  ( builtin(F, Ps, Ss, Sort) ; symbol(F, Ps, Ss, Sort) ),
  arity(Ps, Ss, N), !.

% T is an instance of a symbol of the signature, with type arguments Types and term arguments Us,
% of sorts Ss, and T is of sort Sort
instance(T, Types, Us, Ss, Sort) :-
  functor(T, F, N),
  signature_symbol(F/N, Ps, Ss, Sort),
  T =.. [_|As],
  append(Ps, Us, As),
  Types = Ps.

% the number of type arguments of a term or atom
type_arity(T, K) :- instance(T, Types, _, _, _), !, length(Types, K).
type_arity(_, 0).

% the sort of term T, where binders Bs give the sorts of variables; an untyped variable or symbol is
% an individual
term_sort(Bs, T, S) :- var(T), !, ( member(X:S0, Bs), X == T -> S = S0 ; S = '$i' ).
term_sort(_, T, S) :- instance(T, _, _, _, S0), !, S = S0.
term_sort(_, _, '$i').

% formula F with every equation S = T given its sort A, as '$='(A, S, T), where binders Bs give the
% sorts of variables
typed(Bs, '!'(C, F0), F) :- !, F = '!'(C, F1), typed([C|Bs], F0, F1).
typed(Bs, '?'(C, F0), F) :- !, F = '?'(C, F1), typed([C|Bs], F0, F1).
typed(Bs, S = T, F) :- !, F = '$='(A, S, T), ( var(S) -> term_sort(Bs, T, A) ; term_sort(Bs, S, A) ).
typed(Bs, F0, F) :- connective(F0, _), !, F0 =.. [C|Gs0], maplist(typed(Bs), Gs0, Gs), F =.. [C|Gs].
typed(_, A, A).

% untyped symbols get the default sorts
default_signature :-
  findall(P-S, (step(_, C, _), conclusion_symbol(C, P, S)), Ss),
  sort(Ss, Symbols),
  maplist(default_symbol, Symbols).

conclusion_symbol(clause(_, Ls), P, S) :- member(L, Ls), formula_symbol(L, P, S).
conclusion_symbol(formula(F), P, S) :- formula_symbol(F, P, S).

% a symbol Name/Arity of a formula, one at a time, in Position function or predicate, outside type
% arguments
formula_symbol(F, P, S) :- connective(F, Gs), !, member(G, Gs), formula_symbol(G, P, S).
formula_symbol('$='(_, A, B), P, S) :- !, ( term_symbol(A, P, S) ; term_symbol(B, P, S) ).
formula_symbol(A, P, S) :- functor_symbol(predicate, A, P, S).

term_symbol(T, P, S) :- nonvar(T), functor_symbol(function, T, P, S).

functor_symbol(Position, T, Position, F/N) :- functor(T, F, N).
functor_symbol(_, T, P, S) :-
  ( instance(T, _, Us, _, _) -> true ; T =.. [_|Us] ),
  member(U, Us),
  term_symbol(U, P, S).

default_sort(function, '$i').
default_sort(predicate, '$o').

% functions sort before predicates, so a name used as both is a function
default_symbol(_-Symbol) :- signature_symbol(Symbol, _, _, _), !.
default_symbol(P-(F/N)) :-
  default_sort(P, Sort),
  length(Args, N),
  maplist(=('$i'), Args),
  record(symbol(F, [], Args, Sort)).

arity(Ps, As, N) :- length(Ps, K), length(As, M), N =:= K + M.

% the name F is also used with an arity other than N, so a back end must tell them apart
overloaded(F/N) :- symbol(F, Ps, As, _), \+ arity(Ps, As, N), !.
