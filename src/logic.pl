% utilities for formulas and clauses in the internal syntax (see ops.pl)
:- module(logic, [
  clause_form/2,
  clause_formula/2,
  disjunction/2,
  complement/2,
  flip/2,
  number_vars/3,
  split_def/2,
  symbols/3
]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(db).

% a formula is a clause: clause(Xs, Literals)
clause_form('!'(Xs, F), C) :- !, C = clause(Xs, Ls), literals(F, Ls).
% AVATAR clauses are printed as (! [X] : C) | ~split
clause_form(('!'(Xs, F) | G), C) :- !, C = clause(Xs, Ls), literals((F | G), Ls).
clause_form(F, clause([], Ls)) :- literals(F, Ls).

literals('$false', []) :- !.
literals((F | G), Ls) :- !, literals(F, Fs), literals(G, Gs), append(Fs, Gs, Ls).
literals(~A, [~A]) :- !, atomic_formula(A).
literals(A, [A]) :- atomic_formula(A).

% and back again
clause_formula(clause([], Ls), F) :- !, disjunction(Ls, F).
clause_formula(clause(Xs, Ls), '!'(Xs, F)) :- disjunction(Ls, F).

disjunction([], '$false').
disjunction([L], L) :- !.
disjunction([L|Ls], (L | F)) :- disjunction(Ls, F).

atomic_formula(A) :- nonvar(A), \+ connective(A).

connective('$true').
connective('$false').
connective(~_).
connective(_ | _).
connective(_ & _).
connective(_ => _).
connective(_ <=> _).
connective('!'(_, _)).
connective('?'(_, _)).

complement(~A, L) :- !, L = A.
complement(A, ~A).

% the same literal, with the equation the other way round
flip(S = T, T = S).
flip(~(S = T), ~(T = S)).

% bind variables Vs to '$VAR'(N0), '$VAR'(N0 + 1), ...
number_vars([], N, N).
number_vars(['$VAR'(N0)|Vs], N0, N) :- N1 is N0 + 1, number_vars(Vs, N1, N).

% the definition of an AVATAR split symbol, a fresh instance
split_def(Symbol, Clause) :- split(Symbol, Clause), !.

% function and predicate symbols of a formula, as Name/Arity lists
symbols(F, Fs, Ps) :- symbols(F, [], Fs, [], Ps).

symbols(V, Fs, Fs, Ps, Ps) :- var(V), !.
symbols('$VAR'(_), Fs, Fs, Ps, Ps) :- !.
symbols('$true', Fs, Fs, Ps, Ps) :- !.
symbols('$false', Fs, Fs, Ps, Ps) :- !.
symbols('!'(_, F), Fs0, Fs, Ps0, Ps) :- !, symbols(F, Fs0, Fs, Ps0, Ps).
symbols('?'(_, F), Fs0, Fs, Ps0, Ps) :- !, symbols(F, Fs0, Fs, Ps0, Ps).
symbols(S = T, Fs0, Fs, Ps, Ps) :- !, terms_symbols([S, T], Fs0, Fs).
symbols(F, Fs0, Fs, Ps0, Ps) :-
  connective(F), !,
  F =.. [_|Gs],
  formulas_symbols(Gs, Fs0, Fs, Ps0, Ps).
symbols(A, Fs0, Fs, Ps0, Ps) :-
  functor(A, P, N),
  add(P/N, Ps0, Ps),
  A =.. [_|Ts],
  terms_symbols(Ts, Fs0, Fs).

formulas_symbols([], Fs, Fs, Ps, Ps).
formulas_symbols([G|Gs], Fs0, Fs, Ps0, Ps) :-
  symbols(G, Fs0, Fs1, Ps0, Ps1),
  formulas_symbols(Gs, Fs1, Fs, Ps1, Ps).

terms_symbols([], Fs, Fs).
terms_symbols([T|Ts], Fs0, Fs) :- term_symbols(T, Fs0, Fs1), terms_symbols(Ts, Fs1, Fs).

term_symbols(V, Fs, Fs) :- var(V), !.
term_symbols('$VAR'(_), Fs, Fs) :- !.
term_symbols(T, Fs0, Fs) :-
  functor(T, F, N),
  add(F/N, Fs0, Fs1),
  T =.. [_|Ts],
  terms_symbols(Ts, Fs1, Fs).

add(X, Xs, Ys) :- ( memberchk(X, Xs) -> Ys = Xs ; Ys = [X|Xs] ).
