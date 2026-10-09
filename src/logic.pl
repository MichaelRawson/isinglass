% utilities for formulas and clauses in the internal syntax (see ops.pl)
:- module(logic, [
  formula_clause/2,
  binder_variables/2,
  clause_formula/2,
  disjunction/2,
  complement/2,
  flip/2,
  number_vars/3,
  substitute/4,
  formula_symbol/3
]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(ops).

% a formula is a clause: clause(Bs, Literals), with quantifier binders Bs
formula_clause('!'(Bs, F), C) :- !, C = clause(Bs, Ls), literals(F, Ls).
% AVATAR clauses are printed as (! [X] : C) | ~split
formula_clause(('!'(Bs, F) | G), C) :- !, C = clause(Bs, Ls), literals((F | G), Ls).
formula_clause(F, clause([], Ls)) :- literals(F, Ls).

literals('$false', []) :- !.
literals((F | G), Ls) :- !, literals(F, Fs), literals(G, Gs), append(Fs, Gs, Ls).
literals(~A, [~A]) :- !, atomic_formula(A).
literals(A, [A]) :- atomic_formula(A).

% and back again
clause_formula(clause([], Ls), F) :- !, disjunction(Ls, F).
clause_formula(clause(Bs, Ls), '!'(Bs, F)) :- disjunction(Ls, F).

% the variables of quantifier binders X : Sort
binder_variables(Bs, Xs) :- maplist(binder_variable, Bs, Xs).

binder_variable(X:_, X).

disjunction([], '$false').
disjunction([L], L) :- !.
disjunction([L|Ls], (L | F)) :- disjunction(Ls, F).

atomic_formula(A) :- nonvar(A), \+ connective(A, _).

% a formula with a connective at its root, and its subformulas
connective('$true', []).
connective('$false', []).
connective(~F, [F]).
connective(F | G, [F, G]).
connective(F & G, [F, G]).
connective(F => G, [F, G]).
connective(F <=> G, [F, G]).
connective('!'(_, F), [F]).
connective('?'(_, F), [F]).

complement(~A, L) :- !, L = A.
complement(A, ~A).

% the same literal, with the equation the other way round
flip(S = T, T = S).
flip(~(S = T), ~(T = S)).

% bind variables Vs to '$VAR'(N0), '$VAR'(N0 + 1), ...
number_vars([], N, N).
number_vars(['$VAR'(N0)|Vs], N0, N) :- N1 is N0 + 1, number_vars(Vs, N1, N).

% B is A with every occurrence of the term X replaced by S
substitute(X, S, A, B) :- A == X, !, B = S.
substitute(_, _, A, B) :- \+ compound(A), !, B = A.
substitute(X, S, A, B) :-
  A =.. [F|As],
  maplist(substitute(X, S), As, Bs),
  B =.. [F|Bs].

% a symbol Name/Arity of a formula, one at a time, in Position function or predicate
formula_symbol(F, P, S) :- connective(F, Gs), !, member(G, Gs), formula_symbol(G, P, S).
formula_symbol(A = B, P, S) :- !, ( term_symbol(A, P, S) ; term_symbol(B, P, S) ).
formula_symbol(A, P, S) :- functor_symbol(predicate, A, P, S).

term_symbol(T, P, S) :- nonvar(T), functor_symbol(function, T, P, S).

functor_symbol(Position, T, Position, F/N) :- functor(T, F, N).
functor_symbol(_, T, P, S) :- T =.. [_|Ts], member(U, Ts), term_symbol(U, P, S).
