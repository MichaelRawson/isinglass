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
  occurs/2,
  subterm/2,
  canonical/2,
  opened/2,
  open_binders/4,
  renamed/3,
  connective/2
]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
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
connective((F | G), [F, G]).
connective((F & G), [F, G]).
connective((F => G), [F, G]).
connective((F <=> G), [F, G]).
connective('!'(_, F), [F]).
connective('?'(_, F), [F]).

complement(~A, L) :- !, L = A.
complement(A, ~A).

% the same literal, with the equation the other way round
flip('$='(A, S, T), '$='(A, T, S)).
flip(~'$='(A, S, T), ~'$='(A, T, S)).

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

% the term X occurs in T
occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.

% a subterm S of T that is not a variable
subterm(T, T) :- nonvar(T).
subterm(T, S) :- compound(T), T =.. [_|Ts], member(U, Ts), subterm(U, S).

% a formula with its bound variables named canonically, so that formulas are compared up to these
% names syntactically: a bound variable is '$BOUND'(H), where H is the number of binders nested in
% its scope. So a variable is bound outside any of the same name, and instantiating the outermost
% keeps the rest canonical. A binder named otherwise is substituted, a pass over its scope: a formula
% whose names may all change should be opened first
canonical(F0, F) :- canonical(F0, F, _).

canonical(F0, F, H) :-
  nonvar(F0),
  F0 =.. [Q, Bs0, G0],
  ( Q == '!' ; Q == '?' ), !,
  canonical(G0, G1, H0),
  bound(Bs0, G1, H0, H, Bs, G),
  F =.. [Q, Bs, G].
canonical(F0, F, H) :-
  nonvar(F0),
  connective(F0, Gs0), !,
  F0 =.. [C|_],
  foldl(canonical_part, Gs0, Gs, 0, H),
  F =.. [C|Gs].
canonical(A, A, 0).

canonical_part(F0, F, H0, H) :- canonical(F0, F, H1), H is max(H0, H1).

% the formula with each bound variable named canonically a fresh Prolog variable, in one pass, by the
% names of the binders in scope (which are distinct on a path); other binders are kept
opened(F0, F) :- empty_assoc(Scope), opened(F0, Scope, F).

opened(F0, Scope0, F) :-
  nonvar(F0),
  F0 =.. [Q, Bs0, G0],
  ( Q == '!' ; Q == '?' ), !,
  open_binders(Bs0, Bs, Scope0, Scope),
  opened(G0, Scope, G),
  F =.. [Q, Bs, G].
opened(F0, Scope, F) :-
  nonvar(F0),
  connective(F0, _), !,
  F0 =.. [C|Gs0],
  maplist(opened_in(Scope), Gs0, Gs),
  F =.. [C|Gs].
opened(A0, Scope, A) :- renamed(Scope, A0, A).

opened_in(Scope, F0, F) :- opened(F0, Scope, F).

% the binders Bs0 with fresh variables, added to the Scope; the sort of a binder may name those before
% it (TF1)
open_binders(Bs0, Bs, Scope0, Scope) :- foldl(opened_binder, Bs0, Bs, Scope0, Scope).

opened_binder(X:S0, V:S, Scope0, Scope) :-
  renamed(Scope0, S0, S),
  ( nonvar(X), X = '$BOUND'(_) -> put_assoc(X, Scope0, V, Scope) ; V = X, Scope = Scope0 ).

% the term T with the bound variables of the Scope renamed; there are none outside a quantifier
renamed(Scope, T, T) :- empty_assoc(Scope), !.
renamed(_, T, T) :- \+ compound(T), !.
renamed(Scope, T, V) :- T = '$BOUND'(_), !, ( get_assoc(T, Scope, V) -> true ; V = T ).
renamed(Scope, T0, T) :- T0 =.. [F|As0], maplist(renamed(Scope), As0, As), T =.. [F|As].

% the binders are named innermost first: a variable is bound in a fresh instance, a binder already
% named B (as in a canonical formula) is kept, and otherwise substituted
bound([], G, H, H, [], G).
bound([X:S|Bs0], G0, H0, H, [B:S|Bs], G) :-
  bound(Bs0, G0, H0, H1, Bs1, G1),
  B = '$BOUND'(H1),
  H is H1 + 1,
  (   var(X) -> X = B, Bs = Bs1, G = G1
  ;   X == B -> Bs = Bs1, G = G1
  ;   substitute(X, B, Bs1-G1, Bs-G)
  ).
