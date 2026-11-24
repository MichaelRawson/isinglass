% utilities for formulas and clauses in the internal syntax (see ops.pl)
:- module(logic, [
  formula_clause/2,
  quantifier/4,
  quantify/4,
  quantifier_prefix/4,
  quantifier_prefix/5,
  binder_variables/2,
  clause_formula/2,
  disjunction/2,
  complement/2,
  flip/2,
  number_vars/3,
  substitute/4,
  substitute_all/4,
  literal/1,
  signed_atom/4,
  occurs/2,
  subterm/2,
  canonical/2,
  opened/2,
  open_binder/4,
  renamed/3,
  connective/2,
  map_arguments/3
]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).

% F is a quantifier Q ('!' or '?') with one binder B, X : Sort (see load.pl), and body G
quantifier(F, Q, B, G) :- nonvar(F), F =.. [Q, B, G], ( Q == '!' ; Q == '?' ).

% G is F under a quantifier Q for each of the binders Bs, outermost first
quantify(_, [], F, F) :- !.
quantify(Q, [B|Bs], F, G) :- quantify(Q, Bs, F, G1), G =.. [Q, B, G1].

% ...and back again: the binders Bs of the outermost quantifiers Q of G, around F
quantifier_prefix(Q, G, [B|Bs], F) :- nonvar(G), G =.. [Q, B, G1], !, quantifier_prefix(Q, G1, Bs, F).
quantifier_prefix(_, F, [], F).

% ...or of exactly N of them
quantifier_prefix(_, 0, F, [], F) :- !.
quantifier_prefix(Q, N, G, [B|Bs], F) :- nonvar(G), G =.. [Q, B, G1], N1 is N - 1, quantifier_prefix(Q, N1, G1, Bs, F).

% a formula is a clause: clause(Bs, Literals), with quantifier binders Bs
formula_clause(G, C) :- quantifier_prefix('!', G, Bs, F), Bs = [_|_], !, C = clause(Bs, Ls), literals(F, Ls).
% AVATAR clauses are printed as (! [X] : C) | ~split
formula_clause((G | H), C) :- quantifier_prefix('!', G, Bs, F), Bs = [_|_], !, C = clause(Bs, Ls), literals((F | H), Ls).
formula_clause(F, clause([], Ls)) :- literals(F, Ls).

literals('$false', []) :- !.
literals((F | G), Ls) :- !, literals(F, Fs), literals(G, Gs), append(Fs, Gs, Ls).
literals(~A, [~A]) :- !, atomic_formula(A).
literals(A, [A]) :- atomic_formula(A).

% and back again
clause_formula(clause(Bs, Ls), G) :- disjunction(Ls, F), quantify('!', Bs, F, G).

% the variables of quantifier binders X : Sort
binder_variables(Bs, Xs) :- maplist(binder_variable, Bs, Xs).

binder_variable(X:_, X).

disjunction([], '$false').
disjunction([L], L) :- !.
disjunction([L|Ls], (L | F)) :- disjunction(Ls, F).

atomic_formula(A) :- nonvar(A), \+ connective(A, _).

literal(~A) :- !, atomic_formula(A).
literal(A) :- atomic_formula(A).

% an atom A of F, and its sign S (pos or neg), where F has the sign S0; an atom under <=> has both
signed_atom(~F, S0, A, S) :- !, opposite(S0, S1), signed_atom(F, S1, A, S).
signed_atom((F => G), S0, A, S) :- !, ( opposite(S0, S1), signed_atom(F, S1, A, S) ; signed_atom(G, S0, A, S) ).
signed_atom((F <=> G), _, A, S) :- !, member(S1, [pos, neg]), ( signed_atom(F, S1, A, S) ; signed_atom(G, S1, A, S) ).
signed_atom(F, S0, A, S) :- connective(F, Gs), !, member(G, Gs), signed_atom(G, S0, A, S).
signed_atom(A, S, A, S).

opposite(pos, neg).
opposite(neg, pos).

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

% T is T0 with each argument mapped by P
:- meta_predicate(map_arguments(2, ?, ?)).
map_arguments(P, T0, T) :- T0 =.. [F|As0], maplist(P, As0, As), T =.. [F|As].

% B is A with every occurrence of the term X replaced by S
substitute(X, S, A, B) :- A == X, !, B = S.
substitute(_, _, A, B) :- \+ compound(A), !, B = A.
substitute(X, S, A, B) :- map_arguments(substitute(X, S), A, B).

% B is A with the terms Xs replaced by the terms Ts at once, so that none of Ts is substituted again
substitute_all(Xs, Ts, A, B) :- foldl(substitute_fresh, Xs, Vs, A, B), Vs = Ts.

substitute_fresh(X, V, A, B) :- substitute(X, V, A, B).

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
  quantifier(F0, Q, X:S, G0), !,
  canonical(G0, G1, H0),
  bound(X, G1, H0, B, G),
  H is H0 + 1,
  F =.. [Q, B:S, G].
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
  quantifier(F0, Q, B0, G0), !,
  open_binder(B0, B, Scope0, Scope),
  opened(G0, Scope, G),
  F =.. [Q, B, G].
opened(F0, Scope, F) :-
  nonvar(F0),
  connective(F0, _), !,
  map_arguments(opened_in(Scope), F0, F).
opened(A0, Scope, A) :- renamed(Scope, A0, A).

opened_in(Scope, F0, F) :- opened(F0, Scope, F).

% the binder with a fresh variable, added to the Scope; its sort may name binders around it (TF1)
open_binder(X:S0, V:S, Scope0, Scope) :-
  renamed(Scope0, S0, S),
  ( nonvar(X), X = '$BOUND'(_) -> put_assoc(X, Scope0, V, Scope) ; V = X, Scope = Scope0 ).

% the term T with the bound variables of the Scope renamed; there are none outside a quantifier
renamed(Scope, T, T) :- empty_assoc(Scope), !.
renamed(_, T, T) :- \+ compound(T), !.
renamed(Scope, T, V) :- T = '$BOUND'(_), !, ( get_assoc(T, Scope, V) -> true ; V = T ).
renamed(Scope, T0, T) :- map_arguments(renamed(Scope), T0, T).

% the binder X of the body G0, in which H binders are nested, is named B: a variable is bound in a
% fresh instance, a binder already named B (as in a canonical formula) is kept, and otherwise
% substituted
bound(X, G0, H, B, G) :-
  B = '$BOUND'(H),
  (   var(X) -> X = B, G = G0
  ;   X == B -> G = G0
  ;   substitute(X, B, G0, G)
  ).
