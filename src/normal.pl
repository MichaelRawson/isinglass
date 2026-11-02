/*
Normal forms of formulas: keys to compare the parent and the conclusion of a preprocessing step
(transform.pl), approximately, so that small differences in how a prover implements it do not matter.

  normal(Mode, F, K)

K is a ground key for the formula F, which is canonical (logic.pl). Formulas with the same key are
equivalent. Mode is the transformation that the step performs, and decides what the key forgets:

  base         names of bound variables, ~~, F => G as ~F | G, nesting of & and |, the units $true
               of & and $false of |, the order of operands, the orientation of equations, vacuous
               binders, and how quantifiers are grouped
  ennf         as base, and negation is pushed to the atoms, but for that of <=>
  nnf          as ennf, and <=> is expanded
  simplify     as base, and $true and $false are simplified away
  pure(Ss)     as simplify, with the atoms of a predicate N/A replaced by V, for each N/A-V in Ss
  skolem(Ss)   as ennf, and Skolemisation is forgotten: bound variables and the terms of the
               Skolem symbols Ss are all '$skolem' (a ? of the parent is a ! of its complement, so
               the variables of both are)

The key of F & G is and(Ks), and of F | G or(Ks), where Ks are the keys of the operands, flattened,
sorted and without duplicates.
*/
:- module(normal, [normal/3]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).

% the formula is first reshaped, then its bound variables are named again (as binders may have gone),
% and then its operands are ordered
normal(Mode, F, K) :-
  shape(Mode, F, F1),
  canonical(F1, F2),
  key(F2, K).

pushes(ennf).
pushes(nnf).
pushes(skolem(_)).

simplifies(simplify).
simplifies(pure(_)).

shape(_, '$true', '$true') :- !.
shape(_, '$false', '$false') :- !.
shape(Mode, ~F, K) :- !, negated(Mode, F, K).
shape(Mode, (F & G), K) :- !, shape(Mode, F, A), shape(Mode, G, B), conjunction(Mode, A, B, K).
shape(Mode, (F | G), K) :- !, shape(Mode, F, A), shape(Mode, G, B), disjunction(Mode, A, B, K).
shape(Mode, (F => G), K) :- !, shape(Mode, (~F | G), K).
shape(nnf, (F <=> G), K) :- !, shape(nnf, ((~F | G) & (F | ~G)), K).
shape(Mode, (F <=> G), K) :- !, shape(Mode, F, A), shape(Mode, G, B), equivalence(Mode, A, B, K).
shape(skolem(Ss), F, K) :- quantified(F, _, Bs, G), !, blurred_binders(Bs, G, G1), shape(skolem(Ss), G1, K).
shape(Mode, F, K) :-
  quantified(F, Q, Bs, G), !,
  opened(Bs, G, Vs, G1),
  shape(Mode, G1, B),
  occurring(Vs, B, Bs1),
  quantify(Q, Bs1, B, K).
shape(pure(Ss), A, V) :- functor(A, N, Arity), memberchk(N/Arity-V, Ss), !.
shape(skolem(Ss), A, K) :- !, blurred(Ss, A, K).
shape(_, A, A).

% the shape of ~F
negated(Mode, ~F, K) :- !, shape(Mode, F, K).
negated(nnf, (F <=> G), K) :- !, shape(nnf, ((F | G) & (~F | ~G)), K).
negated(Mode, F, K) :- pushes(Mode), pushed(F, G), !, shape(Mode, G, K).
negated(Mode, F, K) :- shape(Mode, F, A), negation(Mode, A, K).

pushed('$true', '$false').
pushed('$false', '$true').
pushed((F & G), (~F | ~G)).
pushed((F | G), (~F & ~G)).
pushed((F => G), (F & ~G)).
pushed('!'(Bs, F), '?'(Bs, ~F)).
pushed('?'(Bs, F), '!'(Bs, ~F)).

negation(_, ~A, A) :- !.
negation(Mode, '$true', '$false') :- simplifies(Mode), !.
negation(Mode, '$false', '$true') :- simplifies(Mode), !.
negation(_, A, ~A).

conjunction(_, '$true', B, B) :- !.
conjunction(_, A, '$true', A) :- !.
conjunction(Mode, A, B, '$false') :- simplifies(Mode), ( A == '$false' ; B == '$false' ), !.
conjunction(_, A, B, (A & B)).

disjunction(_, '$false', B, B) :- !.
disjunction(_, A, '$false', A) :- !.
disjunction(Mode, A, B, '$true') :- simplifies(Mode), ( A == '$true' ; B == '$true' ), !.
disjunction(_, A, B, (A | B)).

equivalence(Mode, '$true', B, B) :- simplifies(Mode), !.
equivalence(Mode, A, '$true', A) :- simplifies(Mode), !.
equivalence(Mode, '$false', B, K) :- simplifies(Mode), !, negation(Mode, B, K).
equivalence(Mode, A, '$false', K) :- simplifies(Mode), !, negation(Mode, A, K).
equivalence(_, A, B, (A <=> B)).

quantified(F, Q, Bs, G) :- compound(F), F =.. [Q, Bs, G], ( Q == '!' ; Q == '?' ).

% the binders Bs, bound in G, replaced by fresh variables
opened([], G, [], G).
opened([X:S|Bs], G0, [V:S|Vs], G) :-
  substitute(X, V, Bs-G0, Bs1-G1),
  opened(Bs1, G1, Vs, G).

% the binders Bs, bound in G, replaced by '$skolem'
blurred_binders([], G, G).
blurred_binders([X:_|Bs0], G0, G) :-
  substitute(X, '$skolem', Bs0-G0, Bs-G1),
  blurred_binders(Bs, G1, G).

% the terms of the Skolem symbols Ss in T replaced by '$skolem'
blurred(_, T, T) :- var(T), !.
blurred(Ss, T, '$skolem') :- functor(T, F, _), memberchk(F, Ss), !.
blurred(_, T, T) :- \+ compound(T), !.
blurred(Ss, T0, T) :- T0 =.. [F|As0], maplist(blurred(Ss), As0, As), T =.. [F|As].

% the binders that occur in F
occurring([], _, []).
occurring([V:S|Vs], F, Bs) :- ( occurs(V, F) -> Bs = [V:S|Bs1] ; Bs = Bs1 ), occurring(Vs, F, Bs1).

quantify(_, [], F, F) :- !.
quantify(Q, Bs, F, K) :- K =.. [Q, Bs, F].

% the key of a canonical formula
key((F & G), K) :- !, junction(and, '&', (F & G), K).
key((F | G), K) :- !, junction(or, '|', (F | G), K).
key((F <=> G), iff(Ks)) :- !, key(F, A), key(G, B), ( B @< A -> Ks = [B, A] ; Ks = [A, B] ).
key(~F, ~K) :- !, key(F, K).
key(F, K) :- quantified(F, Q, Bs, G), !, key(G, K0), nested(Q, Bs, K0, K).
key('$='(S, A, B), K) :- !, ( B @< A -> K = '$='(S, B, A) ; K = '$='(S, A, B) ).
key(A, A).

% the operands of nested Op, their keys spliced into one sorted list, which is the key if alone
junction(Name, Op, F, K) :-
  operands(Op, F, Fs, []),
  maplist(key, Fs, Ks0),
  foldl(spliced(Name), Ks0, Ks1, []),
  sort(Ks1, Ks),
  ( Ks = [K] -> true ; K =.. [Name, Ks] ).

operands(Op, F, Fs0, Fs) :- compound(F), F =.. [Op, G, H], !, operands(Op, G, Fs0, Fs1), operands(Op, H, Fs1, Fs).
operands(_, F, [F|Fs], Fs).

spliced(Name, K, Ks0, Ks) :- ( K =.. [Name, Ls] -> append(Ls, Ks, Ks0) ; Ks0 = [K|Ks] ).

% one binder per quantifier
nested(_, [], K, K).
nested(Q, [B|Bs], K0, K) :- nested(Q, Bs, K0, K1), K =.. [Q, [B], K1].
