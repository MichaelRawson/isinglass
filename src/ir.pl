/*
The intermediate representation (IR) of proofs, and its checker.

  ir_step(Name, Conclusion, Justification)        (db.pl)

  Conclusion    ::= clause(Xs, Literals) | formula(F)
  Justification ::= input(Role, Source)
                  | split_def(Symbol, Clause)       Symbol is defined as Clause (AVATAR)
                  | proof(M)                        M is a proof term of the conclusion clause
                  | todo(Record, Parents)           not (yet) reconstructed

Proofs are λ-terms, Curry-Howard style, in minimal logic: no particular logic is fixed, and
⊥ ('$false') is abstract. Classically it is falsity, but in the A-translation it is the conjecture G.
Types are formulas, where ~F is F → ⊥ and F => G is implication:

  clause(Xs, [L_0, ..., L_n-1])  has type  '!'(Xs, ~L_0 => ... => ~L_n-1 => '$false')

So the hypothesis for a negative literal ~A is ~~A, and ¬¬-elimination is never needed.
A split symbol is a defined proposition: it unfolds to the type of its defining clause.

  M ::= X                 a hypothesis h(N)
      | app(F, Ts, Ms)    F applied to first-order terms Ts, then to proofs Ms
      | lam(X, T, M)      X : T is h(N) for a proof, or an eigenvariable '$VAR'(N) : '$i' for an individual
      | let(X, F, M, M')  X : F is M, in M' (a lemma)
  F ::= X | Name          a hypothesis, or a step
      | '$sym'            built-in: '!'([X, Y], X = Y => Y = X)

Heads are always variables or constants, so terms are β-normal but for let.

Search produces the same terms, with Prolog variables for binder types (see reconstruct.pl).
elaborate/2 type-checks a term bidirectionally, instantiating these annotations from the expected
types of λs as it goes. Annotations are only ever unified with ground types, so an annotation
that is already present is checked; once elaborated, a term is ground.
*/
:- module(ir, [elaborate/2]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% M is a closed proof of the conclusion clause, and its binder types are filled in
elaborate(Conclusion, M) :-
  clause_type(Conclusion, T),
  empty_assoc(Gamma),
  check(Gamma, M, T).

% Gamma is an assoc mapping hypotheses to their types, and eigenvariables to '$i'
check(Gamma, lam(X, A, M), T0) :- !,
  unfold(T0, T),
  (   T = '!'([Y|Ys], B)
  ->  X = '$VAR'(_),
      \+ occurs(X, Gamma),
      X = Y,
      A = '$i',
      ( Ys == [] -> T1 = B ; T1 = '!'(Ys, B) ),
      put_assoc(X, Gamma, A, Gamma1),
      check(Gamma1, M, T1)
  ;   T = (A => B),
      ground(A),
      nonvar(X), X = h(_),
      put_assoc(X, Gamma, A, Gamma1),
      check(Gamma1, M, B)
  ).
check(Gamma, let(X, F, M, M1), T) :- !,
  check(Gamma, M, F),
  nonvar(X), X = h(_),
  put_assoc(X, Gamma, F, Gamma1),
  check(Gamma1, M1, T).
check(Gamma, M, T) :-
  infer(Gamma, M, T1),
  T1 == T.

infer(Gamma, app(F, Ts, Ms), T) :- !,
  head(Gamma, F, T0),
  ground(Ts),
  instantiate(Ts, T0, T1),
  arguments(Ms, Gamma, T1, T).
infer(Gamma, X, T) :- head(Gamma, X, T).

% the type of a head: steps, split definitions and built-ins are fresh instances
head(Gamma, X, T) :- nonvar(X), X = h(_), !, get_assoc(X, Gamma, T).
head(_, Name, T) :- atom(Name), builtin(Name, T), !.
head(_, Name, T) :- atom(Name), step(Name, Clause, _), Clause = clause(_, _), clause_type(Clause, T).

builtin('$sym', '!'([X, Y], ((X = Y) => (Y = X)))).

instantiate([], T, T) :- !.
instantiate(Ts, T0, T) :- unfold(T0, '!'(Ts, T)).

arguments([], _, T, T).
arguments([M|Ms], Gamma, T0, T) :-
  unfold(T0, (A => B)),
  check(Gamma, M, A),
  arguments(Ms, Gamma, B, T).

% weak head normal form: negation is implication, and split symbols are their definitions
unfold(~A, (A => '$false')) :- !.
unfold(S, T) :- atom(S), split_def(S, Clause), !, clause_type(Clause, T).
unfold(T, T).

occurs(X, T) :- X == T, !.
occurs(X, T) :- compound(T), T =.. [_|Ts], member(S, Ts), occurs(X, S), !.
