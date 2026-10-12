/*
The intermediate representation (IR) of proofs, and the types of clauses.

  ir_step(Name, Conclusion, Justification)        (db.pl), checked by checker.pl

  Conclusion    ::= clause(Bs, Literals) | formula(F)
  Justification ::= input(Role, Source)             an axiom (never the conjecture)
                  | split_def(Symbol, Clause)       Symbol is defined as Clause (AVATAR)
                  | proof(M)                        M is a proof term of the conclusion clause
                  | negated_conjecture(Conjecture)  the hypothesis ~G, discharged by Conjecture
                  | conjecture(Source, Negated, Refutation)
                                                    G, as Refutation refutes the hypothesis Negated:
                                                    by contradiction, the last step
                  | todo(Record, Parents)           not (yet) reconstructed: Record is a Rule for an
                                                    entailment, or esa(Rule, Symbols) if it only
                                                    preserves satisfiability, introducing Symbols

Proofs are λ-terms, Curry-Howard style, in minimal logic: no particular logic is fixed, and
⊥ ('$false') is abstract. Classically it is falsity, but in the A-translation it is the conjecture G.
Types are formulas, where ~F is F → ⊥ and F => G is implication:

  clause(Bs, [L_0, ..., L_n-1])  has type  '!'(Bs, ~L_0 => ... => ~L_n-1 => '$false')

where the binders Bs are X : Sort, as in quantifiers; the literals contain the variables X.

So the hypothesis for a negative literal ~A is ~~A, and ¬¬-elimination is never needed.
A split symbol is a defined proposition: it unfolds to the type of its defining clause.

  M ::= X                 a hypothesis h(N)
      | app(F, Ts, Ms)    F applied to first-order terms Ts, then to proofs Ms
      | lam(X, T, M)      X : T is h(N) for a proof, or an eigenvariable '$VAR'(N) : Sort
      | let(X, F, M, M')  X : F is M, in M' (a lemma)
      | rewrite(X:S, A, E, M)
                          E : S = T and M : A[X:=S] give A[X:=T], where X is an eigenvariable
                          '$VAR'(N) of sort S bound only in the motive A, and E's type is
                          inferred (a hypothesis or an application)
  F ::= X | Name          a hypothesis, or a step: a clause, or the negated conjecture
      | '$sym'            built-in: '!'([A:'$tType', X:A, Y:A], '$='(A, X, Y) => '$='(A, Y, X))
      | '$refl'           built-in: '!'([A:'$tType', X:A], '$='(A, X, X))

Heads are always variables or constants, so terms are β-normal but for let.
A formula(F) conclusion is an object-level formula, so its type is F, but for the negated
conjecture: its outermost ~ is the refutation's ⊥. A classical back end proves the conjecture G by
¬¬-elimination; the A-translation takes ⊥ to be G, and the hypothesis ~G to be the identity, so
that the conjecture is the refutation itself. Only clausification (todo) is otherwise classical.

Equations are typed, as '$='(A, S, T) with A the sort of S and T. Sorts are terms of sort '$tType'
(see signature.pl), and type variables are binders X : '$tType', as in TF1.

First-order terms Ts are built from the signature, eigenvariables '$VAR'(N), and '$inhabited'(S),
an arbitrary individual of sort S for a variable that search left unconstrained; S is
'$tType' for a type variable (see close.pl).
*/
:- module(ir, [clause_type/2, reference/2, builtin_type/2]).
:- use_module(library(lists)).
:- use_module(ops).

% the type of proofs of a clause: '!'(Bs, ~L_0 => ... => ~L_n-1 => '$false')
clause_type(clause(Bs, Ls), T) :-
  implications(Ls, F),
  ( Bs == [] -> T = F ; T = '!'(Bs, F) ).

implications([], '$false').
implications([L|Ls], (~L => F)) :- implications(Ls, F).

% the types of the built-in heads
builtin_type('$sym', '!'([A:'$tType', X:A, Y:A], ('$='(A, X, Y) => '$='(A, Y, X)))).
builtin_type('$refl', '!'([A:'$tType', X:A], '$='(A, X, X))).

% a step that a justification cites, one at a time
reference(proof(M), Name) :- head(M, Name).
reference(todo(_, Parents), Name) :- member(Name, Parents).
reference(conjecture(_, Negated, Refutation), Name) :- ( Name = Negated ; Name = Refutation ).

% a step at the head of an application in a proof term
head(lam(_, _, M), Name) :- head(M, Name).
head(let(_, _, M, N), Name) :- ( head(M, Name) ; head(N, Name) ).
head(rewrite(_, _, E, M), Name) :- ( head(E, Name) ; head(M, Name) ).
head(app(F, _, _), F) :- atom(F), \+ builtin_type(F, _).
head(app(_, _, Ms), Name) :- member(M, Ms), head(M, Name).
