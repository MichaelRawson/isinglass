/*
The intermediate representation (IR) of proofs, and the types of clauses.

  ir_step(Name, Conclusion, Justification)        (db.pl), checked by checker.pl

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
*/
:- module(ir, [clause_type/2]).
:- use_module(ops).

% the type of proofs of a clause: '!'(Xs, ~L_0 => ... => ~L_n-1 => '$false')
clause_type(clause(Xs, Ls), T) :-
  implications(Ls, F),
  ( Xs == [] -> T = F ; T = '!'(Xs, F) ).

implications([], '$false').
implications([L|Ls], (~L => F)) :- implications(Ls, F).
