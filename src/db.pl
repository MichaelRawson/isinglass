% the shared database: written by the front end and reconstruction, read by back ends
:- module(db, [step/3, symbol/3, introduced/2, ir_step/3, split/2]).

% step(Name, Conclusion, How): a proof step, as understood by a front end
% Conclusion is clause(Xs, Literals) or formula(F), with Prolog variables:
% each retrieval is a fresh instance
% How is input(Role, Source), split_def(Symbol, Clause), tactic(Procedure, Parents) or todo(Record, Parents)
:- dynamic(step/3).

% symbol(Name, ArgumentSorts, Sort): signature, with sorts '$i' and '$o' by default
:- dynamic(symbol/3).

% introduced(Name, Kind): symbol introduced by the prover (e.g. naming, skolem)
:- dynamic(introduced/2).

/*
ir_step(Name, Conclusion, Justification): the intermediate representation (IR) of proofs, as
reconstructed steps in dependency order. Steps are ground: variables are numbered as '$VAR'(N),
in binder order. checker.pl type-checks them.

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
:- dynamic(ir_step/3).

% split(Symbol, Clause): AVATAR split definitions, indexed by symbol, with Prolog variables
:- dynamic(split/2).
