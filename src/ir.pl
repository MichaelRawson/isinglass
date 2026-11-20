/*
The intermediate representation (IR) of proofs.

Each IR step is kept as a record (db.pl):
   ir_step(Name, Conclusion, Justification)

where a conclusion is either a clause or a formula.

  Conclusion    ::= clause(Bs, Literals) | formula(F)

Each is justified by one of a few kinds of records.

  Justification ::= input(Role, Source)
                  | negated_conjecture(Conjecture)
                  | conjecture(Source, Negated, Refutation)
                  | definition(Symbol, Bs, Body)
                  | skolem_def(Symbol, Bs, F)
                  | proof(M)
                  | todo(Record, Parents)

`input` is an axiom provided by the user and reported by the ATP.
`negated_conjecture` is the negated conjecture: it will be discharged by `conjecture`.
`definition` introduces a definition for a term, clause or formula.
`skolem_def` introduces a Skolem: the conclusion is a choice axiom.
`proof` justifies a step by deduction with a proof term `M`.
Finally, `todo` indicates that a step is yet to be reconstructed.

Throughout, binders B are a variable X and a sort S.

The internal logic is a typed λ-calculus.
Formulas are also types, where ~F is F → ⊥ and F => G is implication:

  clause([B_0, ..., B_m-1], [L_0, ..., L_n-1])
                 has type  '!'(B_0, ... '!'(B_m-1, ~L_0 => ... => ~L_n-1 => '$false'))
  formula(F)     has type  F

The bound variables of a formula are named canonically, '$BOUND'(H) (see logic.pl), so that types are compared syntactically.

Proofs are terms M, Curry-Howard style, in minimal logic: no particular logic is fixed, and ⊥ ('$false') is abstract.

  M ::= X
      | app(F, Ts, Ms)    F applied to first-order terms Ts, then to proofs Ms
      | lam(X, T, M)      X : T is h(N) for a proof, or an eigenvariable '$VAR'(N) : Sort; T is
                          '$inferred' for a hypothesis of an expansion rule, whose type follows
                          from the type of the rule's first argument
      | rewrite(X:S, A, E, M)
                          E : S = T and M : A[X:=S] give A[X:=T], where X is an eigenvariable
                          '$VAR'(N) of sort S bound only in the motive A, and E's type is
                          inferred (not a λ)
  F ::= M                 any term: a hypothesis, or
      | Name              a step: a clause or a formula, or
      | Builtin           a built-in, typed by head_type/2

The λ of a redex states the types of its hypotheses, so none are '$inferred'.

A head of type '!'(X:S, T) is applied to a term of sort S for X.
A built-in (presently) takes no terms: its type variables are inferred by unification.
Builtins '$nimp', '$niff', '$nall' and '$dne' are not valid in minimal logic, so steps that use them are classical.

The outermost ~ of the negated conjecture is the refutation's ⊥. A classical back end proves the
conjecture G by ¬¬-elimination; the A-translation takes ⊥ to be G, and the hypothesis ~G to be the
identity, so that the conjecture is the refutation itself. Only steps between formulas
(preprocessing and clausification) are otherwise classical.

Equations are typed, as '$='(A, S, T) with A the sort of S and T.
Sorts are terms of sort '$tType' (signature.pl), and type variables are binders X : '$tType', as in TF1.

First-order terms Ts are built from the signature, variables '$VAR'(N), and '$inhabited'(S), which asserts that `S` is inhabited.
*/
:- module(ir, [clause_type/2, step_type/2, reference/2, cited_steps/1, head_type/2, inferred_premise/1, rule_branches/3, formula_step/1, choice_axiom/4,
  defined_atom/2, defined_term/2, expanded/2, terms_unfolded/2, typed_clause/2]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(db).
:- use_module(logic).

% the type of proofs of a clause: ~L_0 => ... => ~L_n-1 => '$false', under a '!' for each binder
clause_type(clause(Bs, Ls), T) :-
  implications(Ls, F),
  quantify('!', Bs, F, T).

implications([], '$false').
implications([L|Ls], (~L => F)) :- implications(Ls, F).

% the clause of a canonical clause type T, with Prolog variables for its binders
typed_clause(T0, clause(Bs, Ls)) :-
  opened(T0, T),
  quantifier_prefix('!', T, Bs, F),
  implications(Ls, F).

% the type of a step: that of its clause, or its formula
step_type(clause(Bs, Ls), T) :- clause_type(clause(Bs, Ls), T).
step_type(formula(F), F).

% a step between formulas, preprocessing or clausification (transform.pl): its proof uses the
% expansion rules, and its parent as a formula, or as the type of its clause
formula_step(Name) :-
  step(Name, _, tactic(Tactic, _)),
  ( Tactic = transform(_) ; Tactic == clausify ), !.

% the types of the built-ins, fresh instances: their Prolog variables are their parameters, the terms
% of an application for those bound by '!', and otherwise inferred (see above)
head_type('$trivial', '$true').
head_type('$refl', '$='(_, X, X)).
head_type('$sym', ('$='(A, X, Y) => '$='(A, Y, X))).
head_type('$dne', (~(~F) => F)).
% the expansion rules: each takes a proof of a formula, and a refutation of each branch
head_type('$and', ((F & G) => ((F => (G => '$false')) => '$false'))).
head_type('$or', ((F | G) => ((F => '$false') => ((G => '$false') => '$false')))).
head_type('$imp', ((F => G) => ((~F => '$false') => ((G => '$false') => '$false')))).
head_type('$iff', ((F <=> G) => ((F => (G => '$false')) => ((~F => (~G => '$false')) => '$false')))).
head_type('$nand', (~(F & G) => ((~F => '$false') => ((~G => '$false') => '$false')))).
head_type('$nor', (~(F | G) => ((~F => (~G => '$false')) => '$false'))).
head_type('$nimp', (~(F => G) => ((F => (~G => '$false')) => '$false'))).
head_type('$niff', (~(F <=> G) => ((F => (~G => '$false')) => ((~F => (G => '$false')) => '$false')))).
head_type('$ex', ('?'(B, F) => ('!'(B, (F => '$false')) => '$false'))).
head_type('$nall', (~'!'(B, F) => ('!'(B, (~F => '$false')) => '$false'))).
head_type('$nex', (~'?'(B, F) => (('!'(B, ~F) => '$false') => '$false'))).

% a built-in whose first premise has parameters, which the type of its first argument may bind:
% '$sym', '$dne', and the expansion rules
inferred_premise(Name) :- head_type(Name, (A => _)), \+ ground(A).

% the Branches of the expansion Rule applied to a proof of the formula F, each the formulas that it
% binds, as read off its type: a refutation of each branch, H_1 => ... => '$false', and then
% '$false'. The rules of quantifiers bind an eigenvariable first, so they have none
rule_branches(F, Rule, Branches) :- nonvar(F), head_type(Rule, (F => T)), refutations(T, Branches), !.

refutations('$false', []).
refutations((K => T), [Hs|Branches]) :- hypotheses(K, Hs), refutations(T, Branches).

hypotheses('$false', []).
hypotheses((H => K), [H|Hs]) :- hypotheses(K, Hs).

% the choice axiom of Symbol, defined for binders Bs as ε Y. T, where F is ?[Y:S] : T
choice_axiom(Symbol, Bs, F, A) :-
  F = '?'(Y:_, T),
  binder_variables(Bs, Xs),
  Term =.. [Symbol|Xs],
  substitute(Y, Term, T, T1),
  quantify('!', Bs, (F => T1), A).

% the atom A of a defined predicate unfolds to Body, the definition's body for the arguments of A
defined_atom(A, Body) :-
  compound(A),
  A =.. [P|Ts],
  ir_step(_, formula(_), definition(P, Bs, Body0)),
  binder_variables(Bs, Xs),
  foldl(abstract, Xs, Vs, Body0, Body),
  Vs = Ts.
defined_atom(A, Body) :-
  atom(A),
  ir_step(_, formula(_), definition(A, [], Body)).

abstract(X, V, F0, F) :- substitute(X, V, F0, F).

% the canonical formula F0 with each defined atom and term unfolded, throughout (definitions are not
% circular)
expanded(F0, F) :- opened(F0, F1), unfolded(F1, F2), ( F2 == F1 -> F = F0 ; canonical(F2, F) ).

unfolded(F0, F) :- quantifier(F0, Q, B, G0), !, unfolded(G0, G), F =.. [Q, B, G].
unfolded(F0, F) :- connective(F0, _), !, F0 =.. [C|Gs0], maplist(unfolded, Gs0, Gs), F =.. [C|Gs].
unfolded(A0, F) :-
  unfolded_arguments(A0, A),
  ( defined_atom(A, Body0) -> opened(Body0, Body), unfolded(Body, F) ; F = A ).

unfolded_arguments(A0, A) :- compound(A0), !, A0 =.. [P|Ts0], maplist(unfolded_term, Ts0, Ts), A =.. [P|Ts].
unfolded_arguments(A, A).

% a quantifier-free formula with each defined function term unfolded, but not its defined atoms
terms_unfolded(F0, F) :- connective(F0, _), !, F0 =.. [C|Gs0], maplist(terms_unfolded, Gs0, Gs), F =.. [C|Gs].
terms_unfolded(A0, A) :- unfolded_arguments(A0, A).

% a term with each defined function term unfolded, outermost first
unfolded_term(T, T) :- var(T), !.
unfolded_term(T0, T) :- defined_term(T0, T1), !, unfolded_term(T1, T).
unfolded_term(T0, T) :- unfolded_arguments(T0, T).

% the term T of a defined function symbol unfolds to Body, the definition's body for its arguments
defined_term(T, Body) :-
  functor(T, F, N),
  introduced(F, definition),
  ir_step(_, clause(_, _), definition(F, Bs, Body0)),
  length(Bs, N), !,
  T =.. [F|Ts],
  binder_variables(Bs, Xs),
  foldl(abstract, Xs, Vs, Body0, Body),
  Vs = Ts.

% a step that a justification cites, one at a time
reference(proof(M), Name) :- head(M, Name).
reference(todo(_, Parents), Name) :- member(Name, Parents).
reference(conjecture(_, Negated, Refutation), Name) :- ( Name = Negated ; Name = Refutation ).

% the steps that some step cites, as an assoc
cited_steps(Cited) :-
  findall(Name-true, ( ir_step(_, _, J), reference(J, Name) ), Pairs0),
  sort(Pairs0, Pairs),
  list_to_assoc(Pairs, Cited).

% a step at the head of an application in a proof term
head(lam(_, _, M), Name) :- head(M, Name).
head(rewrite(_, _, E, M), Name) :- ( head(E, Name) ; head(M, Name) ).
head(app(F, _, _), F) :- atom(F), \+ head_type(F, _).
head(app(F, _, _), Name) :- compound(F), head(F, Name).
head(app(_, _, Ms), Name) :- member(M, Ms), head(M, Name).
