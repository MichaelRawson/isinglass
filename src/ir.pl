/*
The intermediate representation (IR) of proofs, and the types of clauses.

  ir_step(Name, Conclusion, Justification)        (db.pl), checked by checker.pl

  Conclusion    ::= clause(Bs, Literals) | formula(F)
  Justification ::= input(Role, Source)             an axiom (never the conjecture)
                  | split_def(Symbol, Clause)       Symbol is defined as Clause (AVATAR)
                  | skolem_def(Symbol, Bs, F)       Symbol(Xs), for the binders Bs = Xs : Sorts, is
                                                    defined by choice, as ε Y. T, where F is a δ formula
                                                    ?[Y:S|Ys] : G (T is ?[Ys] : G) or ~![Y:S|Ys] : G
                                                    (T is ~![Ys] : G); its conclusion is the choice axiom
                                                    ![Bs] : (F => T[Symbol(Xs)/Y]) (choice_axiom/4)
                  | definition(Symbol, Bs, Body)    Symbol(Xs) is defined as Body, for the binders
                                                    Bs = Xs : Sorts; for a function symbol, Body is a
                                                    term, and the conclusion is the unit clause
                                                    [Symbol(Xs) = Body], either way round; for a
                                                    predicate, Body is a formula, and the conclusion is
                                                    ![Bs] : (Symbol(Xs) <=> Body)
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
  formula(F)                     has type  F

where the binders Bs are X : Sort, as in quantifiers; the literals contain the variables X.
The bound variables of a formula are named canonically, '$BOUND'(H) (see logic.pl), so that types
are compared syntactically.

So the hypothesis for a negative literal ~A is ~~A, and ¬¬-elimination is never needed.
A split symbol is a defined proposition: it unfolds to the type of its defining clause.
A defined predicate unfolds to its body, so a formula is also of any type that differs from it only by
unfolding defined atoms (expanded/2): a proof uses this only at a let, which states the unfolded type.

  M ::= X                 a hypothesis h(N)
      | app(F, Ts, Ms)    F applied to first-order terms Ts, then to proofs Ms
      | lam(X, T, M)      X : T is h(N) for a proof, or an eigenvariable '$VAR'(N) : Sort; T is
                          '$inferred' for a hypothesis of an expansion rule, whose type follows
                          from the rule's first argument
      | let(X, F, M, M')  X : F is M, in M' (a lemma)
      | rewrite(X:S, A, E, M)
                          E : S = T and M : A[X:=S] give A[X:=T], where X is an eigenvariable
                          '$VAR'(N) of sort S bound only in the motive A, and E's type is
                          inferred (a hypothesis or an application)
  F ::= X | Name          a hypothesis, or a step: a clause or a formula
      | '$sym'            built-in: '!'([A:'$tType', X:A, Y:A], '$='(A, X, Y) => '$='(A, Y, X))
      | '$refl'           built-in: '!'([A:'$tType', X:A], '$='(A, X, X))
      | '$trivial'        built-in: '$true'
      | '$dne'            built-in: '!'([F:'$o'], ~ ~F => F), classical
      | Rule              an expansion rule (transform.pl), below

A hypothesis of type '!'(Bs, F) is applied to terms, as a step is. An expansion rule is applied to
a proof of a formula, whose type is inferred as for E above, and then to a refutation of each
branch, which binds the formulas of the branch, and first an eigenvariable for ? and ~!:

  '$and'   F & G        F, G              '$nor'   ~(F | G)     ~F, ~G
  '$or'    F | G        F ; G             '$nand'  ~(F & G)     ~F ; ~G
  '$imp'   F => G       ~F ; G            '$nimp'  ~(F => G)    F, ~G
  '$iff'   F <=> G      F, G ; ~F, ~G     '$niff'  ~(F <=> G)   F, ~G ; ~F, G
  '$ex'    ?[X] : F     F                 '$nall'  ~ ![X] : F   ~F

'$nex' is not a refutation: applied to a proof of ~ ?[Xs] : F it proves ![Xs] : ~F.
Skolemisation is not a rule: a δ formula is opened by its choice axiom, a step (skolem_def).
'$nimp', '$niff', '$nall' and '$dne' are not valid in minimal logic, so the steps that use them
are classical; a formula conclusion F is proved by '$dne', from a refutation of ~F.

Heads are always variables or constants, so terms are β-normal but for let.
The outermost ~ of the negated conjecture is the refutation's ⊥. A classical back end proves the
conjecture G by ¬¬-elimination; the A-translation takes ⊥ to be G, and the hypothesis ~G to be the
identity, so that the conjecture is the refutation itself. Only steps between formulas
(preprocessing and clausification) are otherwise classical.

Equations are typed, as '$='(A, S, T) with A the sort of S and T. Sorts are terms of sort '$tType'
(see signature.pl), and type variables are binders X : '$tType', as in TF1.

First-order terms Ts are built from the signature, eigenvariables '$VAR'(N), and '$inhabited'(S),
an arbitrary individual of sort S for a variable that search left unconstrained, where no such term
of sort S was found; S is '$tType' for a type variable (see close.pl).
*/
:- module(ir, [clause_type/2, step_type/2, reference/2, builtin_type/2, rule_type/3, formula_step/1, choice_axiom/4,
  defined_atom/2, expanded/2]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(db).
:- use_module(logic).

% the type of proofs of a clause: '!'(Bs, ~L_0 => ... => ~L_n-1 => '$false')
clause_type(clause(Bs, Ls), T) :-
  implications(Ls, F),
  ( Bs == [] -> T = F ; T = '!'(Bs, F) ).

implications([], '$false').
implications([L|Ls], (~L => F)) :- implications(Ls, F).

% the type of a step: that of its clause, or its formula
step_type(clause(Bs, Ls), T) :- clause_type(clause(Bs, Ls), T).
step_type(formula(F), F).

% a step between formulas, preprocessing or clausification (transform.pl): its proof uses the
% expansion rules, and its parent as a formula, or as the type of its clause
formula_step(Name) :-
  step(Name, _, tactic(Tactic, _)),
  ( Tactic = transform(_) ; Tactic == clausify ), !.

% the types of the built-in heads
builtin_type('$sym', '!'([A:'$tType', X:A, Y:A], ('$='(A, X, Y) => '$='(A, Y, X)))).
builtin_type('$refl', '!'([A:'$tType', X:A], '$='(A, X, X))).
builtin_type('$trivial', '$true').
builtin_type('$dne', '!'([F:'$o'], (~(~F) => F))).

% the expansion rules: rule_type(Rule, T, T1), where the rule applied to a proof of T is of type
% T1, which takes a refutation of each branch, but for '$nex'
rule_type('$and', (F & G), ((F => (G => '$false')) => '$false')).
rule_type('$or', (F | G), ((F => '$false') => ((G => '$false') => '$false'))).
rule_type('$imp', (F => G), ((~F => '$false') => ((G => '$false') => '$false'))).
rule_type('$iff', (F <=> G), ((F => (G => '$false')) => ((~F => (~G => '$false')) => '$false'))).
rule_type('$nand', ~((F & G)), ((~F => '$false') => ((~G => '$false') => '$false'))).
rule_type('$nor', ~((F | G)), ((~F => (~G => '$false')) => '$false')).
rule_type('$nimp', ~((F => G)), ((F => (~G => '$false')) => '$false')).
rule_type('$niff', ~((F <=> G)), ((F => (~G => '$false')) => ((~F => (G => '$false')) => '$false'))).
rule_type('$ex', '?'([B|Bs], F), ('!'([B], (G => '$false')) => '$false')) :- quantified('?', Bs, F, G).
rule_type('$nall', ~'!'([B|Bs], F), ('!'([B], (~G => '$false')) => '$false')) :- quantified('!', Bs, F, G).
rule_type('$nex', ~'?'(Bs, F), '!'(Bs, ~F)).

% the choice axiom of Symbol, defined for binders Bs as ε Y. T, where T is the body of the δ formula F
choice_axiom(Symbol, Bs, F, A) :-
  ( Rule = '$ex' ; Rule = '$nall' ),
  rule_type(Rule, F, ('!'([Y:_], (T => '$false')) => '$false')), !,
  binder_variables(Bs, Xs),
  Term =.. [Symbol|Xs],
  substitute(Y, Term, T, T1),
  quantified('!', Bs, (F => T1), A).

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

% the canonical formula F0 with each defined atom unfolded, throughout (definitions are not circular)
expanded(F0, F) :- opened(F0, F1), unfolded(F1, F2), canonical(F2, F).

% the bound variables of a canonical formula as Prolog variables: the names on a path are distinct
opened(F0, F) :-
  compound(F0),
  F0 =.. [Q, Bs0, G0],
  ( Q == '!' ; Q == '?' ), !,
  foldl(open_binder, Bs0, Bs, Bs0-G0, _-G1),
  opened(G1, G),
  F =.. [Q, Bs, G].
opened(F0, F) :- connective(F0, _), !, F0 =.. [C|Gs0], maplist(opened, Gs0, Gs), F =.. [C|Gs].
opened(A, A).

open_binder(X:S, V:S, Bs0-G0, Bs-G) :- substitute(X, V, Bs0-G0, Bs-G).

unfolded(F0, F) :-
  compound(F0),
  F0 =.. [Q, Bs, G0],
  ( Q == '!' ; Q == '?' ), !,
  unfolded(G0, G),
  F =.. [Q, Bs, G].
unfolded(F0, F) :- connective(F0, _), !, F0 =.. [C|Gs0], maplist(unfolded, Gs0, Gs), F =.. [C|Gs].
unfolded(A, F) :- defined_atom(A, Body0), !, opened(Body0, Body), unfolded(Body, F).
unfolded(A, A).

% a quantifier over binders Bs, if any
quantified(_, [], F, F) :- !.
quantified(Q, Bs, F, G) :- G =.. [Q, Bs, F].

% a step that a justification cites, one at a time
reference(proof(M), Name) :- head(M, Name).
reference(todo(_, Parents), Name) :- member(Name, Parents).
reference(conjecture(_, Negated, Refutation), Name) :- ( Name = Negated ; Name = Refutation ).

% a step at the head of an application in a proof term
head(lam(_, _, M), Name) :- head(M, Name).
head(let(_, _, M, N), Name) :- ( head(M, Name) ; head(N, Name) ).
head(rewrite(_, _, E, M), Name) :- ( head(E, Name) ; head(M, Name) ).
head(app(F, _, _), F) :- atom(F), \+ builtin_type(F, _), \+ rule_type(F, _, _).
head(app(_, _, Ms), Name) :- member(M, Ms), head(M, Name).
