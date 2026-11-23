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
A type is a sort, of the terms of that sort, or '$proof'(F), of the proofs of the formula F, so the
two are disjoint (as τ and π in Lambdapi). '$proof' is folded: a proof type is taken apart as needed,
'$proof'(F => G) as a function from '$proof'(F) to '$proof'(G), '$proof'(~F) as '$proof'(F => '$false'),
and '$proof'('!'(X:S, F)) as a function from terms X of sort S to '$proof'(F).

  clause([B_0, ..., B_m-1], [L_0, ..., L_n-1])
                 has type  '$proof'('!'(B_0, ... '!'(B_m-1, ~L_0 => ... => ~L_n-1 => '$false')))
  formula(F)     has type  '$proof'(F)

The bound variables of a formula are named canonically, '$BOUND'(H) (see logic.pl), so that types are compared syntactically.

Proofs are terms M, Curry-Howard style, in minimal logic: no particular logic is fixed, and ⊥ ('$false') is abstract.

  M ::= X
      | F
      | '$app'(M, N)            M applied to N: a first-order term, if M is of type
                                '$proof'('!'(X:S, F)), or a proof, if M is of type '$proof'(A => B)
      | '$lam'(X, T, M)         X : T is a variable '$VAR'(N), a hypothesis of type '$proof'(F), or
                                an eigenvariable of a sort; T is '$inferred' for a hypothesis of an
                                expansion rule, whose type follows from the type of the rule's first
                                argument. Its annotation tells the two apart, and the variables of a
                                term are numbered apart
  F ::= Name                    a step: a clause or a formula, named apart from symbols
                                ('$step:f12' or '$def:P', utils:named/3), or
      | Builtin                 a built-in, typed by head_type/2

The constructors of proofs are named with '$', as TPTP reserves such names, so they cannot clash
with a problem's symbols.

The λ of a redex states the types of its hypotheses, so none are '$inferred'.

Application is curried, and its argument is a term or a proof as the type of its function says,
so terms and proofs may come in any order. A term of type '$proof'('!'(X:S, F)) is applied to a term
of sort S for X. In ground IR the two kinds of argument are also told apart by their syntax
(proof_argument/1), but for a variable '$VAR'(N), which the annotation of its λ settles.
A built-in's type variables are inferred by unification. Only '$rewrite' takes a term, its motive,
which unification could not infer (it would be higher-order):

  '$rewrite' : Π (P : S > '$o'). S = T → P S → P T

so '$app'('$app'('$app'('$rewrite', '$abs'(X:S, A)), E), M), for E : S = T and M : A[X:=S], is a
proof of A[X:=T]. E's type is inferred (it is not a λ). The motive '$abs'(X:S, A) is a term of the
arrow sort '$>'(S, '$o') (THF's ^[X:S] : A, of sort S > $o), where X is an eigenvariable '$VAR'(N)
bound only in A, and '$at'(P, T) is its application (THF's @), a formula, β-reduced as soon as P
is a motive (applied_motives/2). Arrow sorts and '$at' occur only in head_type/2, never in a step's
formula, so the logic stays first-order: a motive is a formula with a hole, not a predicate variable.
Builtins '$nimp', '$niff', '$nall' and '$dne' are not valid in minimal logic, so steps that use them are classical.

The outermost ~ of the negated conjecture is the refutation's ⊥. A classical back end proves the
conjecture G by ¬¬-elimination; the A-translation takes ⊥ to be G, and the hypothesis ~G to be the
identity, so that the conjecture is the refutation itself. Only steps between formulas
(preprocessing and clausification) are otherwise classical.

Equations are typed, as '$='(A, S, T) with A the sort of S and T.
Sorts are terms of sort '$tType' (signature.pl), and type variables are binders X : '$tType', as in TF1.

First-order terms Ts are built from the signature, variables '$VAR'(N), and '$inhabited'(S), which asserts that `S` is inhabited.
The one term that is not first-order is the motive of a rewrite, '$abs'(X:S, A), above.
*/
:- module(ir, [clause_type/2, step_type/2, reference/2, cited_steps/1, head_type/2, inferred_premise/1, curried/3, rewrite_parts/4, applied_motives/2, arrow_sort/1, spine/3, proof_argument/1, rule_branches/3, formula_step/1, choice_axiom/4, proof_annotation/1,
  defined_atom/2, defined_term/2, expanded/2, terms_unfolded/2, typed_clause/2]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(db).
:- use_module(logic).
:- use_module(utils).

% the formula of a clause, whose proofs are of type '$proof' of it (step_type/2):
% ~L_0 => ... => ~L_n-1 => '$false', under a '!' for each binder
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
step_type(clause(Bs, Ls), '$proof'(T)) :- clause_type(clause(Bs, Ls), T).
step_type(formula(F), '$proof'(F)).

% the annotation of a λ that binds a hypothesis, rather than an eigenvariable: a proof type, or
% '$inferred' (see above)
proof_annotation(A) :- ( nonvar(A), A = '$proof'(_) -> true ; A == '$inferred' ).

% a step between formulas, preprocessing or clausification (transform.pl): its proof uses the
% expansion rules, and its parent as a formula, or as the type of its clause
formula_step(Name) :-
  step(Name, _, tactic(Tactic, _)),
  ( Tactic = transform(_) ; Tactic == clausify ), !.

% the types of the built-ins, fresh instances: their Prolog variables are their parameters, the terms
% of an application for those bound by '!', and otherwise inferred (see above)
head_type('$trivial', '$proof'('$true')).
head_type('$refl', '$proof'('$='(_, X, X))).
head_type('$sym', '$proof'(('$='(A, X, Y) => '$='(A, Y, X)))).
head_type('$dne', '$proof'((~(~F) => F))).
% the expansion rules: each takes a proof of a formula, and a refutation of each branch
head_type('$and', '$proof'(((F & G) => ((F => (G => '$false')) => '$false')))).
head_type('$or', '$proof'(((F | G) => ((F => '$false') => ((G => '$false') => '$false'))))).
head_type('$imp', '$proof'(((F => G) => ((~F => '$false') => ((G => '$false') => '$false'))))).
head_type('$iff', '$proof'(((F <=> G) => ((F => (G => '$false')) => ((~F => (~G => '$false')) => '$false'))))).
head_type('$nand', '$proof'((~(F & G) => ((~F => '$false') => ((~G => '$false') => '$false'))))).
head_type('$nor', '$proof'((~(F | G) => ((~F => (~G => '$false')) => '$false')))).
head_type('$nimp', '$proof'((~(F => G) => ((F => (~G => '$false')) => '$false')))).
head_type('$niff', '$proof'((~(F <=> G) => ((F => (~G => '$false')) => ((~F => (G => '$false')) => '$false'))))).
head_type('$ex', '$proof'(('?'(B, F) => ('!'(B, (F => '$false')) => '$false')))).
head_type('$nall', '$proof'((~'!'(B, F) => ('!'(B, (~F => '$false')) => '$false')))).
% the γ rules turn ~? into the ! that a hypothesis instantiates: '$nex' for a binder of a sort, and
% '$nex_t' for one of '$tType' (a type), by convention, as unification cannot exclude it from '$nex'
head_type('$nex', '$proof'((~'?'(B, F) => (('!'(B, ~F) => '$false') => '$false')))).
head_type('$nex_t', '$proof'((~'?'(X:'$tType', F) => (('!'(X:'$tType', ~F) => '$false') => '$false')))).

% rewriting, with an explicit motive P (see above), a term of an arrow sort
head_type('$rewrite', '$proof'('!'(P:'$>'(A, '$o'), ('$='(A, S, T) => ('$at'(P, S) => '$at'(P, T)))))).

% a built-in whose first premise has parameters, which the type of its first argument may bind:
% '$sym', '$dne', and the expansion rules
inferred_premise(Name) :- head_type(Name, '$proof'((A => _))), \+ ground(A).

% the sort of a motive (see above)
arrow_sort(S) :- nonvar(S), S = '$>'(_, _).

% the formula F0 with each application of a motive '$at'('$abs'(X:_, A), T) β-reduced to A[X:=T];
% F0 may have parameters still to infer, and T may be one
applied_motives(F, F) :- var(F), !.
applied_motives('$at'(P, T), F) :- nonvar(P), P = '$abs'(X:_, A), !, substitute(X, T, A, F).
applied_motives(F0, F) :- compound(F0), !, F0 =.. [C|As0], maplist(applied_motives, As0, As), F =.. [C|As].
applied_motives(F, F).

% a rewrite R, '$rewrite' applied to its motive, equation and proof
rewrite_parts(R, Motive, E, M) :- nonvar(R), spine(R, F, [Motive, E, M]), F == '$rewrite'.

% the Branches of the expansion Rule applied to a proof of the formula F, each the formulas that it
% binds, as read off its type: a refutation of each branch, H_1 => ... => '$false', and then
% '$false'. The rules of quantifiers bind an eigenvariable first, so they have none
rule_branches(F, Rule, Branches) :- nonvar(F), head_type(Rule, '$proof'((F => T))), refutations(T, Branches), !.

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

% a step in a proof term: a first-order term has none, as steps are named apart from symbols
head(M, _) :- var(M), !, fail.
head('$lam'(_, _, M), Name) :- !, head(M, Name).
head('$app'(M, N), Name) :- !, ( head(M, Name) ; head(N, Name) ).
head(Name, Name) :- named_step(Name).

% a step or a definition, by its name (utils:named/3)
named_step(Name) :- atom(Name), named(Kind, _, Name), Kind \== input, !.

% M is F applied to the arguments As, in order (a proper list)
curried(F, As, M) :- foldl(app, As, F, M).

app(A, F, '$app'(F, A)).

% M is the head F applied to the arguments As: F is not an application, or a variable
spine(M, F, As) :- spine(M, F, [], As).

spine(M, F, As0, As) :- nonvar(M), M = '$app'(G, A), !, spine(G, F, [A|As0], As).
spine(F, F, As, As).

% an argument of ground IR that is a proof, rather than a first-order term: a variable may be either
proof_argument(M) :- compound(M), ( M = '$app'(_, _) ; M = '$lam'(_, _, _) ), !.
proof_argument(M) :- atom(M), ( named_step(M) ; head_type(M, _) ), !.
