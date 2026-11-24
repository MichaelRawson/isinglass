/*
The intermediate representation (IR) of proofs: ir_step(Name, Conclusion, Justification) (db.pl),
in dependency order, ground.

  Conclusion    ::= clause(Bs, Literals) | formula(F)
  Justification ::= input(Role, Source)
                  | negated_conjecture(Conjecture)      a hypothesis, discharged by conjecture
                  | conjecture(Source, Negated, Refutation)
                  | definition(Symbol, Bs, Body)        of a function (a term) or predicate (a formula)
                  | skolem_def(Symbol, Bs, F)           the conclusion is its choice axiom
                  | proof(M)
                  | todo(Record, Parents)               not reconstructed

A type is a sort, or '$proof'(F), of the proofs of F, taken apart as needed: '$proof'(F => G) is
'$proof'(F) → '$proof'(G), ~F is F => '$false', and '$proof'('!'(X:S, F)) is Π X : S. '$proof'(F).
A clause has the type of clause_type/2, Π Bs. ~L_0 => ... => ~L_n-1 => '$false', and formula(F) of F.
Bound variables are named canonically (logic:canonical/2), so types are compared syntactically.

Proofs, in minimal logic with an abstract ⊥ ('$false'):

  M ::= '$VAR'(N)            a hypothesis or an eigenvariable, as the annotation of its λ says
      | Name                 a step ('$step:f12', '$def:P', utils:named/3)
      | Builtin              typed by head_type/2
      | M @ N                N is a term if M : '$proof'('!'(X:S, F)), a proof if M : '$proof'(A => B)
      | '$lam'(X, T, M)      T a sort, a proof type, or '$inferred' (a hypothesis of an expansion rule)

'$rewrite' takes its motive explicitly, as unification cannot infer it: '$rewrite' @ '$abs'(X:S, A)
@ E @ M, for E : S = T and M : A[X:=S], proves A[X:=T]. The motive is of the arrow sort '$>'(S, '$o'),
and '$at'(P, T) its application (applied_motives/2); both occur only in head_type/2.
*/
:- module(ir, [clause_type/2, step_type/2, reference/2, cited_steps/1, head_type/2, inferred_premise/1, curried/3, rewrite_parts/4, applied_motives/2, arrow_sort/1, spine/3, proof_argument/1, term_size/2, named_step/1, rule_branches/3, formula_step/1, todo_rule/2, choice_axiom/4, proof_annotation/1,
  defined_atom/2, defined_term/2, expanded/2, terms_unfolded/2, typed_clause/2]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- op(200, yfx, @). % as exported by ops, which Trealla ignores
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
% '$inferred'
proof_annotation(A) :- ( nonvar(A), A = '$proof'(_) -> true ; A == '$inferred' ).

% a step between formulas, preprocessing or clausification (transform.pl): its proof uses the
% expansion rules, and its parent as a formula, or as the type of its clause
formula_step(Name) :-
  step(Name, _, tactic(Tactic, _)),
  ( Tactic = transform(_) ; Tactic == clausify ), !.

% the rule of a todo step, as a warning names it
todo_rule(esa(Rule, _), Rule) :- !.
todo_rule(Record, Rule) :- functor(Record, Rule, _).

% the types of the built-ins, fresh instances: their Prolog variables are their parameters, inferred
% by unification (with the expected type, and the types of the arguments)
head_type('$trivial', '$proof'('$true')).
head_type('$refl', '$proof'('$='(_, X, X))).
head_type('$sym', '$proof'(('$='(A, X, Y) => '$='(A, Y, X)))).
head_type('$dne', '$proof'((~(~F) => F))).
% the expansion rules: each takes a proof of a formula, and a refutation of each branch
head_type('$and', '$proof'(((F & G) => ((F => (G => '$false')) => '$false')))).
head_type('$or', '$proof'(((F | G) => ((F => '$false') => ((G => '$false') => '$false'))))).
head_type('$imp', '$proof'(((F => G) => ((~F => '$false') => ((G => '$false') => '$false'))))).
head_type('$iff', '$proof'(((F <=> G) => ((F => (G => '$false')) => ((~F => (~G => '$false')) => '$false'))))).
head_type('$nand', '$proof'((~ (F & G) => ((~F => '$false') => ((~G => '$false') => '$false'))))).
head_type('$nor', '$proof'((~ (F | G) => ((~F => (~G => '$false')) => '$false')))).
head_type('$nimp', '$proof'((~ (F => G) => ((F => (~G => '$false')) => '$false')))).
head_type('$niff', '$proof'((~ (F <=> G) => ((F => (~G => '$false')) => ((~F => (G => '$false')) => '$false'))))).
head_type('$ex', '$proof'(('?'(B, F) => ('!'(B, (F => '$false')) => '$false')))).
head_type('$nall', '$proof'((~'!'(B, F) => ('!'(B, (~F => '$false')) => '$false')))).
% the γ rules turn ~? into the ! that a hypothesis instantiates: '$nex' for a binder of a sort, and
% '$nex_t' for one of '$tType' (a type), by convention, as unification cannot exclude it from '$nex'
head_type('$nex', '$proof'((~'?'(B, F) => (('!'(B, ~F) => '$false') => '$false')))).
head_type('$nex_t', '$proof'((~'?'(X:'$tType', F) => (('!'(X:'$tType', ~F) => '$false') => '$false')))).

% rewriting, with an explicit motive P, a term of an arrow sort
head_type('$rewrite', '$proof'('!'(P:'$>'(A, '$o'), ('$='(A, S, T) => ('$at'(P, S) => '$at'(P, T)))))).

% a built-in whose first premise has parameters, which the type of its first argument may bind:
% '$sym', '$dne', and the expansion rules
inferred_premise(Name) :- head_type(Name, '$proof'((A => _))), \+ ground(A).

% the sort of a motive
arrow_sort(S) :- nonvar(S), S = '$>'(_, _).

% the formula F0 with each application of a motive '$at'('$abs'(X:_, A), T) β-reduced to A[X:=T];
% F0 may have parameters still to infer, and T may be one
applied_motives(F, F) :- var(F), !.
applied_motives('$at'(P, T), F) :- nonvar(P), P = '$abs'(X:_, A), !, substitute(X, T, A, F).
applied_motives(F0, F) :- compound(F0), !, map_arguments(applied_motives, F0, F).
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
  substitute_all(Xs, Ts, Body0, Body).
defined_atom(A, Body) :-
  atom(A),
  ir_step(_, formula(_), definition(A, [], Body)).

% the canonical formula F0 with each defined atom and term unfolded, throughout (definitions are not
% circular)
expanded(F0, F) :- opened(F0, F1), unfolded(F1, F2), ( F2 == F1 -> F = F0 ; canonical(F2, F) ).

unfolded(F0, F) :- quantifier(F0, Q, B, G0), !, unfolded(G0, G), F =.. [Q, B, G].
unfolded(F0, F) :- connective(F0, _), !, map_arguments(unfolded, F0, F).
unfolded(A0, F) :-
  unfolded_arguments(A0, A),
  ( defined_atom(A, Body0) -> opened(Body0, Body), unfolded(Body, F) ; F = A ).

unfolded_arguments(A0, A) :- compound(A0), !, map_arguments(unfolded_term, A0, A).
unfolded_arguments(A, A).

% a quantifier-free formula with each defined function term unfolded, but not its defined atoms
terms_unfolded(F0, F) :- connective(F0, _), !, map_arguments(terms_unfolded, F0, F).
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
  substitute_all(Xs, Ts, Body0, Body).

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
head(M @ N, Name) :- !, ( head(M, Name) ; head(N, Name) ).
head(Name, Name) :- named_step(Name).

% a step or a definition, by its name (utils:named/3)
named_step(Name) :- atom(Name), named(Kind, _, Name), Kind \== input, !.

% M is F applied to the arguments As, in order (a proper list)
curried(F, As, M) :- foldl(app, As, F, M).

app(A, F, F @ A).

% M is the head F applied to the arguments As: F is not an application, or a variable
spine(M, F, As) :- spine(M, F, [], As).

spine(M, F, As0, As) :- nonvar(M), M = G @ A, !, spine(G, F, [A|As0], As).
spine(F, F, As, As).

% the number of symbols of a term, but for the tag of a proof type
term_size('$proof'(F), N) :- !, term_size(F, N).
term_size(T, N) :- compound(T), !, T =.. [_|Ts], foldl(add_size, Ts, 1, N).
term_size(_, 1).

add_size(T, N0, N) :- term_size(T, K), N is N0 + K.

% an argument of ground IR that is a proof, rather than a first-order term: a variable may be either
proof_argument(M) :- compound(M), ( M = _ @ _ ; M = '$lam'(_, _, _) ), !.
proof_argument(M) :- atom(M), ( named_step(M) ; head_type(M, _) ), !.
