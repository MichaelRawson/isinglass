/*
SMT-LIB back end, in the manner of "Ground Truth": each step is checked separately,
by asserting the ground facts used in its proof term and the negation of its
conclusion (with its variables as Skolem constants), expecting `unsat`.
The facts are premise instances, and instances of AVATAR definitions, found using the binder
types of the proof term.

Unreconstructed steps (todo) are not checked: the solver echoes a warning instead. Neither are the
negated conjecture, a hypothesis, and the conjecture, which follows from refuting it.
Each check is preceded by (echo "name"), so the solver prints the name and then the result,
and by (set-info :status unsat), so that a solver fails loudly on any other result: z3 reports an
error and exits 1 at the end, and cvc5 aborts at once.

Types are sorts, declared with their arity: SMT-LIB has parametric sorts, but solvers do not yet
support polymorphic functions (declare-sort-parameter). As each check is ground, polymorphic
symbols are monomorphised: each instance f(Types, ...) used in a check is declared in its scope,
as |t.f[Types]|, and so is each '$inhabited'(S). Type variables are Skolem sorts.
*/
:- module(smtlib, [emit_smtlib/0]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(ir).
:- use_module(printing).
:- use_module(signature).
:- set_prolog_flag(double_quotes, codes).

emit_smtlib :-
  header_instances(Declared),
  out(header(Declared)),
  each(ir_step(Name, Conclusion, Justification), out(check(Declared, Justification, Name, Conclusion))).

% '$inhabited'('$tType') is an arbitrary sort
header(Declared) -->
  "(set-logic ALL)\n",
  "(set-option :print-success false)\n",
  "(declare-sort I 0)\n",
  "(declare-sort |$inhabited| 0)\n",
  { findall(S-(Args-Sort), ( symbol(S, [], Args, Sort), \+ defined_symbol(S, _, _) ), Symbols),
    findall(S-(Bs-Body), defined_symbol(S, Bs, Body), Definitions) },
  declarations(Symbols),
  instances(Declared),
  foldl(symbol_definition, Definitions).

% the instances of polymorphic symbols in the bodies of the monomorphic definitions, which are declared
% in the header, before them, and so not in any check
header_instances(Is) :-
  findall(Body, defined_symbol(_, _, Body), Bodies),
  needed_instances(Bodies, [], Is).

% the instances in the formulas Fs, each after those in its definition, that are not Declared already
needed_instances(Fs, Declared, Is) :-
  foldl(formula_instances, Fs, Is0, []),
  sort(Is0, Is1),
  foldl(with_dependencies, Is1, Declared, Is2),
  append(Is3, Declared, Is2),
  reverse(Is3, Is).

% a monomorphic symbol defined by its body, a formula or a term (see ir.pl), in the order of the steps;
% a split symbol of a clause with binders is uninterpreted, as its body is quantified, and its definition
% is asserted where it is used (fact//4)
defined_symbol(S, Bs, Body) :- ir_step(_, _, definition(S, Bs, Body)), symbol(S, [], _, _), \+ split(S, clause([_|_], _)).

symbol_definition(S-(Bs-Body)) -->
  { length(Bs, N), symbol(S, [], _, Sort) },
  "(define-fun ", sym(S/N), " (", binders(Bs), ") ", sort(Sort), " ", defined_body(Sort, Body), ")\n".

defined_body('$o', F) --> !, formula(F).
defined_body(_, T) --> term(T).

% types are sorts; polymorphic symbols are declared by instance, in each check
declarations([]) --> [].
declarations([S-(Args-'$tType')|Ss]) --> !,
  { length(Args, N) },
  "(declare-sort ", sym(S/N), " ", number(N), ")\n",
  declarations(Ss).
declarations([S-(Args-Sort)|Ss]) -->
  { length(Args, N) },
  "(declare-fun ", sym(S/N), " (", sorts(Args), ") ", sort(Sort), ")\n",
  declarations(Ss).

sorts([]) --> [].
sorts([S]) --> !, sort(S).
sorts([S|Ss]) --> sort(S), " ", sorts(Ss).

sort('$i') --> !, "I".
sort('$o') --> !, "Bool".
sort('$inhabited'('$tType')) --> !, "|$inhabited|".
sort('$VAR'(N)) --> !, "x", number(N).
sort(T) --> { atom(T) }, !, sym(T/0).
sort(T) --> { T =.. [F|Ts], length(Ts, N) }, "(", sym(F/N), sort_arguments(Ts), ")".

sort_arguments([]) --> [].
sort_arguments([S|Ss]) --> " ", sort(S), sort_arguments(Ss).

/********************************************************************************
 * checks
 ********************************************************************************/

check(_, input(_, _), _, _) --> [].
% Skolem symbols are uninterpreted, and their definitions not checked
check(_, skolem_def(_, _, _), _, _) --> [].
% nor are definitions: monomorphic symbols are defined in the header
check(_, definition(_, _, _), _, _) --> [].
% a step between formulas has formulas for premises, which have no ground instances to assert
check(_, proof(_), Name, _) --> { formula_step(Name) }, !,
  "(echo \"warning: ", name(Name), " (formula step) is not checked\")\n".
check(Declared, proof(M), Name, clause(Bs, Ls)) -->
  { empty_assoc(Env),
    facts(Env, M, Fs, []),
    skolem_constants(M, Cs0, []),
    sort(Cs0, Cs) },
  scope(Declared, Name, clause(Bs, Ls), Cs, Fs).

% the negated conjecture is a hypothesis, and the conjecture follows from refuting it
check(_, negated_conjecture(_), _, _) --> [].
check(_, conjecture(_, _, _), _, _) --> [].
% unreconstructed: checking it with quantified premises is liable to time out
check(_, todo(Record, _), Name, _) --> { todo_rule(Record, Rule) },
  "(echo \"warning: ", name(Name), " (", atom(Rule), ") is not checked\")\n".

% steps are never SMT-LIB symbols (|t.f|), only text in an echo: a step by its name, a definition by
% its symbol, with " doubled as in an SMT-LIB string
name(Name) --> { named(step, Bare, Name) }, !, quoted(Bare).
name(Name) --> { named(definition, Symbol, Name) }, quoted(Symbol), " (definition)".

quoted(A) --> { atom_codes(A, Cs) }, foldl(quoted_code, Cs).

quoted_code(0'") --> !, "\"\"".
quoted_code(C) --> [C].

% the facts Fs and the negated conclusion, with Skolem constants Cs, and the instances not Declared in
% the header
scope(Declared, Name, Conclusion, Cs, Fs) -->
  { negated(Conclusion, Ns),
    append(Fs, Ns, All),
    needed_instances(All, Declared, Is) },
  "(push 1)\n",
  constants(Cs),
  instances(Is),
  asserts(All),
  "(echo \"", name(Name), "\")\n(set-info :status unsat)\n(check-sat)\n(pop 1)\n".

% the negated conclusion, with free variables
negated(clause(_, Ls), Ns) :- maplist(negation, Ls, Ns).

negation(L, ~L).

% type variables first, as the sorts of the others depend on them
constants(Cs) --> foldl(type_constant, Cs), foldl(term_constant, Cs).

type_constant(X:S) --> { S == '$tType' }, !, "(declare-sort ", term(X), " 0)\n".
type_constant(_) --> [].

term_constant(X:S) --> { S \== '$tType' }, !, "(declare-const ", term(X), " ", sort(S), ")\n".
term_constant(_) --> [].

% the instances of polymorphic symbols in a check, as F/N-Types, to be monomorphised
formula_instances(F) --> { connective(F, Gs) }, !, foldl(formula_instances, Gs).
formula_instances(A) --> term_instances(A).

term_instances(T) --> { polymorphic(T, F, N, Types, Us) }, !, [F/N-Types], foldl(term_instances, Us).
term_instances(T) --> { instance(T, _, Us, _, _) }, !, foldl(term_instances, Us).
term_instances(_) --> [].

% T is an instance of a polymorphic symbol F/N, with type arguments Types and term arguments Us
polymorphic(T, F, N, Types, Us) :-
  compound(T),
  T \= '$VAR'(_),
  functor(T, F, N),
  F \== '$=',
  instance(T, Types, Us, _, _),
  Types \== [].

% the instances Is0, each after the instances in the body of its definition, if it is defined
with_dependencies(I, Is0, Is) :-
  (   memberchk(I, Is0)
  ->  Is = Is0
  ;   instance_definition(I, _, Body)
  ->  formula_instances(Body, Js0, []),
      sort(Js0, Js),
      foldl(with_dependencies, Js, Is0, Is1),
      Is = [I|Is1]
  ;   Is = [I|Is0]
  ).

% the definition of a polymorphic symbol, for the binders Bs of its term arguments, with Types for
% its type parameters
instance_definition(F/_-Types, Bs, Body) :-
  ir_step(_, _, definition(F, Bs0, Body0)),
  same_length(Types, Ts),
  append(Ts, Bs1, Bs0),
  binder_variables(Ts, Xs),
  substitute_all(Xs, Types, Bs1-Body0, Bs-Body).

instances(Is) --> foldl(instance_declaration, Is).

% the declaration of an instance, whose sorts are those of the symbol with Types for its parameters;
% an instance of a defined symbol is defined by its body
instance_declaration(F/N-Types) -->
  { instance_definition(F/N-Types, Bs, Body), !, instance_term(F/N-Types, T), instance(T, _, _, _, Sort) },
  "(define-fun ", instance_name(F/N, Types), " (", binders(Bs), ") ", sort(Sort), " ", defined_body(Sort, Body), ")\n".
instance_declaration(F/N-Types) -->
  { instance_term(F/N-Types, T), instance(T, _, _, Ss, Sort) },
  "(declare-fun ", instance_name(F/N, Types), " (", sorts(Ss), ") ", sort(Sort), ")\n".

% a term of the instance, with fresh term arguments
instance_term(F/N-Types, T) :- length(Types, K), M is N - K, length(Us, M), append(Types, Us, As), T =.. [F|As].

instance_name('$inhabited'/1, [S]) --> !, "|$inhabited[", type_name(S), "]|".
instance_name(F/N, Types) --> "|t.", atom(F), arity(F, N), "[", type_names(Types), "]|".

% a type within a symbol name, as in TPTP
type_names([T]) --> !, type_name(T).
type_names([T|Ts]) --> type_name(T), ",", type_names(Ts).

type_name('$VAR'(N)) --> !, "x", number(N).
type_name('$inhabited'('$tType')) --> !, "$inhabited".
type_name(T) --> { atom(T) }, !, atom(T).
type_name(T) --> { T =.. [F|Ts] }, atom(F), "(", type_names(Ts), ")".

/*
Variables are Skolem constants in a check, shared by its assertions: the conclusion's variables,
from negating it, and the eigenvariables of split definitions proved in the term (see fact//4).
Both are bound by the λs of the proof term, with their sorts.
*/
skolem_constants('$lam'(X, S, M)) --> { \+ proof_annotation(S) }, !, [X:S], skolem_constants(M).
skolem_constants('$lam'(_, _, M)) --> !, skolem_constants(M).
skolem_constants(M) --> { M = _ @ _, spine(M, F, As) }, !, foldl(skolem_constants, As), skolem_constants(F).
skolem_constants(_) --> [].

asserts([]) --> [].
asserts([F|Fs]) --> "(assert ", formula(F), ")\n", asserts(Fs).

% the ground facts used in proof term M, in order; Env maps binders to their types
facts(Env, '$lam'(X, T, M)) --> !, { put_assoc(X, Env, T, Env1) }, facts(Env1, M).
facts(Env, M) --> { ( M = _ @ _ ; atom(M) ), spine(M, F, As) }, !,
  fact(Env, F, As), foldl(facts(Env), As), head_facts(Env, F).
facts(_, _) --> [].

% a head that is a term in its own right, a λ or an application
head_facts(Env, F) --> { compound(F), F \= '$VAR'(_) }, !, facts(Env, F).
head_facts(_, _) --> [].

% a premise instance, by the terms As begin with
fact(_, F, As) -->
  { atom(F), step(F, clause(Bs, Ls), _), instance(Bs, As) }, !,
  { disjunction(Ls, D) }, [D].
% the negated conjecture
fact(_, F, _) --> { atom(F), step(F, formula(G), negated_conjecture(_)) }, !, [G].
% the definition of Split is used, from F : Split
fact(Env, F, As) -->
  { get_assoc(F, Env, '$proof'(Split)), atom(Split), split(Split, clause(Bs, Ls)), instance(Bs, As) }, !,
  { disjunction(Ls, D) }, [(Split => D)].
% the definition of Split holds for eigenvariables Xs, refuting F : ~Split, so Split holds: sound by
% Skolemisation of ~Split => ? [X] : ~C, as the eigenvariables are fresh (which search guarantees,
% and checker.pl checks, but this back end does not)
fact(Env, F, [M]) -->
  { get_assoc(F, Env, '$proof'(~Split)), atom(Split), split(Split, clause(Bs, Ls)),
    binder_variables(Bs, Xs), eigenvariables(M, Xs) }, !,
  { disjunction(Ls, D) }, [(D => Split)].
% ...and so does a component C of a general split, of clause type T (ir:typed_clause/2), refuting F : ~T,
% or F : P(ts), its defined predicate, which unfolds to ~T
fact(Env, F, [M]) -->
  { get_assoc(F, Env, '$proof'(A)), component_type(A, T), typed_clause(T, clause(Bs, Ls)),
    binder_variables(Bs, Xs), eigenvariables(M, Xs) }, !,
  { disjunction(Ls, D) }, [(D => T)].
fact(_, _, _) --> [].

% the binders Bs instantiated by the terms that the arguments As begin with
instance(Bs, As) :- binder_variables(Bs, Ts), append(Ts, _, As), !.

component_type(~T, T) :- !.
component_type(A, T) :- defined_atom(A, ~T).

eigenvariables('$lam'(X, S, M), [X|Xs]) :- \+ proof_annotation(S), !, eigenvariables(M, Xs).
eigenvariables(_, []).

/********************************************************************************
 * formulas and terms
 ********************************************************************************/

formula('$false') --> !, "false".
formula('$true') --> !, "true".
formula(~F) --> !, "(not ", formula(F), ")".
formula((F | G)) --> !, "(or ", formula(F), " ", formula(G), ")".
formula((F & G)) --> !, "(and ", formula(F), " ", formula(G), ")".
formula((F => G)) --> !, "(=> ", formula(F), " ", formula(G), ")".
formula((F <=> G)) --> !, "(= ", formula(F), " ", formula(G), ")".
formula('!'(B, F)) --> !, "(forall (", binder(B), ") ", formula(F), ")".
formula('?'(B, F)) --> !, "(exists (", binder(B), ") ", formula(F), ")".
formula('$='(_, S, T)) --> !, "(= ", term(S), " ", term(T), ")".
formula(A) --> term(A).

binders([]) --> [].
binders([B]) --> !, binder(B).
binders([B|Bs]) --> binder(B), " ", binders(Bs).

binder(X:S) --> "(", term(X), " ", sort(S), ")".

term('$VAR'(N)) --> !, "x", number(N).
term('$BOUND'(N)) --> !, "y", number(N).
term(T) --> { polymorphic(T, F, N, Types, []) }, !, instance_name(F/N, Types).
term(T) --> { polymorphic(T, F, N, Types, Us) }, !, "(", instance_name(F/N, Types), arguments(Us), ")".
term(T) --> { atomic(T) }, !, sym(T/0).
term(T) --> { T =.. [F|Ts], length(Ts, N) }, "(", sym(F/N), arguments(Ts), ")".

arguments([]) --> [].
arguments([T|Ts]) --> " ", term(T), arguments(Ts).

% namespaced, to avoid clashes with SMT-LIB symbols
sym(F/N) --> "|t.", atom(F), arity(F, N), "|".

% a name overloaded by arity is told apart by its arity
arity(F, N) --> { overloaded(F/N) }, !, "/", number(N).
arity(_, _) --> [].
