/*
SMT-LIB back end, in the manner of "Ground Truth": each step is checked separately,
by asserting the ground facts used in its proof term and the negation of its
conclusion (with its variables as Skolem constants), expecting `unsat`.
The facts are premise instances, and instances of AVATAR definitions, found using the binder
types of the proof term.

Unreconstructed steps (todo) are checked with their premises universally quantified.
Each check is preceded by (echo "name"), so the solver prints the name and then the result,
and by (set-info :status unsat), so that a solver fails loudly on any other result: z3 reports an
error and exits 1 at the end, and cvc5 aborts at once.
*/
:- module(smtlib, [emit/0]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(printing).
:- use_module(signature).
:- set_prolog_flag(double_quotes, codes).

emit :-
  out(header),
  forall(ir_step(Name, Conclusion, Justification), out(check(Justification, Name, Conclusion))).

header -->
  "(set-logic ALL)\n",
  "(set-option :print-success false)\n",
  "(declare-sort I 0)\n",
  "(declare-const |$inhabited| I)\n",
  { findall(S-(Args-Sort), symbol(S, Args, Sort), Symbols) },
  declarations(Symbols).

declarations([]) --> [].
declarations([S-(Args-Sort)|Ss]) -->
  { length(Args, N) },
  "(declare-fun ", sym(S/N), " (", sorts(Args), ") ", sort(Sort), ")\n",
  declarations(Ss).

sorts([]) --> [].
sorts([S]) --> !, sort(S).
sorts([S|Ss]) --> sort(S), " ", sorts(Ss).

sort('$i') --> "I".
sort('$o') --> "Bool".

/********************************************************************************
 * checks
 ********************************************************************************/

check(input(_, _), _, _) --> [].
check(split_def(_, _), _, _) --> [].
check(proof(M), Name, clause(Bs, Ls)) -->
  { empty_assoc(Env),
    phrase(facts(Env, M), Fs),
    phrase(skolem_constants(M), Cs0),
    sort(Cs0, Cs) },
  scope(Name, clause(Bs, Ls), Cs, Fs).
check(todo(_, Parents), Name, Conclusion) -->
  { findall(F, (member(P, Parents), ir_step(P, C, _), quantified(C, F)), Fs),
    conclusion_constants(Conclusion, Cs) },
  "; TODO\n",
  scope(Name, Conclusion, Cs, Fs).

quantified(clause(Bs, Ls), F) :- clause_formula(clause(Bs, Ls), F).
quantified(formula(F), F).

% the facts Fs and the negated conclusion, with Skolem constants Cs
scope(Name, Conclusion, Cs, Fs) -->
  { negated(Conclusion, Ns),
    append(Fs, Ns, All) },
  "(push 1)\n",
  constants(Cs),
  asserts(All),
  "(echo \"", atom(Name), "\")\n(set-info :status unsat)\n(check-sat)\n(pop 1)\n".

% the negated conclusion, with free variables
negated(clause(_, Ls), Ns) :- maplist(negation, Ls, Ns).
negated(formula(F), [~F]).

negation(L, ~L).

constants([]) --> [].
constants([X:S|Cs]) --> "(declare-const ", term(X), " ", sort(S), ")\n", constants(Cs).

/*
Variables are Skolem constants in a check, shared by its assertions: the conclusion's variables,
from negating it, and the eigenvariables of split definitions proved in the term (see fact//4).
Both are bound by the λs of the proof term, with their sorts; a todo step has the conclusion's.
*/
skolem_constants(lam('$VAR'(N), S, M)) --> !, ['$VAR'(N):S], skolem_constants(M).
skolem_constants(lam(_, _, M)) --> !, skolem_constants(M).
skolem_constants(let(_, _, M, N)) --> !, skolem_constants(M), skolem_constants(N).
skolem_constants(app(_, _, Ms)) --> !, foldl(skolem_constants, Ms).
skolem_constants(_) --> [].

conclusion_constants(clause(Bs, _), Bs).
conclusion_constants(formula(_), []).

asserts([]) --> [].
asserts([F|Fs]) --> "(assert ", formula(F), ")\n", asserts(Fs).

% the ground facts used in proof term M, in order; Env maps binders to their types
facts(Env, lam(X, T, M)) --> !, { put_assoc(X, Env, T, Env1) }, facts(Env1, M).
facts(Env, let(X, F, M, N)) --> !, facts(Env, M), { put_assoc(X, Env, F, Env1) }, facts(Env1, N).
facts(Env, app(F, Ts, Ms)) --> !, fact(Env, F, Ts, Ms), foldl(facts(Env), Ms).
facts(_, _) --> [].

% a premise instance
fact(_, F, Ts, _) -->
  { atom(F), step(F, clause(Bs, Ls), _), binder_variables(Bs, Ts) }, !,
  { disjunction(Ls, D) }, [D].
% the definition of Split is used, from F : Split
fact(Env, F, Ts, _) -->
  { get_assoc(F, Env, Split), atom(Split), split(Split, clause(Bs, Ls)), binder_variables(Bs, Ts) }, !,
  { disjunction(Ls, D) }, [(Split => D)].
% the definition of Split holds for eigenvariables Xs, refuting F : ~Split, so Split holds: sound by
% Skolemisation of ~Split => ? [X] : ~C, as the eigenvariables are fresh (which search guarantees,
% and checker.pl checks, but this back end does not)
fact(Env, F, [], [M]) -->
  { get_assoc(F, Env, ~Split), atom(Split), split(Split, clause(Bs, Ls)),
    binder_variables(Bs, Xs), eigenvariables(M, Xs) }, !,
  { disjunction(Ls, D) }, [(D => Split)].
fact(_, _, _, _) --> [].

eigenvariables(lam('$VAR'(N), _, M), ['$VAR'(N)|Xs]) :- !, eigenvariables(M, Xs).
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
formula('!'(Bs, F)) --> !, "(forall (", binders(Bs), ") ", formula(F), ")".
formula('?'(Bs, F)) --> !, "(exists (", binders(Bs), ") ", formula(F), ")".
formula(S = T) --> !, "(= ", term(S), " ", term(T), ")".
formula(A) --> term(A).

binders([]) --> [].
binders([B]) --> !, binder(B).
binders([B|Bs]) --> binder(B), " ", binders(Bs).

binder(X:S) --> "(", term(X), " ", sort(S), ")".

term('$VAR'(N)) --> !, "x", number(N).
term('$inhabited') --> !, "|$inhabited|".
term(T) --> { atomic(T) }, !, sym(T/0).
term(T) --> { T =.. [F|Ts], length(Ts, N) }, "(", sym(F/N), arguments(Ts), ")".

arguments([]) --> [].
arguments([T|Ts]) --> " ", term(T), arguments(Ts).

% namespaced, to avoid clashes with SMT-LIB symbols
sym(F/N) --> "|t.", atom(F), arity(F, N), "|".

% a name overloaded by arity is told apart by its arity
arity(F, N) --> { overloaded(F/N) }, !, "/", number(N).
arity(_, _) --> [].
