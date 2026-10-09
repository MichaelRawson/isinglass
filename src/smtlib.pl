/*
SMT-LIB back end, in the manner of "Ground Truth": each step is checked separately,
by asserting the ground facts used in its proof term and the negation of its
conclusion (with variables as fresh constants), expecting `unsat`.
The facts are premise instances, and instances of AVATAR definitions, found using the binder
types of the proof term.

Unreconstructed steps (todo) are checked with their premises universally quantified.
Each check is preceded by (echo "name"), so the solver prints the name and then the result.
*/
:- module(smtlib, [emit/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- set_prolog_flag(double_quotes, codes).

emit :-
  out(header),
  forall(ir_step(Name, Conclusion, Justification), out(check(Justification, Name, Conclusion))).

out(G) :- phrase(G, Cs), atom_codes(A, Cs), write(A).

header -->
  "(set-logic ALL)\n",
  "(set-option :print-success false)\n",
  "(declare-sort I 0)\n",
  "(declare-const |$any| I)\n",
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
check(proof(M), Name, clause(Xs, Ls)) -->
  { empty_assoc(Env),
    facts(M, Env, Fs, []) },
  scope(Name, clause(Xs, Ls), Fs).
check(todo(_, Parents), Name, Conclusion) -->
  { findall(F, (member(P, Parents), ir_step(P, C, _), quantified(C, F)), Fs) },
  "; TODO\n",
  scope(Name, Conclusion, Fs).

quantified(clause(Xs, Ls), F) :- clause_formula(clause(Xs, Ls), F).
quantified(formula(F), F).

scope(Name, Conclusion, Fs) -->
  { negated(Conclusion, Ns),
    append(Fs, Ns, All),
    free_variables(All, Vs) },
  "(push 1)\n",
  constants(Vs),
  asserts(All),
  "(echo \"", atom(Name), "\")\n(check-sat)\n(pop 1)\n".

% the negated conclusion, with free variables
negated(clause(_, Ls), Ns) :- findall(~L, member(L, Ls), Ns).
negated(formula(F), [~F]).

constants([]) --> [].
constants([V|Vs]) --> "(declare-const ", term(V), " I)\n", constants(Vs).

asserts([]) --> [].
asserts([F|Fs]) --> "(assert ", formula(F), ")\n", asserts(Fs).

% facts(A, Env, Fs0, Fs): the ground facts used in annotated term A; Env maps binders to types
facts(lam(X, T, A), Env, Fs0, Fs) :- !, put_assoc(X, Env, T, Env1), facts(A, Env1, Fs0, Fs).
facts(let(X, F, A, B), Env, Fs0, Fs) :- !,
  facts(A, Env, Fs0, Fs1),
  put_assoc(X, Env, F, Env1),
  facts(B, Env1, Fs1, Fs).
facts(app(F, Ts, As), Env, Fs0, Fs) :- !,
  fact(F, Ts, As, Env, Fs0, Fs1),
  foldl_facts(As, Env, Fs1, Fs).
facts(_, _, Fs, Fs).

foldl_facts([], _, Fs, Fs).
foldl_facts([A|As], Env, Fs0, Fs) :- facts(A, Env, Fs0, Fs1), foldl_facts(As, Env, Fs1, Fs).

% a premise instance
fact(F, Ts, _, _, [D|Fs], Fs) :- atom(F), step(F, clause(Ts, Ls), _), !, disjunction(Ls, D).
% the definition of Split is used, from F : Split
fact(F, Ts, _, Env, [(Split => D)|Fs], Fs) :-
  get_assoc(F, Env, Split), atom(Split), split(Split, clause(Ts, Ls)), !,
  disjunction(Ls, D).
% the definition of Split holds for eigenvariables Xs, refuting F : ~Split, so Split holds (by skolemisation)
fact(F, [], [A], Env, [(D => Split)|Fs], Fs) :-
  get_assoc(F, Env, ~Split), atom(Split), split(Split, clause(Xs, Ls)), eigenvariables(A, Xs), !,
  disjunction(Ls, D).
fact(_, _, _, _, Fs, Fs).

eigenvariables(lam(X, '$i', A), [X|Xs]) :- !, eigenvariables(A, Xs).
eigenvariables(_, []).

% '$VAR' terms occurring free, i.e. not bound by a quantifier
free_variables(Fs, Vs) :-
  free_variables(Fs, [], [], Vs0),
  sort(Vs0, Vs).

free_variables('$VAR'(N), Bound, Vs0, Vs) :- !,
  ( memberchk('$VAR'(N), Bound) -> Vs = Vs0 ; Vs = ['$VAR'(N)|Vs0] ).
free_variables('!'(Xs, F), Bound, Vs0, Vs) :- !, append(Xs, Bound, Bound1), free_variables(F, Bound1, Vs0, Vs).
free_variables('?'(Xs, F), Bound, Vs0, Vs) :- !, append(Xs, Bound, Bound1), free_variables(F, Bound1, Vs0, Vs).
free_variables(T, Bound, Vs0, Vs) :-
  compound(T), !,
  T =.. [_|Ts],
  free_variables_list(Ts, Bound, Vs0, Vs).
free_variables(_, _, Vs, Vs).

free_variables_list([], _, Vs, Vs).
free_variables_list([T|Ts], Bound, Vs0, Vs) :-
  free_variables(T, Bound, Vs0, Vs1),
  free_variables_list(Ts, Bound, Vs1, Vs).

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
formula('!'(Xs, F)) --> !, "(forall (", binders(Xs), ") ", formula(F), ")".
formula('?'(Xs, F)) --> !, "(exists (", binders(Xs), ") ", formula(F), ")".
formula(S = T) --> !, "(= ", term(S), " ", term(T), ")".
formula(A) --> term(A).

binders([]) --> [].
binders([X]) --> !, "(", term(X), " I)".
binders([X|Xs]) --> "(", term(X), " I) ", binders(Xs).

term('$VAR'(N)) --> !, "x", number(N).
term('$any') --> !, "|$any|".
term(T) --> { T =.. [F|Ts], length(Ts, N) }, ( { Ts == [] } -> sym(F/N) ; "(", sym(F/N), arguments(Ts), ")" ).

arguments([]) --> [].
arguments([T|Ts]) --> " ", term(T), arguments(Ts).

% namespaced, to avoid clashes with SMT-LIB symbols
sym(F/N) --> "|t.", atom(F), arity(F, N), "|".

% a name overloaded by arity is told apart by its arity
arity(F, N) --> { symbol(F, As, _), \+ length(As, N) }, !, "/", number(N).
arity(_, _) --> [].

atom(A) --> { atom_codes(A, Cs) }, codes(Cs).
number(N) --> { number_codes(N, Cs) }, codes(Cs).

codes([]) --> [].
codes([C|Cs]) --> [C], codes(Cs).
