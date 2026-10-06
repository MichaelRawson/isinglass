/*
SMT-LIB back end, in the manner of "Ground Truth": each step is checked separately,
by asserting the ground premise instances used in its reconstruction and the negation of its
conclusion (with variables as fresh constants), expecting `unsat`.

Unreconstructed steps (todo) are checked with their premises universally quantified.
Each check is preceded by (echo "name"), so the solver prints the name and then the result.
*/
:- module(smtlib, [emit/1]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(ir).
:- set_prolog_flag(double_quotes, codes).

emit(_) :-
  out(header),
  \+ ( ir_step(Name, Conclusion, _), \+ out(check(Name, Conclusion)) ).

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
  "(declare-fun ", sym(S), " (", sorts(Args), ") ", sort(Sort), ")\n",
  declarations(Ss).

sorts([]) --> [].
sorts([S]) --> !, sort(S).
sorts([S|Ss]) --> sort(S), " ", sorts(Ss).

sort('$i') --> "I".
sort('$o') --> "Bool".

/********************************************************************************
 * checks
 ********************************************************************************/

check(Name, Conclusion) -->
  { elaborate(Name, E) },
  check(E, Name, Conclusion).

check(input(_, _), _, _) --> [].
check(split_def(_, _), _, _) --> [].
check(refute(_, E), Name, clause(Xs, Ls)) -->
  { assertions(E, [], Fs, []) },
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

/*
assertions(E, Ds, Fs0, Fs): the ground facts used in elaborated refutation E
Ds maps local definitions to their split symbols
*/
assertions(use(P, Ts, Args), Ds, [F|Fs0], Fs) :-
  (   memberchk(P-(Split-Clause), Ds)
  ->  instance(Clause, Ts, Ls), disjunction(Ls, D), F = (Split => D)
  ;   ir_step(P, Clause, _), instance(Clause, Ts, Ls), disjunction(Ls, F)
  ),
  argument_assertions(Args, Ds, Fs0, Fs).
assertions(let(_, _, Arg, E), Ds, Fs0, Fs) :-
  argument_assertions([Arg], Ds, Fs0, Fs1),
  assertions(E, Ds, Fs1, Fs).
assertions(contra(_, _, arg(L, A)), Ds, Fs0, Fs) :-
  argument_assertions([arg(L, A)], Ds, Fs0, Fs).
% for eigenvariables Xs, the definition of Split holds if it holds for Xs (sound by skolemisation)
assertions(contra(_, Split, intro(Xs, _, E)), Ds, [(D => Split)|Fs0], Fs) :-
  split_def(Split, Clause),
  instance(Clause, Xs, Ls),
  disjunction(Ls, D),
  assertions(E, Ds, Fs0, Fs).

argument_assertions([], _, Fs, Fs).
argument_assertions([arg(L, A)|Args], Ds, Fs0, Fs) :-
  argument_assertion(A, L, Ds, Fs0, Fs1),
  argument_assertions(Args, Ds, Fs1, Fs).

argument_assertion(hyp(_), _, _, Fs, Fs).
argument_assertion(sym(L, A), _, Ds, Fs0, Fs) :- argument_assertion(A, L, Ds, Fs0, Fs).
argument_assertion(assume(_, E), _, Ds, Fs0, Fs) :- assertions(E, Ds, Fs0, Fs).
argument_assertion(unfold(D, Clause, E), Split, Ds, Fs0, Fs) :- assertions(E, [D-(Split-Clause)|Ds], Fs0, Fs).

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
formula((F <~> G)) --> !, "(xor ", formula(F), " ", formula(G), ")".
formula('!'(Xs, F)) --> !, "(forall (", binders(Xs), ") ", formula(F), ")".
formula('?'(Xs, F)) --> !, "(exists (", binders(Xs), ") ", formula(F), ")".
formula(S = T) --> !, "(= ", term(S), " ", term(T), ")".
formula(A) --> term(A).

binders([]) --> [].
binders([X]) --> !, "(", term(X), " I)".
binders([X|Xs]) --> "(", term(X), " I) ", binders(Xs).

term('$VAR'(N)) --> !, "x", number(N).
term('$any') --> !, "|$any|".
term(T) --> { T =.. [F|Ts] }, ( { Ts == [] } -> sym(F) ; "(", sym(F), arguments(Ts), ")" ).

arguments([]) --> [].
arguments([T|Ts]) --> " ", term(T), arguments(Ts).

% namespaced, to avoid clashes with SMT-LIB symbols
sym(S) --> "|t.", atom(S), "|".

atom(A) --> { atom_codes(A, Cs) }, codes(Cs).
number(N) --> { number_codes(N, Cs) }, codes(Cs).

codes([]) --> [].
codes([C|Cs]) --> [C], codes(Cs).
