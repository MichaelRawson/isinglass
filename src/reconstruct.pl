/*
Reconstruct steps into ir_step/3 facts by searching for proof terms (see ir.pl for the IR).

The search procedures below are given hypotheses Hs, a list of X-T pairs where X : T is a
variable, and build a term of type ⊥, which is then abstracted over the conclusion (checker.pl
type-checks it). Each λ is annotated with its binder's type when it is built (but for those of the
expansion rules in transform.pl, '$inferred'). During search, binders are Prolog variables, and
are named h(N) afterwards.
Clauses are stored with Prolog variables (db.pl), so retrieving a premise gives a fresh instance.
The conclusion is made rigid by numbering its variables, and premise instances are found by
unification with it, Prolog's backtracking performing the search.
Steps between formulas are reconstructed by the tactics of transform.pl, which have the same interface.
*/
:- module(reconstruct, [reconstruct/0]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(signature).
:- use_module(rup).
:- use_module(close).
:- use_module(matching).
:- use_module(transform).
:- use_module(ir).

% reconstruct everything required for the last refutation, and then the conjecture, if any
reconstruct :-
  each(step(_, _, split_def(Symbol, Clause)), record(split(Symbol, Clause))),
  findall(Name, step(Name, clause([], []), _), Refutations),
  final(Refutations, Refutation),
  prove(Refutation),
  findall(Name-Source, step(Name, _, conjecture(Source)), Conjectures),
  conjecture(Conjectures, Refutation).

% the conjecture G holds by refuting its negation, a hypothesis ~G: the last step, and the only
% classical one (but for clausification), as the refutation is in minimal logic with abstract ⊥
conjecture([], _).
conjecture([Conjecture-Source], Refutation) :-
  step(Negated, _, negated_conjecture(Conjecture)), !,
  prove(Negated),
  step(Conjecture, formula(G), _),
  rigid(formula(G), _),
  record(ir_step(Conjecture, formula(G), conjecture(Source, Negated, Refutation))).
conjecture(Conjectures, _) :-
  warn(['error: expected one conjecture and its negation, not ', Conjectures]),
  fail.

prove(Name) :- ir_step(Name, _, _), !.
prove(Name) :-
  step(Name, Conclusion, How),
  rigid(Conclusion, Fresh),
  justify(How, Conclusion, Fresh, Justification),
  record(ir_step(Name, Conclusion, Justification)).

% number the variables of a clause, in binder order; Fresh is the next index
% the bound variables of a formula are named canonically (see logic.pl), and any others numbered
rigid(clause(Bs, _), Fresh) :- binder_variables(Bs, Xs), number_vars(Xs, 0, Fresh).
rigid(formula(F), Fresh) :- canonical(F, _), term_variables(F, Vs), number_vars(Vs, 0, Fresh).

justify(input(Role, Source), _, _, input(Role, Source)).
% the defining clause is rigid as a clause is, not as part of the definition's formula
justify(split_def(Symbol, _), _, _, split_def(Symbol, Clause)) :-
  split(Symbol, Clause),
  rigid(Clause, _),
  definitions_first(Clause).
justify(negated_conjecture(Conjecture), _, _, negated_conjecture(Conjecture)).
justify(define(Symbol), Conclusion, _, Justification) :-
  (   defining(Symbol, Conclusion, Bs, Body)
  ->  definitions_first(Body),
      Justification = definition(Symbol, Bs, Body)
  ;   warn(['warning: ', Symbol, ' is not defined by ', Conclusion]),
      Justification = todo(esa(definition, [Symbol]), [])
  ).
justify(todo(Record, Parents), _, _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Fresh, Justification) :-
  maplist(prove, Parents),
  splits_first(Conclusion),
  search(Tactic, Parents, Conclusion, Fresh, Justification).

% the tactic finds a term of type ⊥ from hypotheses that refute the conclusion
search(Tactic, Parents, Conclusion, Fresh, proof(M)) :-
  refutation(Conclusion, Hs, Body, M),
  once(call(Tactic, Fresh, Hs, Parents, Body)), !,
  close_term(M).
% ...or it fails, and the step is left to do
search(Tactic, Parents, Conclusion, _, todo(Tactic, Parents)) :-
  warn(['warning: ', Tactic, ' failed to reconstruct ', Conclusion]).

% a hypothesis V : ~L for each literal L
hypotheses([], []).
hypotheses([L|Ls], [_-(~L)|Hs]) :- hypotheses(Ls, Hs).

% M proves the conclusion, given Body : ⊥ from the hypotheses Hs: a clause is abstracted over its
% eigenvariables and the hypotheses for its literals, and a formula F is proved classically, from ~F
refutation(clause(Bs, Ls), Hs, Body, M) :-
  hypotheses(Ls, Hs),
  binders(Bs, Hs, Binders),
  lambdas(Binders, Body, M).
refutation(formula(F), [H-(~F)], Body, app('$dne', [F], [lam(H, ~F, Body)])).

% a definition cites no steps, so those of the function symbols in T come first, by name
definitions_first(T) :- each(( subterm(T, U), functor(U, F, _), step(Name, _, define(F)) ), prove(Name)).

% so do the definitions of the split literals of a clause, which a step need not cite (sat_conversion)
splits_first(clause(_, Ls)) :- each(( member(L, Ls), atom_of(L, A), atom(A), step(Name, _, split_def(A, _)) ), prove(Name)).
splits_first(formula(_)).

atom_of(~A, A) :- !.
atom_of(A, A).

% a function definition Symbol(Xs) = Body, either way round: Bs are the binders of Xs, in order
defining(Symbol, clause(Cs, ['$='(_, A, B)]), Bs, Body) :-
  ( A =.. [Symbol|Xs], Body = B ; B =.. [Symbol|Xs], Body = A ), !,
  maplist(argument_binder(Cs), Xs, Bs).
% ...or a predicate definition ![Cs] : (Symbol(Xs) <=> Body), whose binders become eigenvariables
defining(Symbol, formula(F), Bs, Body) :-
  ( F = '!'(Cs0, D0) -> foldl(eigenvariable_binder, Cs0, Cs, 0-D0, _-D) ; Cs = [], D = F ),
  D = (A <=> Body),
  A =.. [Symbol|Xs],
  maplist(argument_binder(Cs), Xs, Bs).

eigenvariable_binder(X:S, '$VAR'(N):S, N-F0, N1-F) :- N1 is N + 1, substitute(X, '$VAR'(N), F0, F).

argument_binder(Cs, X, X:S) :- member(Y:S, Cs), Y == X, !.

% binders X-T: eigenvariables X-Sort for the clause's binders Bs, then the hypotheses Hs
binders(Bs, Hs, Binders) :- maplist(eigenvariable, Bs, Is), append(Is, Hs, Binders).

eigenvariable(X:S, X-S).

% a fresh instance of a premise clause, with variables Ts
premise(Name, Ts, Ls) :- step(Name, clause(Bs, Ls), _), binder_variables(Bs, Ts).

/********************************************************************************
 * search procedures: tactic(Fresh, Hypotheses, Parents, M)
 * Fresh is the next available '$VAR' index, for eigenvariables
 ********************************************************************************/

% the conclusion is an instance of the premise, modulo symmetry, factoring and duplicates
variant(_, Hs, [Premise], app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(matches(Hs), Ls, Ms).

% the conclusion ~A denies the negated conjecture ~A, a hypothesis, modulo symmetry
deny(_, [H-(~(~A))], [Negated], app(H, [], [M])) :-
  step(Negated, formula(~G), _),
  denied(G, Negated, A, M).

denied(G, Negated, A, app(Negated, [], [])) :- unify_with_occurs_check(G, A).
denied(G, Negated, A, M) :- flip(G, F), unify_with_occurs_check(F, A), flipped(A, Negated, M).

% resolution: literals of the major premise are either in the conclusion, or refuted by (an instance
% of) a minor premise; binary, or with unit minors (unit-resulting resolution)
% in binary resolution, only positive literals are refuted by the minor: one resolved literal is
% positive, and either premise may be the major, so this is complete, and avoids an exponential search
% on wide negative clauses; with several minors, negative literals are refuted by units (but for split
% literals)
resolve(_, Hs, Premises, app(Major, Ts, Ms)) :-
  select(Major, Premises, Minors),
  premise(Major, Ts, Ks),
  maplist(resolve_literal(Hs, Minors), Ks, Ms).

resolve_literal(Hs, _, K, M) :- matches(Hs, K, M).
resolve_literal(Hs, Minors, K, lam(X, K, app(Minor, Ts, Ms))) :-
  member(Minor, Minors),
  premise(Minor, Ts, Ls),
  ( K \= ~_ ; Minors = [_, _|_], unit(Ls) ),
  maplist(matches([X-K|Hs]), Ls, Ms).

% a unit clause, but for AVATAR's split literals, which are in the conclusion
unit(Ls) :- exclude(avatar_literal, Ls, [_]).

avatar_literal(L) :- atom_of(L, A), atom(A), split(A, _), !.

% the first tactic of Tactics that succeeds
first(Tactics, Fresh, Hs, Parents, M) :- member(Tactic, Tactics), call(Tactic, Fresh, Hs, Parents, M), !.

% the hypotheses Hs with the defined atoms of their literals unfolded (see ir.pl), where the body is a
% literal: Inner then refutes the conclusion as if it were stated with the bodies, from its first parent
defined(Inner, Fresh, Hs, [Parent|_], M) :-
  unfolded_hypotheses(Hs, Hs1, M, M1),
  call(Inner, Fresh, Hs1, [Parent], M1).

% M binds the hypotheses Hs1 and then is M1
unfolded_hypotheses([], [], M, M).
unfolded_hypotheses([H0|Hs0], [H|Hs], M, M1) :-
  unfolded_hypothesis(H0, H, M, M0),
  unfolded_hypotheses(Hs0, Hs, M0, M1).

% X : ~L is Y : ~L1, where L1 is the literal L with its atom unfolded, by a let that states the
% unfolded type; a hypothesis ~~~C is ~C, refuting C, by one more let
unfolded_hypothesis(X-(~L), H, M, M1) :-
  unfolded_literal(L, L1), !,
  (   L1 = ~(~C)
  ->  H = Y-(~C),
      M = let(Z, ~L1, X, let(Y, ~C, lam(W, C, app(Z, [], [lam(N, ~C, app(N, [], [W]))])), M1))
  ;   H = Y-(~L1),
      M = let(Y, ~L1, X, M1)
  ).
unfolded_hypothesis(H, H, M, M).

unfolded_literal(~A, ~B) :- defined_atom(A, B), literal(B).
unfolded_literal(A, B) :- A \= ~_, defined_atom(A, B), literal(B).

literal(~A) :- !, \+ connective(A, _).
literal(A) :- \+ connective(A, _).

% the conclusion is a ground tautology of equality: the hypotheses ~~A for its negative literals give
% facts A, whose equations are completed into rewrite rules (rigid variables are constants); then, with
% every literal in normal form, a fact is refuted by a hypothesis, or a positive literal is reflexive
tautology(Fresh, Hs, _, M) :-
  partition(fact_hypothesis, Hs, Gs, Ns0),
  foldl(fact, Gs, Facts0, M, M0),
  partition(equation_fact, Facts0, Equations, Facts1),
  completed(Fresh, Equations, [], Rules, M0, M1),
  normalised_all(Fresh, Rules, Facts1, Facts, M1, M2),
  normalised_all(Fresh, Rules, Ns0, Ns, M2, M3),
  closed(Ns, Facts, M3).

fact_hypothesis(_-(~(~A))) :- \+ connective(A, _).

fact(X-(~(~A)), E-A, app(X, [], [lam(E, A, M)]), M).

equation_fact(_-'$='(_, _, _)).

closed(Ns, _, app(N, [], [app('$refl', [S, T], [])])) :- member(N-(~'$='(S, T, U)), Ns), T == U.
closed(Ns, Facts, M) :- member(E-A, Facts), matches(Ns, A, R), applied(R, E, M).

% ground completion: each equation E : S = T, in normal form, is a rule from the greater side to the
% smaller, and the rules that it rewrites are completed again
completed(_, [], Rules, Rules, M, M).
completed(Fresh, [Equation0|Equations], Rules0, Rules, M, M1) :-
  normalised(Fresh, Rules0, Equation0, E-'$='(S, A, B), M, M0),
  (   A == B
  ->  completed(Fresh, Equations, Rules0, Rules, M0, M1)
  ;   oriented(E, S, A, B, Rule),
      Rule = _-'$='(_, L, _),
      partition(reducible(L), Rules0, Reducible, Irreducible),
      append(Reducible, Equations, Equations1),
      completed(Fresh, Equations1, [Rule|Irreducible], Rules, M0, M1)
  ).

oriented(E, S, A, B, E-'$='(S, A, B)) :- smaller(B, A), !.
oriented(E, S, A, B, app('$sym', [S, A, B], [E])-'$='(S, B, A)).

% terms are ordered by size, then in the standard order: a total order, closed under contexts
smaller(T, U) :- size(T, N), size(U, K), N-T @< K-U.

size(T, N) :- compound(T), !, T =.. [_|Ts], foldl(add_size, Ts, 1, N).
size(_, 1).

add_size(T, N0, N) :- size(T, K), N is N0 + K.

reducible(L, _-'$='(_, A, B)) :- ( occurs(L, A) ; occurs(L, B) ), !.

normalised_all(_, _, [], [], M, M).
normalised_all(Fresh, Rules, [H0|Hs0], [H|Hs], M, M1) :-
  normalised(Fresh, Rules, H0, H, M, M0),
  normalised_all(Fresh, Rules, Hs0, Hs, M0, M1).

% X : T is Y : T1, in normal form: each rule E : L = R rewrites every occurrence of L, by a let
normalised(Fresh, Rules, X-T, H, M, M1) :-
  member(E-'$='(S, L, R), Rules),
  occurs(L, T), !,
  substitute(L, '$VAR'(Fresh), T, Motive),
  substitute(L, R, T, T0),
  M = let(Y, T0, rewrite('$VAR'(Fresh):S, Motive, E, X), M0),
  normalised(Fresh, Rules, Y-T0, H, M0, M1).
normalised(_, _, H, H, M, M).

% paramodulation: literals of the Into premise are either in the conclusion, or rewritten by an
% equation of (an instance of) the From premise, the rest of which is in the conclusion
paramodulate(Fresh, Hs, Premises, app(Into, Ts, Ms)) :-
  select(Into, Premises, [From]),
  premise(Into, Ts, Ks),
  maplist(paramodulate_literal(Fresh, Hs, From), Ks, Ms).

paramodulate_literal(_, Hs, _, K, M) :- matches(Hs, K, M).
paramodulate_literal(Fresh, Hs, From, K, lam(Y, K, app(From, Ts, Ms))) :-
  premise(From, Ts, Ls),
  append(Before, [Eq|After], Ls),
  Eq = '$='(_, _, _),
  rewrite_literal(Fresh, Hs, K, Y, E, Eq, Body),
  maplist(matches(Hs), Before, Ms0),
  maplist(matches(Hs), After, Ms1),
  append(Ms0, [lam(E, Eq, Body)|Ms1], Ms).

% equality factoring: as paramodulation, but the equation is a hypothesis for a literal A != B
equality_factor(Fresh, Hs, [Premise], app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ks),
  maplist(factor_literal(Fresh, Hs), Ks, Ms).

factor_literal(_, Hs, K, M) :- matches(Hs, K, M).
factor_literal(Fresh, Hs, K, lam(Y, K, app(H, [], [lam(E, Eq, Body)]))) :-
  member(H-(~(~Eq)), Hs),
  Eq = '$='(_, _, _),
  rewrite_literal(Fresh, Hs, K, Y, E, Eq, Body).

% Body : ⊥ from Y : K and E : A = B: K rewritten one way or the other is refuted by a hypothesis
rewrite_literal(Fresh, Hs, K, Y, E, Eq, Body) :-
  orientation(Eq, E, Sort, L, R, Equation),
  member(X-(~K1), Hs),
  ( Target = K1 ; flip(K1, Target) ),
  rewritten(K, Target, rw(Sort, L, R), '$VAR'(Fresh), Motive),
  refutes(~K1, X, Target, M),
  applied(M, rewrite('$VAR'(Fresh):Sort, Motive, Equation, Y), Body).

orientation('$='(S, A, B), E, S, A, B, E).
orientation('$='(S, A, B), E, S, B, A, app('$sym', [S, A, B], [E])).

% literal K becomes K1 by rewriting L to R, of sort S, at some occurrences, which are Z in Motive;
% rewrites are only where the sort is S (a variable side would otherwise unify with any term), which
% the signature gives for each argument; type arguments are never rewritten
rewritten(~A, ~A1, Rw, Z, ~Motive) :- !, rewritten_atom(A, A1, Rw, Z, Motive).
rewritten(A, A1, Rw, Z, Motive) :- A1 \= ~_, rewritten_atom(A, A1, Rw, Z, Motive).

rewritten_atom(A, A1, Rw, Z, Motive) :-
  nonvar(A),
  A1 =.. [P|Us1],
  A =.. [P|Us],
  instance(A, Types, _, Ss, _),
  rewritten_arguments(Types, Ss, Rw, Z, Us, Us1, Vs),
  Motive =.. [P|Vs].

% the arguments: the type arguments Types are left as they are, and the others, of sorts Ss, rewritten
rewritten_arguments([], Ss, Rw, Z, Us, Us1, Vs) :- maplist(rewritten_term(Rw, Z), Ss, Us, Us1, Vs).
rewritten_arguments([_|Types], Ss, Rw, Z, [U|Us], [U1|Us1], [U|Vs]) :-
  unify_with_occurs_check(U, U1),
  rewritten_arguments(Types, Ss, Rw, Z, Us, Us1, Vs).

% U of sort S becomes U1, as V in the motive
rewritten_term(_, _, _, U, U1, U) :- U == U1, !.
rewritten_term(rw(Sort, L, R), Z, S, U, U1, Z) :-
  unify_with_occurs_check(S, Sort),
  unify_with_occurs_check(U, L),
  unify_with_occurs_check(U1, R).
rewritten_term(_, _, _, U, U1, U1) :- var(U), unify_with_occurs_check(U, U1).
rewritten_term(Rw, Z, _, U, U1, V) :-
  nonvar(U),
  compound(U1),
  U1 =.. [F|Us1],
  U =.. [F|Us],
  instance(U, Types, _, Ss, _),
  rewritten_arguments(Types, Ss, Rw, Z, Us, Us1, Vs),
  V =.. [F|Vs].

% definition unfolding: every occurrence of a defined symbol in the clause is replaced, innermost
% first, each by one rewrite with an instance of its definition; the instances are opened outermost,
% once each, so that every literal can use them
unfold(Fresh, Hs, [Clause|Definitions], M) :-
  sort(Definitions, Ds),
  maplist(definiendum, Ds, Defs),
  premise(Clause, Ts, Ks),
  foldl(unfold_literal(ctx('$VAR'(Fresh), Defs), Hs), Ks, Ms, [], Instances),
  foldl(opened, Instances, app(Clause, Ts, Ms), M).

% a unit definition f(X_1, ..., X_n) = body, or body = f(X_1, ..., X_n), defines f/n
definiendum(D, def(D, F/N, Side)) :-
  premise(D, _, ['$='(_, A, B)]),
  ( Side = left, Def = A ; Side = right, Def = B ),
  pattern(Def),
  functor(Def, F, N).

% definition folding replaces each instance of the body of a function definition sF(Xs) = body by
% sF(...): it is proved the other way round, from the conclusion, whose hypothesis for each folded
% literal is unfolded until it refutes the premise's. Folded terms can be large, with many occurrences
% of each instance, so each instance is unfolded by one rewrite, at every occurrence at once
fold(Fresh, Hs, [Clause|Definitions], M) :-
  sort(Definitions, Ds),
  maplist(folded_symbol, Ds, Defs),
  premise(Clause, Ts, Ks),
  foldl(fold_literal(ctx('$VAR'(Fresh), Defs), Hs), Ks, Ms, [], Instances),
  foldl(opened, Instances, app(Clause, Ts, Ms), M).

% the side of the definition that is a symbol introduced by definition
folded_symbol(D, def(D, F/N, Side)) :-
  premise(D, _, ['$='(_, A, B)]),
  ( Side = left, Def = A ; Side = right, Def = B ),
  pattern(Def),
  functor(Def, F, N),
  introduced(F, definition), !.

% premise literal K is refuted by M, as it is, or by the hypothesis X : ~K1 of a conclusion literal,
% unfolded to ~K (or its flip). Each rewrite states the literal, so a large K (as in SWV545-1.010)
% is not attempted: the proof would be too large to print
fold_literal(_, Hs, K, M, Is, Is) :- matches(Hs, K, M).
fold_literal(Ctx, Hs, K, M, Is0, Is) :-
  nodes_within(K, 100000, _),
  member(X-(~K1), Hs),
  unfold_all(K1, Ctx, K2, [], Steps, Is0, Is),
  Steps \== [],
  Ctx = ctx(Z, _),
  chain(Steps, Z, X, W),
  (   unify_with_occurs_check(K2, K)
  ->  M = W
  ;   flip(K2, K3),
      unify_with_occurs_check(K3, K),
      M = let(Y, ~K2, W, M1),
      flipped(K, Y, M1)
  ).

% T has at most N0 nodes, N0 - N of them
nodes_within(T, N0, N) :- N0 > 0, N1 is N0 - 1, ( compound(T) -> T =.. [_|Ts], foldl(nodes_within, Ts, N1, N) ; N = N1 ).

% T becomes T1 as each defined term in it is replaced by its body, at every occurrence, outermost first
unfold_all(T, Ctx, T1, Steps0, Steps, Is0, Is) :-
  Ctx = ctx(Z, Defs),
  (   subterm(T, U), functor(U, F, N), memberchk(def(D, F/N, Side), Defs)
  ->  premise(D, Us, [Eq]),
      Eq = '$='(Sort, _, _),
      oriented(Side, Eq, E, U, Body, Equation),
      substitute(U, Z, T, Motive),
      substitute(Z, Body, Motive, T0),
      opening(D, Us, Eq, E, Is0, Is1),
      unfold_all(T0, Ctx, T1, [step(Sort, ~Motive, Equation)|Steps0], Steps, Is1, Is)
  ;   T1 = T, Steps = Steps0, Is = Is0
  ).

% f(X_1, ..., X_n) with distinct variables
pattern(T) :-
  nonvar(T),
  T =.. [_|Xs],
  maplist(var, Xs),
  sort(Xs, Ys),
  same_length(Xs, Ys).

opened(instance(D, Us, Equation, E), M, app(D, Us, [lam(E, Equation, M)])).

% literal K is unfolded by a chain of rewrites, from Y : K, and refuted by a hypothesis
unfold_literal(Ctx, Hs, K, M, Is0, Is) :-
  unfold_atom(K, Ctx, K1, []-Is0, Steps-Is),
  (   Steps == []
  ->  matches(Hs, K, M)
  ;   M = lam(Y, K, Body),
      Ctx = ctx(Z, _),
      chain(Steps, Z, Y, W),
      member(X-(~K2), Hs),
      ( Target = K2 ; flip(K2, Target) ),
      unify_with_occurs_check(K1, Target),
      refutes(~K2, X, Target, Refutation),
      applied(Refutation, W, Body)
  ).

% the rewrites, most recent first, applied to Y
chain([], _, Y, Y).
chain([step(Sort, Motive, Equation)|Steps], Z, Y, rewrite(Z:Sort, Motive, Equation, W)) :-
  chain(Steps, Z, Y, W).

% the arguments of the atom are unfolded; frames(F, Done, Rest) record the context of the subterm
% being unfolded, from the inside out, with its unfolded left siblings Done (reversed) and the rest;
% type arguments are left as they are
unfold_atom(~A, Ctx, ~A1, S0, S) :- !, unfold_arguments(A, Ctx, [frame(~, [], [])], A1, S0, S).
unfold_atom(A, Ctx, A1, S0, S) :- unfold_arguments(A, Ctx, [], A1, S0, S).

unfold_arguments(T, Ctx, Frames, T1, S0, S) :-
  T =.. [F|As],
  type_arity(T, N),
  length(Types, N),
  append(Types, Us, As),
  reverse(Types, Done),
  unfold_list(Us, F, Done, Ctx, Frames, Vs, S0, S),
  append(Types, Vs, Bs),
  T1 =.. [F|Bs].

unfold_list([], _, _, _, _, [], S, S).
unfold_list([A|As], F, Done, Ctx, Frames, [B|Bs], S0, S) :-
  unfold_term(A, Ctx, [frame(F, Done, As)|Frames], B, S0, S1),
  unfold_list(As, F, [B|Done], Ctx, Frames, Bs, S1, S).

% innermost first: the arguments, then the term itself, whose body is unfolded again
unfold_term(T, _, _, T, S, S) :- var(T), !.
unfold_term(T, Ctx, Frames, T1, S0, S) :-
  unfold_arguments(T, Ctx, Frames, T0, S0, S1),
  Ctx = ctx(_, Defs),
  (   functor(T0, F, N), member(def(D, F/N, Side), Defs)
  ->  unfolded(D, Side, T0, Ctx, Frames, Body, S1, S2),
      unfold_term(Body, Ctx, Frames, T1, S2, S)
  ;   T1 = T0, S = S1
  ).

% T is replaced by Body, with an instance of definition D: a step with the motive of the frames,
% and the instance, unless the same one is already open
unfolded(D, Side, T, ctx(Z, _), Frames, Body, Steps-Is0, [step(Sort, Motive, Equation)|Steps]-Is) :-
  premise(D, Us, [Eq]),
  Eq = '$='(Sort, _, _),
  oriented(Side, Eq, E, T, Body, Equation),
  plug(Frames, Z, Motive),
  opening(D, Us, Eq, E, Is0, Is).

oriented(left, '$='(_, A, B), E, A, B, E).
oriented(right, '$='(S, A, B), E, B, A, app('$sym', [S, A, B], [E])).

% an instance of definition D is opened once
opening(D, Us, _, E, Is, Is) :- member(instance(D, Vs, _, E), Is), Vs == Us, !.
opening(D, Us, Equation, E, Is, [instance(D, Us, Equation, E)|Is]).

% the term with X in the context of the frames
plug([], T, T).
plug([frame(F, Done, Rest)|Frames], X, T) :-
  reverse(Done, Left),
  append(Left, [X|Rest], As),
  U =.. [F|As],
  plug(Frames, U, T).

% reverse unit propagation (see rup.pl) over ground premises: premises with variables are ignored,
% which is enough for Vampire's rat, over AVATAR's propositional clauses
rup(_, Hs, Premises, M) :-
  findall(P-Ls, (member(P, Premises), premise(P, [], Ls)), Clauses),
  rup(Hs, Clauses, M).

% AVATAR component clause: C | ~split, where split is defined as C
avatar_component(_, Hs, [_], app(H, [], [lam(D, Split, app(D, Ts, Ms))])) :-
  select(H-(~(~Split)), Hs, Others),
  split(Split, clause(Bs, Ls)),
  binder_variables(Bs, Ts),
  maplist(matches(Others), Ls, Ms).
% ...or ~L | split, where split is defined as L: the definition is proved from two hypotheses,
% Y : ~T and X : T
avatar_component(Fresh, Hs, [_], app(H, [], [Intro])) :-
  select(H-(~Split), Hs, Others),
  intro(Split, Fresh, _, Others, All, app(Y, [], [X]), Intro),
  member(Y-(~T), All),
  member(X-U, All),
  U == T.

% Intro proves the definition of Split by M, with eigenvariables from Fresh0 and hypotheses for its literals
intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro) :-
  split(Split, clause(Bs, Ls)),
  binder_variables(Bs, Xs),
  number_vars(Xs, Fresh0, Fresh),
  hypotheses(Ls, Gs),
  append(Gs, Hs, Hs1),
  binders(Bs, Gs, Binders),
  lambdas(Binders, M, Intro).

% AVATAR split clause: split_1 | ... | split_n from the premise C_1 | ... | C_n
avatar_split(Fresh, Hs, [Premise|_], M) :-
  splits(Hs, Fresh, Hs, [], Premise, M).

splits([], _, Hs, Ds, Premise, app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(split_literal(Hs, Ds), Ls, Ms).
splits([H-(~(~Split))|Rest], Fresh, Hs, Ds, Premise, M) :-
  split(Split, Clause),
  splits(Rest, Fresh, Hs, [H-Split-Clause|Ds], Premise, M).
splits([H-(~Split)|Rest], Fresh0, Hs, Ds, Premise, app(H, [], [Intro])) :-
  intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro),
  splits(Rest, Fresh, Hs1, Ds, Premise, M).

% a premise literal is refuted by a hypothesis, or by a ground unit definition, from H : ~~split
split_literal(Hs, _, L, M) :- matches(Hs, L, M).
split_literal(_, Ds, L, lam(X, L, app(H, [], [lam(D, Split, app(D, [], [M]))]))) :-
  member(H-Split-clause([], [K]), Ds),
  matches([X-L], K, M).
