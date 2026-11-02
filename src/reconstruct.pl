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
justify(split_def(Symbol, _), _, _, split_def(Symbol, Clause)) :- split(Symbol, Clause), rigid(Clause, _).
justify(negated_conjecture(Conjecture), _, _, negated_conjecture(Conjecture)).
justify(todo(Record, Parents), _, _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Fresh, Justification) :-
  maplist(prove, Parents),
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

% binary resolution: literals of the major premise are either in the conclusion,
% or refuted by (an instance of) the minor premise
% only positive literals are refuted by the minor: one resolved literal is positive, and either premise
% may be the major, so this is complete, and avoids an exponential search on wide negative clauses
resolve(_, Hs, Premises, app(Major, Ts, Ms)) :-
  select(Major, Premises, [Minor]),
  premise(Major, Ts, Ks),
  maplist(resolve_literal(Hs, Minor), Ks, Ms).

resolve_literal(Hs, _, K, M) :- matches(Hs, K, M).
resolve_literal(Hs, Minor, K, lam(X, K, app(Minor, Ts, Ms))) :-
  K \= ~_,
  premise(Minor, Ts, Ls),
  maplist(matches([X-K|Hs]), Ls, Ms).

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
