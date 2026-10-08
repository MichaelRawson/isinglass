/*
Reconstruct steps into ir_step/3 facts by searching for proof terms (see ir.pl for the IR).

The search procedures below are given hypotheses Hs, a list of X-T pairs where X : T is a
variable, and build a term of type ⊥, which is then abstracted over the conclusion and elaborated
by ir:elaborate/2. During search, binders are Prolog variables, and are named h(N) afterwards;
binder types are left as variables, for elaboration to fill in.
Clauses are stored with Prolog variables (db.pl), so retrieving a premise gives a fresh instance.
The conclusion is made rigid by numbering its variables, and premise instances are found by
unification with it, Prolog's backtracking performing the search.
*/
:- module(reconstruct, [reconstruct/0]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(ir).

% reconstruct everything required for the last refutation
reconstruct :-
  forall(step(_, _, split_def(Symbol, Clause)), assertz(split(Symbol, Clause))),
  findall(Name, step(Name, clause([], []), _), Refutations),
  last(Refutations, Refutation),
  prove(Refutation).

prove(Name) :- ir_step(Name, _, _), !.
prove(Name) :-
  step(Name, Conclusion, How),
  rigid(Conclusion, Fresh),
  justify(How, Conclusion, Fresh, Justification),
  assertz(ir_step(Name, Conclusion, Justification)).

% number the variables of a conclusion, in binder order; Fresh is the next index
rigid(clause(Xs, _), Fresh) :- number_vars(Xs, 0, Fresh).
rigid(formula(F), Fresh) :- term_variables(F, Vs), number_vars(Vs, 0, Fresh).

justify(input(Role, Source), _, _, input(Role, Source)).
justify(split_def(Symbol, Clause), _, _, split_def(Symbol, Clause)).
justify(todo(Record, Parents), _, _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Fresh, Justification) :-
  maplist(prove, Parents),
  (   Conclusion = clause(Xs, Ls),
      hypotheses(Ls, Hs, Vs),
      call_tactic(Tactic, Fresh, Hs, Parents, Body)
  ->  append(Xs, Vs, Binders),
      lambdas(Binders, Body, M),
      close_term(M, 0, _),
      elaborated(Tactic, Conclusion, M),
      Justification = proof(M)
  ;   format(user_error, "warning: ~w failed to reconstruct ~w~n", [Tactic, Conclusion]),
      Justification = todo(Tactic, Parents)
  ).

% a term that fails to elaborate is a bug in the search
elaborated(_, Conclusion, M) :- elaborate(Conclusion, M), !.
elaborated(Tactic, Conclusion, _) :-
  format(user_error, "error: ~w reconstructed an incorrect proof of ~w~n", [Tactic, Conclusion]),
  fail.

call_tactic(Tactic, Fresh, Hs, Parents, M) :-
  Goal =.. [Tactic, Fresh, Hs, Parents, M],
  call(Goal), !.

% a hypothesis V : ~L for each literal L, with the variables Vs
hypotheses([], [], []).
hypotheses([L|Ls], [V-(~L)|Hs], [V|Vs]) :- hypotheses(Ls, Hs, Vs).

lambdas([], M, M).
lambdas([X|Xs], M, lam(X, _, N)) :- lambdas(Xs, M, N).

% after search, binders are named h(N), h(N + 1), ..., and unconstrained term variables become '$any'
% binder types are left to elaboration
close_term(V, N, N) :- var(V), !.
close_term(lam(X, _, M), N0, N) :- !, bind(X, N0, N1), close_term(M, N1, N).
close_term(let(X, _, M, M1), N0, N) :- !, bind(X, N0, N1), close_term(M, N1, N2), close_term(M1, N2, N).
close_term(app(_, Ts, Ms), N0, N) :- !,
  term_variables(Ts, Vs),
  maplist(=('$any'), Vs),
  foldl(close_term, Ms, N0, N).
close_term(_, N, N).

bind(X, N0, N) :- var(X), !, X = h(N0), N is N0 + 1.
bind(_, N, N).

/********************************************************************************
 * literal matching
 ********************************************************************************/

% a hypothesis refutes premise literal L, as M : ~L
matches(Hs, L, M) :-
  member(X-T, Hs),
  refutes(T, X, L, M).

% refutes(T, X, L, M): X : T refutes L as M, modulo symmetry of equality
refutes(~K, X, L, X) :- unify_with_occurs_check(K, L).
refutes(~K, X, L, M) :- flip(K, F), unify_with_occurs_check(F, L), flipped(L, X, M).
refutes(A, X, ~B, lam(K, _, app(K, [], [X]))) :- A \= ~_, unify_with_occurs_check(A, B).
refutes(S = T, X, ~B, lam(K, _, app(K, [], [app('$sym', [S, T], [X])]))) :- unify_with_occurs_check(T = S, B).

% X refutes L with the equation the other way round
flipped(S = T, X, lam(E, _, app(X, [], [app('$sym', [S, T], [E])]))).
flipped(~(S = T), X, lam(K, _, app(X, [], [lam(E, _, app(K, [], [app('$sym', [T, S], [E])]))]))).

% X : C refutes the complement of C, as M
assumption(~_, X, X) :- !.
assumption(_, X, lam(K, _, app(K, [], [X]))).

% a fresh instance of a premise clause, with variables Ts
premise(Name, Ts, Ls) :- step(Name, clause(Ts, Ls), _).

/********************************************************************************
 * search procedures: tactic(Fresh, Hypotheses, Parents, M)
 * Fresh is the next available '$VAR' index, for eigenvariables
 ********************************************************************************/

% the conclusion is an instance of the premise, modulo symmetry, factoring and duplicates
variant(_, Hs, [Premise], app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(matches(Hs), Ls, Ms).

% binary resolution: literals of the major premise are either in the conclusion,
% or refuted by (an instance of) the minor premise
% only positive literals are refuted by the minor: one resolved literal is positive, and either premise
% may be the major, so this is complete, and avoids an exponential search on wide negative clauses
resolve(_, Hs, Premises, app(Major, Ts, Ms)) :-
  select(Major, Premises, [Minor]),
  premise(Major, Ts, Ks),
  maplist(resolve_literal(Hs, Minor), Ks, Ms).

resolve_literal(Hs, _, K, M) :- matches(Hs, K, M).
resolve_literal(Hs, Minor, K, lam(X, _, app(Minor, Ts, Ms))) :-
  K \= ~_,
  premise(Minor, Ts, Ls),
  maplist(matches([X-K|Hs]), Ls, Ms).

% reverse unit propagation over ground clauses
% the trail maps literals L to variables of type ~L
% propagation is confluent, so commit to each unit found:
% when a literal becomes false, (re)check the clauses in which it occurs
rup(_, Hs, Premises, M) :-
  findall(P-Ls, (member(P, Premises), premise(P, [], Ls)), Clauses),
  empty_assoc(Empty),
  foldl(trail, Hs, Empty, Trail),
  foldl(occurrences, Clauses, Empty, Occurrences),
  propagate(Clauses, Occurrences, Trail, M).

trail(X-(~L), Trail0, Trail) :- put_assoc(L, Trail0, X, Trail).

occurrences(P-Ls, Occurrences0, Occurrences) :- foldl(occurrence(P-Ls), Ls, Occurrences0, Occurrences).

occurrence(Clause, L, Occurrences0, Occurrences) :-
  ( get_assoc(L, Occurrences0, Cs) -> true ; Cs = [] ),
  put_assoc(L, Occurrences0, [Clause|Cs], Occurrences).

% propagate(Queue, Occurrences, Trail, M): fails if the queue empties without conflict
propagate([P-Ls|Queue], Occurrences, Trail, M) :-
  (   unit(Trail, Ls, Unit, Ms),
      ( var(Unit) -> true ; Unit = L-_, complement(L, C), \+ get_assoc(C, Trail, _) )
  ->  (   var(Unit)
      ->  M = app(P, [], Ms)
      ;   Unit = _-A,
          assumption(C, X, A),
          M = let(G, ~C, lam(X, _, app(P, [], Ms)), M1),
          put_assoc(C, Trail, G, Trail1),
          ( get_assoc(C, Occurrences, Cs) -> append(Cs, Queue, Queue1) ; Queue1 = Queue ),
          propagate(Queue1, Occurrences, Trail1, M1)
      )
  ;   propagate(Queue, Occurrences, Trail, M)
  ).

% all literals but (at most) one Unit are false according to Trail
unit(_, [], _, []).
unit(Trail, [L|Ls], Unit, [M|Ms]) :-
  ( get_assoc(L, Trail, M) -> true ; Unit = L-M ),
  unit(Trail, Ls, Unit, Ms).

% AVATAR component clause: C | ~split, where split is defined as C
avatar_component(_, Hs, [_], app(H, [], [lam(D, _, app(D, Ts, Ms))])) :-
  select(H-(~(~Split)), Hs, Others),
  split_def(Split, clause(Ts, Ls)),
  maplist(matches(Others), Ls, Ms).
% ...or ~L | split, where split is defined as L
avatar_component(Fresh, Hs, [_], app(H, [], [Intro])) :-
  select(H-(~Split), Hs, Others),
  intro(Split, Fresh, _, Others, All, M, Intro),
  mate(All, M).

% two hypotheses Y : ~T and X : T
mate(Hs, app(Y, [], [X])) :-
  member(Y-(~T), Hs),
  member(X-U, Hs),
  U == T.

% Intro proves the definition of Split by M, with eigenvariables from Fresh0 and hypotheses for its literals
intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro) :-
  split_def(Split, clause(Xs, Ls)),
  number_vars(Xs, Fresh0, Fresh),
  hypotheses(Ls, Gs, Vs),
  append(Gs, Hs, Hs1),
  append(Xs, Vs, Binders),
  lambdas(Binders, M, Intro).

% AVATAR split clause: split_1 | ... | split_n from the premise C_1 | ... | C_n
avatar_split(Fresh, Hs, [Premise|_], M) :-
  splits(Hs, Fresh, Hs, [], Premise, M).

splits([], _, Hs, Ds, Premise, app(Premise, Ts, Ms)) :-
  premise(Premise, Ts, Ls),
  maplist(split_literal(Hs, Ds), Ls, Ms).
splits([H-(~(~Split))|Rest], Fresh, Hs, Ds, Premise, M) :-
  split_def(Split, Clause),
  splits(Rest, Fresh, Hs, [H-Clause|Ds], Premise, M).
splits([H-(~Split)|Rest], Fresh0, Hs, Ds, Premise, app(H, [], [Intro])) :-
  intro(Split, Fresh0, Fresh, Hs, Hs1, M, Intro),
  splits(Rest, Fresh, Hs1, Ds, Premise, M).

% a premise literal is refuted by a hypothesis, or by a ground unit definition, from H : ~~split
split_literal(Hs, _, L, M) :- matches(Hs, L, M).
split_literal(_, Ds, L, lam(X, _, app(H, [], [lam(D, _, app(D, [], [M]))]))) :-
  member(H-clause([], [K]), Ds),
  matches([X-L], K, M).
