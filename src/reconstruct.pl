/*
Reconstruct steps into ir_step/3 facts using generic tactics (see ir.pl for the IR).

Tactics search for a refutation term R of the conclusion clause. They work with
hypotheses Hs, a list of H-L pairs where H is the name of a hypothesis that literal L is false.
Premise instances are found by unification with the (ground) conclusion, Prolog's
backtracking performing the search.
*/
:- module(reconstruct, [reconstruct/0]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

% reconstruct everything required for the last refutation
reconstruct :-
  findall(Name, step(Name, clause([], []), _), Refutations),
  last(Refutations, Refutation),
  prove(Refutation).

prove(Name) :- ir_step(Name, _, _), !.
prove(Name) :-
  step(Name, Conclusion, How),
  justify(How, Conclusion, Justification),
  assertz(ir_step(Name, Conclusion, Justification)).

justify(input(Role, Source), _, input(Role, Source)).
justify(split_def(Symbol, Clause), _, split_def(Symbol, Clause)) :- assertz(split(Symbol, Clause)).
justify(todo(Record, Parents), _, todo(Record, Parents)) :- maplist(prove, Parents).
justify(tactic(Tactic, Parents), Conclusion, Justification) :-
  maplist(prove, Parents),
  (   Conclusion = clause(Xs, Ls),
      hypotheses(Ls, 0, Hs),
      length(Xs, Fresh),
      call_tactic(Tactic, Fresh, Hs, Parents, R)
  ->  length(Ls, N),
      name_binders(R, N, _),
      term_variables(R, Unused),
      maplist(=('$any'), Unused),
      Justification = refute(R)
  ;   format(user_error, "warning: ~w failed to reconstruct ~w~n", [Tactic, Conclusion]),
      Justification = todo(Tactic, Parents)
  ).

call_tactic(Tactic, Fresh, Hs, Parents, R) :-
  Goal =.. [Tactic, Fresh, Hs, Parents, R],
  call(Goal), !.

hypotheses([], _, []).
hypotheses([L|Ls], N, [h(N)-L|Hs]) :- M is N + 1, hypotheses(Ls, M, Hs).

% binders are variables during search: give them names h(N), h(N + 1), ...
name_binders(V, N0, N) :- var(V), !, N = N0.
name_binders(use(_, _, As), N0, N) :- !, name_binders_list(As, N0, N).
name_binders(let(H, _, A, R), N0, N) :- !, bind(H, N0, N1), name_binders(A, N1, N2), name_binders(R, N2, N).
name_binders(contra(_, P), N0, N) :- !, name_binders(P, N0, N).
name_binders(intro(_, Hs, R), N0, N) :- !, name_list(Hs, N0, N1), name_binders(R, N1, N).
name_binders(hyp(_), N, N) :- !.
name_binders(sym(A), N0, N) :- !, name_binders(A, N0, N).
name_binders(assume(H, R), N0, N) :- !, bind(H, N0, N1), name_binders(R, N1, N).
name_binders(unfold(H, R), N0, N) :- !, bind(H, N0, N1), name_binders(R, N1, N).

name_binders_list([], N, N).
name_binders_list([A|As], N0, N) :- name_binders(A, N0, N1), name_binders_list(As, N1, N).

bind(H, N0, N) :- H = h(N0), N is N0 + 1.

name_list([], N, N).
name_list([H|Hs], N0, N) :- bind(H, N0, N1), name_list(Hs, N1, N).

/********************************************************************************
 * literal matching
 ********************************************************************************/

% a hypothesis refutes premise literal L, modulo symmetry of equality
matches(Hs, L, Arg) :-
  member(H-K, Hs),
  oriented(K, L, hyp(H), Arg).

oriented(K, L, Arg, Arg) :- unify_with_occurs_check(K, L).
oriented(K, L, Arg, sym(Arg)) :- flip(K, F), unify_with_occurs_check(F, L).

premise(Name, Ts, Ls) :-
  ir_step(Name, Clause, _),
  Clause = clause(_, _),
  fresh_instance(Clause, Ts, Ls).

/********************************************************************************
 * tactics: tactic(Fresh, Hypotheses, Parents, Refutation)
 * Fresh is the next available '$VAR' index, for eigenvariables
 ********************************************************************************/

% the conclusion is an instance of the premise, modulo symmetry, factoring and duplicates
variant(_, Hs, [Premise], use(Premise, Ts, Args)) :-
  premise(Premise, Ts, Ls),
  maplist(matches(Hs), Ls, Args).

% binary resolution: literals of the major premise are either in the conclusion,
% or refuted by (an instance of) the minor premise
resolve(_, Hs, Premises, use(Major, Ts, Args)) :-
  select(Major, Premises, [Minor]),
  premise(Major, Ts, Ks),
  maplist(resolve_literal(Hs, Minor), Ks, Args).

resolve_literal(Hs, _, K, Arg) :- matches(Hs, K, Arg).
resolve_literal(Hs, Minor, K, assume(H, use(Minor, Ts, Args))) :-
  complement(K, C),
  premise(Minor, Ts, Ls),
  maplist(matches([H-C|Hs]), Ls, Args).

% reverse unit propagation over ground clauses
% the trail maps literals to hypotheses that they are false
% propagation is confluent, so commit to each unit found:
% when a literal becomes false, (re)check the clauses in which it occurs
rup(_, Hs, Premises, R) :-
  findall(P-Ls, (member(P, Premises), premise(P, [], Ls)), Clauses),
  empty_assoc(Empty),
  foldl(trail, Hs, Empty, Trail),
  foldl(occurrences, Clauses, Empty, Occurrences),
  propagate(Clauses, Occurrences, Trail, R).

trail(H-L, Trail0, Trail) :- put_assoc(L, Trail0, H, Trail).

occurrences(P-Ls, Occurrences0, Occurrences) :- foldl(occurrence(P-Ls), Ls, Occurrences0, Occurrences).

occurrence(Clause, L, Occurrences0, Occurrences) :-
  ( get_assoc(L, Occurrences0, Cs) -> true ; Cs = [] ),
  put_assoc(L, Occurrences0, [Clause|Cs], Occurrences).

% propagate(Queue, Occurrences, Trail, R): fails if the queue empties without conflict
propagate([P-Ls|Queue], Occurrences, Trail, R) :-
  (   unit(Trail, Ls, Unit, Args),
      ( var(Unit) -> true ; Unit = L-_, complement(L, C), \+ get_assoc(C, Trail, _) )
  ->  (   var(Unit)
      ->  R = use(P, [], Args)
      ;   Unit = _-H,
          R = let(G, C, assume(H, use(P, [], Args)), R1),
          put_assoc(C, Trail, G, Trail1),
          ( get_assoc(C, Occurrences, Cs) -> append(Cs, Queue, Queue1) ; Queue1 = Queue ),
          propagate(Queue1, Occurrences, Trail1, R1)
      )
  ;   propagate(Queue, Occurrences, Trail, R)
  ).

% all literals but (at most) one Unit are false according to Trail
unit(_, [], _, []).
unit(Trail, [L|Ls], Unit, [hyp(H)|Args]) :-
  ( get_assoc(L, Trail, H) -> true ; Unit = L-H ),
  unit(Trail, Ls, Unit, Args).

% AVATAR component clause: C | ~split, where split is defined as C
avatar_component(_, Hs, [_], contra(H, unfold(D, use(D, Ts, Args)))) :-
  select(H-(~Split), Hs, Others),
  split_def(Split, Clause),
  fresh_instance(Clause, Ts, Ls),
  maplist(matches(Others), Ls, Args).
% ...or ~L | split, where split is defined as L
avatar_component(Fresh, Hs, [_], contra(H, intro(Xs, Gs, R))) :-
  select(H-Split, Hs, Others),
  split_def(Split, Clause),
  eigenvariables(Clause, Fresh, _, Xs, Ls),
  hypotheses_for(Ls, Gs, GHs),
  append(GHs, Others, All),
  mate(All, R).

% two hypotheses refute complementary literals
mate(Hs, contra(H, hyp(G))) :-
  member(H-(~A), Hs),
  member(G-B, Hs),
  B == A.

% AVATAR split clause: split_1 | ... | split_n from the premise C_1 | ... | C_n
avatar_split(Fresh, Hs, [Premise|_], R) :-
  splits(Hs, Fresh, Hs, [], Premise, R).

splits([], _, Hs, Ds, Premise, use(Premise, Ts, Args)) :-
  premise(Premise, Ts, Ls),
  maplist(split_literal(Hs, Ds), Ls, Args).
splits([H-(~Split)|Rest], Fresh, Hs, Ds, Premise, contra(H, unfold(D, R))) :-
  split_def(Split, Clause),
  splits(Rest, Fresh, Hs, [D-Clause|Ds], Premise, R).
splits([H-Split|Rest], Fresh0, Hs, Ds, Premise, contra(H, intro(Xs, Gs, R))) :-
  split_def(Split, Clause),
  eigenvariables(Clause, Fresh0, Fresh, Xs, Ls),
  hypotheses_for(Ls, Gs, GHs),
  append(GHs, Hs, Hs1),
  splits(Rest, Fresh, Hs1, Ds, Premise, R).

% a premise literal is refuted by a hypothesis, or by a ground unit definition
split_literal(Hs, _, L, Arg) :- matches(Hs, L, Arg).
split_literal(_, Ds, L, assume(G, use(D, [], [Arg]))) :-
  member(D-clause([], [K]), Ds),
  complement(L, C),
  oriented(C, K, hyp(G), Arg).

eigenvariables(Clause, Fresh0, Fresh, Xs, Ls) :-
  Clause = clause(Ys, _),
  length(Ys, N),
  length(Xs, N),
  number_vars(Xs, Fresh0, Fresh),
  instance(Clause, Xs, Ls).

hypotheses_for([], [], []).
hypotheses_for([L|Ls], [G|Gs], [G-L|GHs]) :- hypotheses_for(Ls, Gs, GHs).
