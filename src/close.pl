/*
Closing a proof term after search, so that it is ground (see ir.pl):

  - term variables left unconstrained by search become '$inhabited'(S), an arbitrary individual of
    their sort S, and type variables become '$inhabited'('$tType'), an arbitrary type;
  - binders, Prolog variables during search, are named h(0), h(1), ..., in binder order.

Every variable comes from the binders of some instance app(F, Ts, _), of a step, a split definition
or a built-in, so its sort is that of its binder. Type variables are closed first, so that the sorts
of the others are then ground.

'$inhabited' assumes that every sort is inhabited, as classical first-order logic (and TF1) does.
Back ends decide what it stands for. A constructive back end (Agda, say) may not assume this,
and could instead look for a closed term of the sort, e.g. a constant of the signature: that choice
belongs here.
*/
:- module(close, [close_term/1]).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).

close_term(M) :-
  phrase(instances([], M), Bs),
  maplist(inhabited_type, Bs),
  maplist(inhabited, Bs),
  name_binders(M, 0, _).

inhabited_type(X:S) :- S == '$tType', var(X), !, X = '$inhabited'('$tType').
inhabited_type(_).

inhabited(X:S) :- var(X), !, X = '$inhabited'(S).
inhabited(_).

% the binders X : S of the instances in M, with X unified with the term instantiating it; Env holds
% the types of the λ and let binders in scope, as X-T; a hypothesis is still a variable
instances(_, V) --> { var(V) }, !.
instances(Env, lam(X, T, M)) --> !, instances([X-T|Env], M).
instances(Env, let(X, F, M, M1)) --> !, instances(Env, M), instances([X-F|Env], M1).
instances(Env, rewrite(_, _, E, M)) --> !, instances(Env, E), instances(Env, M).
instances(Env, app(F, Ts, Ms)) --> !, { instance_binders(Env, F, Ts, Bs) }, Bs, foldl(instances(Env), Ms).
instances(_, _) --> [].

instance_binders(_, _, [], []) :- !.
instance_binders(Env, F, Ts, Bs) :- head_binders(Env, F, Bs), !, binder_variables(Bs, Ts).
instance_binders(_, F, Ts, _) :-
  format(user_error, "error: no binders for the instance ~w of ~w~n", [Ts, F]),
  fail.

% a step, a built-in, or a hypothesis whose type is a split symbol
head_binders(_, F, Bs) :- atom(F), step(F, clause(Bs, _), _), !.
head_binders(_, F, Bs) :- atom(F), builtin_type(F, '!'(Bs, _)), !.
head_binders(Env, F, Bs) :- member(X-T, Env), X == F, !, atom(T), split(T, clause(Bs, _)).

% a hypothesis is a variable until named, so the clauses below would bind it: hence the guard
name_binders(V, N, N) :- var(V), !.
name_binders(lam(X, _, M), N0, N) :- !, bind(X, N0, N1), name_binders(M, N1, N).
name_binders(let(X, _, M, M1), N0, N) :- !, bind(X, N0, N1), name_binders(M, N1, N2), name_binders(M1, N2, N).
name_binders(app(_, _, Ms), N0, N) :- !, foldl(name_binders, Ms, N0, N).
name_binders(rewrite(_, _, E, M), N0, N) :- !, name_binders(E, N0, N1), name_binders(M, N1, N).
name_binders(_, N, N).

% binders of eigenvariables are already named '$VAR'(N)
bind(X, N0, N) :- var(X), !, X = h(N0), N is N0 + 1.
bind(_, N, N).
