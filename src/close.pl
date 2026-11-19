/*
Closing a proof term after search, so that it is ground (see ir.pl):

  - term and type variables left unconstrained by search become some term of their sort S (the
    sort of types is '$tType'), or else '$inhabited'(S), an arbitrary individual of S;
  - binders, Prolog variables during search, are named h(0), h(1), ..., in binder order.

Every variable comes from the binders of some instance app(F, Ts, _), of a step, a split definition
or a built-in, so its sort is that of its binder. Type variables are closed first, so that the sorts
of the others are then ground.

The term is the first of: an eigenvariable in scope, a constant of the signature, or a function of
the signature applied to these. A variable is closed where it is first instantiated, outermost
first, so it must not also occur outside the scope of the eigenvariables there: the tactics only
instantiate premises under all of their eigenvariables.

'$inhabited' assumes that every sort is inhabited, as classical first-order logic (and TF1) does.
Back ends decide what it stands for: a constructive back end (Agda, say) may not assume this.
*/
:- module(close, [close_term/1, name_binders/3]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).

close_term(M) :-
  instances([], _, M, Holes, []),
  maplist(close_type, Holes),
  maplist(close_variable, Holes),
  name_binders(M, 0, _).

close_type(hole(Env, X, S)) :- S == '$tType', var(X), !, inhabitant(Env, S, X).
close_type(_).

close_variable(hole(Env, X, S)) :- var(X), !, inhabitant(Env, S, X).
close_variable(_).

% T is of the ground sort S: the smallest term found, or else an arbitrary individual
inhabitant(Env, S, T) :- member(Depth, [0, 1, 2]), small_term(Depth, Env, S, T0), !, T = T0.
inhabitant(_, S, '$inhabited'(S)).

% a term of sort S, one at a time: an eigenvariable of Env, or a symbol of the signature applied to
% such terms, nested to at most Depth
small_term(_, Env, S, X) :- member(X-S0, Env), nonvar(X), S0 == S.
small_term(Depth, Env, S, T) :-
  Depth > 0,
  Depth1 is Depth - 1,
  symbol(F, Params, Sorts, S0),
  % a symbol of polymorphic sort is of any sort, but is not a type
  ( S == '$tType' -> S0 == S ; S0 = S ),
  maplist(parameter(Depth1, Env), Params),
  maplist(argument(Depth1, Env), Sorts, Us),
  append(Params, Us, As),
  T =.. [F|As].

% a type parameter that the sort leaves open is any type, which the arguments may depend on
parameter(_, _, P) :- nonvar(P), !.
parameter(Depth, Env, P) :- small_term(Depth, Env, '$tType', P).

% any argument will do, as nothing depends on it
argument(Depth, Env, S, U) :- small_term(Depth, Env, S, U), !.

% a hole(Env, X, S) for each binder X : S of the instances in M, with X unified with the term
% instantiating it; Env holds the types of the λ and let binders in scope, as X-T, where a
% hypothesis X is still a variable and an eigenvariable is not. T is the type of M, if known: a
% binder annotated '$inferred' takes its type from it
instances(_, _, V) --> { var(V) }, !.
instances(Env, T, lam(X, A, M)) --> !, { abstraction(T, X, A, A1, T1) }, instances([X-A1|Env], T1, M).
instances(Env, _, let(X, F, M, M1)) --> !, instances(Env, F, M), instances([X-F|Env], _, M1).
instances(Env, _, rewrite(_, _, E, M)) --> !, instances(Env, _, E), instances(Env, _, M).
instances(Env, _, app(F, Ts, Ms)) --> !,
  { instance_binders(Env, F, Ts, Bs), maplist(hole(Env), Bs, Holes), argument_types(Env, F, Ms, Types) },
  list(Holes),
  foldl(instances(Env), Types, Ms).
instances(_, _, _) --> [].

% λ X : A of type T has the binder X : A1, and the body of type T1
abstraction(T, X, _, S, T1) :- nonvar(T), T = '!'([Y:S|Bs], B), !, substitute(Y, X, Bs-B, Bs1-B1), quantified(Bs1, B1, T1).
abstraction(T, _, _, A, B) :- nonvar(T), T = (A => B), !.
abstraction(T, _, _, A, '$false') :- nonvar(T), T = ~A, !.
abstraction(_, _, A, A, _).

quantified([], B, B) :- !.
quantified(Bs, B, '!'(Bs, B)).

% the types of the arguments Ms of F, where known: those of an expansion rule follow from the type of
% its first argument, a hypothesis, and those of a hypothesis that is not quantified from its type
argument_types(Env, F, Ms, Types) :-
  same_length(Ms, Types),
  ( known_types(Env, F, Ms, Types) -> true ; true ).

known_types(Env, Rule, [M|Ms], [T0|Ts]) :-
  atom(Rule),
  rule_type(Rule, _, _), !,
  var(M),
  typed(Env, M, T0),
  rule_type(Rule, T0, T1),
  premises(Ms, T1, Ts).
known_types(Env, X, Ms, Ts) :-
  var(X),
  typed(Env, X, T),
  T \= '!'(_, _),
  premises(Ms, T, Ts).

typed(Env, X, T) :- member(Y-T, Env), Y == X, !, nonvar(T), T \== '$inferred'.

premises([], _, []).
premises([_|Ms], (A => B), [A|Ts]) :- !, premises(Ms, B, Ts).
premises([_|Ms], ~A, [A|Ts]) :- !, premises(Ms, '$false', Ts).
premises([_|Ms], _, [_|Ts]) :- premises(Ms, '$false', Ts).

hole(Env, X:S, hole(Env, X, S)).

% a ground instance has nothing to close (as a choice axiom's, see transform.pl)
instance_binders(_, _, Ts, []) :- ground(Ts), !.
instance_binders(Env, F, Ts, Bs) :-
  member(X-T, Env),
  X == F,
  nonvar(T),
  T = '!'(Bs0, _), !,
  instantiated(Bs0, Ts, Bs).
instance_binders(Env, F, Ts, Bs) :- head_binders(Env, F, Bs), !, binder_variables(Bs, Ts).
instance_binders(_, F, Ts, _) :-
  warn(['error: no binders for the instance ', Ts, ' of ', F]),
  fail.

% the binders of a quantified hypothesis, instantiated by Ts: the sort of each may depend on the
% terms before it
instantiated([], [], []).
instantiated([X:S|Bs0], [T|Ts], [T:S|Bs]) :- substitute(X, T, Bs0, Bs1), instantiated(Bs1, Ts, Bs).

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
