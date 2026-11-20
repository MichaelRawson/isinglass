/*
Closing a proof term after search, so that it is ground (see ir.pl):

  - term and type variables left unconstrained by search become some term of their sort S (the
    sort of types is '$tType'), or else '$inhabited'(S), an arbitrary individual of S;
  - binders still Prolog variables (those of hypotheses, during search) are variables '$VAR'(N),
    numbered in binder order after those already numbered (eigenvariables, rigid during search).

Every variable comes from the binders of some instance '$app'(F, Ts, _), of a step, a split definition
or a built-in, so its sort is that of its binder. Type variables are closed first, so that the sorts
of the others are then ground.

The term is the first of: an eigenvariable in scope, a constant of the signature, or a function of
the signature applied to these. A variable is closed where it is first instantiated, outermost
first, so it must not also occur outside the scope of the eigenvariables there: the tactics only
instantiate premises under all of their eigenvariables.

'$inhabited' assumes that every sort is inhabited, as classical first-order logic (and TF1) does.
Back ends decide what it stands for: a constructive back end (Agda, say) may not assume this.
*/
:- module(close, [close_term/1, number_binders/1]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).

close_term(M) :-
  instances([], _, M, Holes, []),
  maplist(close_type, Holes),
  maplist(close_variable, Holes),
  number_binders(M).

% the binders of M that are still Prolog variables are numbered after its variables already numbered
number_binders(M) :-
  first_unnumbered(M, N),
  name_binders(M, N, _).

% the number after those of the variables of M
first_unnumbered(M, N) :-
  findall(I, ( subterm(M, '$VAR'(I)), integer(I) ), Is),
  max_list([-1|Is], Max),
  N is Max + 1.

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
% instantiating it; Env holds the types of the λ binders in scope, as X-T, where a
% hypothesis X is still a variable and an eigenvariable is not. T is the type of M, if known: a
% binder annotated '$inferred' takes its type from it
instances(_, _, V) --> { var(V) }, !.
instances(Env, T, '$lam'(X, A, M)) --> !, { abstraction(T, X, A, A1, T1) }, instances([X-A1|Env], T1, M).
% a redex: each λ takes an argument, of the type of its binder (a hypothesis at the head is a variable)
instances(Env, T, '$app'(L, [], [M|Ms])) --> { nonvar(L), L = '$lam'(X, F, N) }, !,
  instances(Env, F, M),
  { ( Ms == [] -> N1 = N, T1 = T ; N1 = '$app'(N, [], Ms) ) },
  instances([X-F|Env], T1, N1).
instances(Env, _, '$rewrite'(_, _, E, M)) --> !, instances(Env, _, E), instances(Env, _, M).
instances(Env, _, '$app'(F, Ts, Ms)) --> !,
  { instance_binders(Env, F, Ts, Bs), maplist(hole(Env), Bs, Holes), argument_types(Env, F, Ms, Types) },
  list(Holes),
  foldl(instances(Env), Types, Ms).
instances(_, _, _) --> [].

% λ X : A of type T has the binder X : A1, and the body of type T1
abstraction(T, X, _, A1, T1) :- nonvar(T), T = '$proof'(F), nonvar(F), proof_abstraction(F, X, A1, T1), !.
abstraction(_, _, A, A, _).

proof_abstraction('!'(Y:S, B), X, S, '$proof'(B1)) :- substitute(Y, X, B, B1).
proof_abstraction((A => B), _, '$proof'(A), '$proof'(B)).
proof_abstraction(~A, _, '$proof'(A), '$proof'('$false')).

% the types of the arguments Ms of F, where known: those of an expansion rule follow from the type of
% its first argument, a hypothesis, and those of a hypothesis that is not quantified from its type
argument_types(Env, F, Ms, Types) :-
  same_length(Ms, Types),
  ( known_types(Env, F, Ms, Types) -> true ; true ).

known_types(Env, Rule, [M|Ms], ['$proof'(F0)|Ts]) :-
  atom(Rule),
  inferred_premise(Rule), !,
  var(M),
  typed(Env, M, '$proof'(F0)),
  head_type(Rule, '$proof'((F0 => F1))),
  premises(Ms, F1, Ts).
known_types(Env, X, Ms, Ts) :-
  var(X),
  typed(Env, X, '$proof'(F)),
  F \= '!'(_, _),
  premises(Ms, F, Ts).

typed(Env, X, T) :- member(Y-T, Env), Y == X, !, nonvar(T), T = '$proof'(F), nonvar(F).

% the proof types of the arguments Ms of a proof of formula F, where known
premises([], _, []).
premises([_|Ms], (A => B), ['$proof'(A)|Ts]) :- !, premises(Ms, B, Ts).
premises([_|Ms], ~A, ['$proof'(A)|Ts]) :- !, premises(Ms, '$false', Ts).
premises([_|Ms], _, [_|Ts]) :- premises(Ms, '$false', Ts).

hole(Env, X:S, hole(Env, X, S)).

% a ground instance has nothing to close (as a choice axiom's, see transform.pl)
instance_binders(_, _, Ts, []) :- ground(Ts), !.
instance_binders(Env, F, Ts, Bs) :-
  member(X-T, Env),
  X == F,
  nonvar(T),
  T = '$proof'(G),
  length(Ts, N),
  quantifier_prefix('!', N, G, Bs0, _), !,
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
head_binders(_, F, Bs) :- atom(F), head_type(F, '$proof'(T)), quantifier_prefix('!', T, Bs, _), Bs = [_|_], !.
head_binders(Env, F, Bs) :- member(X-T, Env), X == F, !, T = '$proof'(A), atom(A), split(A, clause(Bs, _)).

% a hypothesis is a variable until named, so the clauses below would bind it: hence the guard
name_binders(V, N, N) :- var(V), !.
name_binders('$lam'(X, _, M), N0, N) :- !, bind(X, N0, N1), name_binders(M, N1, N).
name_binders('$app'(L, _, Ms), N0, N) :- nonvar(L), L = '$lam'(X, _, B), !,
  bind(X, N0, N1), foldl(name_binders, Ms, N1, N2), name_binders(B, N2, N).
name_binders('$app'(F, _, Ms), N0, N) :- !, foldl(name_binders, Ms, N0, N1), name_binders(F, N1, N).
name_binders('$rewrite'(X:_, _, E, M), N0, N) :- !,
  bind(X, N0, N1), name_binders(E, N1, N2), name_binders(M, N2, N).
name_binders(_, N, N).

% binders already numbered keep their names
bind(X, N0, N) :- var(X), !, X = '$VAR'(N0), N is N0 + 1.
bind(_, N, N).
