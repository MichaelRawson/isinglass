/*
Closing a proof term after search, so that it is ground (see ir.pl):

  - term and type variables left unconstrained by search become some term of their sort S (the
    sort of types is '$tType'), or else '$inhabited'(S), an arbitrary individual of S;
  - binders still Prolog variables (those of hypotheses, during search) are variables '$VAR'(N),
    numbered in binder order after those already numbered (eigenvariables, rigid during search).

Every variable is an argument of a step, a split definition, a built-in or a quantified hypothesis,
for a binder of its type, so its sort is that of its binder. Type variables are closed first, so that the sorts
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
  numbered_max(M, -1, Max),
  N is Max + 1.

% the greatest number of a variable '$VAR'(I) of T, folded over T (not by subterm/2, which backtracks
% through every level of a curried application)
numbered_max(T, N, N) :- var(T), !.
numbered_max('$VAR'(I), N0, N) :- integer(I), !, N is max(N0, I).
numbered_max(T, N0, N) :- compound(T), !, T =.. [_|As], foldl(numbered_max, As, N0, N).
numbered_max(_, N, N).

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
instances(Env, T, M) --> { M = '$app'(_, _), spine(M, F, As) }, !, applied(Env, T, F, As).
instances(_, _, _) --> [].

% F applied to As, of type T. A redex: the λ takes the first argument, of the type of its binder (a
% hypothesis at the head is a variable); otherwise each argument is of the type the head's says
applied(Env, T, L, [A|As]) --> { nonvar(L), L = '$lam'(X, F, N) }, !,
  instances(Env, F, A),
  { curried(N, As, N1), ( As == [] -> T1 = T ; true ) },
  instances([X-F|Env], T1, N1).
applied(Env, _, F, As) -->
  { head_of(Env, F, As, T) },
  arguments(Env, T, As),
  ( { compound(F) } -> instances(Env, _, F) ; [] ).

% abstraction(T, X, A, A1, T1): λ X : A of type T has the binder X : A1, as annotated, or else as T
% says, and the body of type T1
abstraction(T, X, A, A1, T1) :-
  nonvar(T), T = '$proof'(F), nonvar(F), proof_abstraction(F, X, A0, T1), !,
  ( A == '$inferred' -> A1 = A0 ; A1 = A ).
abstraction(_, _, A, A, _).

proof_abstraction('!'(Y:S, B), X, S, '$proof'(B1)) :- substitute(Y, X, B, B1).
proof_abstraction((A => B), _, '$proof'(A), '$proof'(B)).
proof_abstraction(~A, _, '$proof'(A), '$proof'('$false')).

% the type of a head, where known: a hypothesis, a step, or a built-in, whose parameters, if those of
% an expansion rule, follow from the type of its first argument, a hypothesis
head_of(Env, F, _, T) :- \+ atom(F), !, ( typed(Env, F, T) -> true ; true ).
head_of(Env, Rule, As, T) :-
  atom(Rule),
  head_type(Rule, T), !,
  (   inferred_premise(Rule), As = [A|_], var(A), typed(Env, A, '$proof'(F0)),
      T = '$proof'((F1 => _)), F1 = F0
  ->  true
  ;   true
  ).
head_of(_, F, _, T) :- atom(F), step(F, Conclusion, _), !, step_type(Conclusion, T).
head_of(_, _, _, _).

typed(Env, X, T) :- member(Y-T, Env), Y == X, !, nonvar(T), T = '$proof'(F), nonvar(F).

% each argument of a head of type T: a term for a binder X : S, a hole to close, whose term the sorts
% and types after it may depend on, or a proof of a premise; a split symbol is its clause type. The
% terms are substituted only where they are needed, at once, in a premise of a proof to look into,
% and a type in the sort of a binder (which mentions no other term): substituting each term into the
% rest of a wide clause's type would be quadratic
arguments(Env, T, As) --> arguments(Env, T, []-[], As).

arguments(_, _, _, []) --> !.
arguments(Env, T, Sub, [A|As]) --> { nonvar(T), T = '$proof'(F0), nonvar(F0), unfolded(F0, F) }, !,
  argument(Env, F, Sub, A, T1, Sub1),
  arguments(Env, T1, Sub1, As).
arguments(Env, _, _, [A|As]) --> instances(Env, _, A), arguments(Env, _, []-[], As).

% Sub is Types-Terms, the substitutions of the binders so far, of types and of all; a motive (of an
% arrow sort, see ir.pl) is substituted at once, as the type after it is small
argument(_, '!'(X:S, B0), Sub, A, '$proof'(B), Sub) --> { arrow_sort(S), nonvar(A) }, !,
  { substitute(X, A, B0, B1), applied_motives(B1, B) }.
argument(Env, '!'(X:S0, B), Types-Terms, A, '$proof'(B), Types1-[X-A|Terms]) --> !,
  { substituted(Types, S0, S), ( S == '$tType' -> Types1 = [X-A|Types] ; Types1 = Types ) },
  ( { var(A) } -> [hole(Env, A, S)] ; [] ).
argument(Env, (P => Q), Sub, A, '$proof'(Q), Sub) --> !, premise(Env, Sub, P, A).
argument(Env, ~P, Sub, A, '$proof'('$false'), Sub) --> !, premise(Env, Sub, P, A).
argument(Env, _, _, A, _, []-[]) --> instances(Env, _, A).

% the type of a proof is needed only for a binder '$inferred' of its λs (a hypothesis has nothing to
% close, and an application is typed by its head)
premise(_, _, _, A) --> { var(A) }, !.
premise(Env, _-Terms, P0, A) --> { inferred_binder(A) }, !, { substituted(Terms, P0, P) }, instances(Env, '$proof'(P), A).
premise(Env, _, _, A) --> instances(Env, _, A).

inferred_binder(M) :- nonvar(M), M = '$lam'(_, A, B), ( A == '$inferred' -> true ; inferred_binder(B) ).

% each binder X of Sub, as X-A, replaced by A, in one pass: a binder is a variable (of a fresh
% instance), '$VAR'(N) or '$BOUND'(H)
substituted([], F, F) :- !.
substituted(Sub, T, A) :- binder(T), !, ( member(X-A0, Sub), X == T -> A = A0 ; A = T ).
substituted(_, T, T) :- \+ compound(T), !.
substituted(Sub, T0, T) :- T0 =.. [F|As0], maplist(substituted(Sub), As0, As), T =.. [F|As].

binder(T) :- ( var(T) ; T = '$VAR'(_) ; T = '$BOUND'(_) ), !.

unfolded(F, T) :- atom(F), split(F, Clause), !, clause_type(Clause, T).
unfolded(F, F).

% a hypothesis is a variable until named, so the clauses below would bind it: hence the guard
name_binders(V, N, N) :- var(V), !.
name_binders('$lam'(X, _, M), N0, N) :- !, bind(X, N0, N1), name_binders(M, N1, N).
name_binders(M, N0, N) :- M = '$app'(_, _), !, spine(M, F, As), name_applied(F, As, N0, N).
name_binders('$abs'(X:_, _), N0, N) :- !, bind(X, N0, N).
name_binders(_, N, N).

% the binder of a redex is named before its arguments, and its body after them
name_applied(L, As, N0, N) :- nonvar(L), L = '$lam'(X, _, B), !,
  bind(X, N0, N1), foldl(name_binders, As, N1, N2), name_binders(B, N2, N).
name_applied(F, As, N0, N) :- foldl(name_binders, As, N0, N1), name_binders(F, N1, N).

% binders already numbered keep their names
bind(X, N0, N) :- var(X), !, X = '$VAR'(N0), N is N0 + 1.
bind(_, N, N).
