/*
Closing a proof term after search, so that it is ground (see ir.pl):

  - binders, Prolog variables during search, are named h(0), h(1), ..., in binder order;
  - term variables left unconstrained by search become '$inhabited', an arbitrary individual.

'$inhabited' assumes that the sort of individuals is inhabited, as classical first-order logic
does. Back ends decide what it stands for. A constructive back end (Agda, say) may not assume this,
and could instead look for a closed term of the sort, e.g. a constant of the signature: that choice
belongs here.
*/
:- module(close, [close_term/1]).
:- use_module(library(apply)).

close_term(M) :- close_term(M, 0, _).

% a proof term is never a variable, but if it were, the clauses below would bind it: hence the guard
close_term(V, N, N) :- var(V), !.
close_term(lam(X, _, M), N0, N) :- !, bind(X, N0, N1), close_term(M, N1, N).
close_term(let(X, _, M, M1), N0, N) :- !, bind(X, N0, N1), close_term(M, N1, N2), close_term(M1, N2, N).
close_term(app(_, Ts, Ms), N0, N) :- !,
  term_variables(Ts, Vs),
  maplist(=('$inhabited'), Vs),
  foldl(close_term, Ms, N0, N).
close_term(_, N, N).

% binders of eigenvariables are already named '$VAR'(N)
bind(X, N0, N) :- var(X), !, X = h(N0), N is N0 + 1.
bind(_, N, N).
