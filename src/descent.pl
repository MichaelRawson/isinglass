/*
The tactic for steps between formulas: preprocessing and clausification.

  descent(Fresh, Hs, Parents, M)

M : ⊥ is found from the hypotheses Hs, which refute the conclusion, and the parents, by the
expansion rules of ir.pl. Such a step transforms its parent part by part, so the parent and the
refuted conclusion are two sides that are taken apart in step, and only against each other: a
branch is closed by a formula F of one side and ~F of the other, modulo symmetry of equality
(matching.pl), and formulas of the same side are never compared. A formula that joins a side

  closes the branch,      against the other side;
  α, ~~, ~?               or is expanded at once, so that nested conjunctions are flat;
  β, γ, δ                 or else waits.

Either way it stays on its side, so that its counterpart closes against it whole, when that joins
the other side: parts which the step leaves alone are not taken apart.

When no formula is left to join, one that waits is developed: a δ formula has new eigenvariables,
a β formula is split in two branches, and the bound variables of a γ formula become Prolog
variables, which closing a branch instantiates. Where one formula waits on each side, they are
counterparts, and so are what comes of them, as long as neither side runs ahead of the other: a γ
formula is developed with its δ.

Where several wait on a side, it is first narrowed to one of them, the counterpart of what waits on
the other side, and the rest are dropped: they are other parts of the parent (or of the
conclusion), which would be split again in each branch. This choice is the search: those with
the literals that the other side needs are tried first. A formula that waits alone may also have
its counterpart in several parts (a β formula has, in a conjunction; so has <=>, once it is replaced
by other connectives), so it is also developed with the other side as it is.

Variables are rigid: a formula is developed at most once on a branch. An eigenvariable may not
occur in the instance of a γ formula developed before its δ, so δ formulas come before γ, and a γ
formula whose instance has a δ before the others; β formulas come first, so that each branch has
its own instance.

Formulas are canonical (see logic.pl), so those that differ only in the names of bound variables
close a branch as they are.
*/
:- module(descent, [descent/4]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(matching).

% a branch is branch(Left, Right, Scope): the left side, of the parents, and the right side, of
% the conclusion. A side is side(Kept, Waiting): the formulas X-F that have joined it, apart
% from those still to develop.
% Scope is scope(Fresh, Open, Deltas): the next eigenvariable index, the variables Open of the γ
% instances so far, and for each eigenvariable E of a δ, E-Open as it then was.
% The agenda holds the formulas still to join, each as Side-(X-F)
descent(Fresh, Hs, Parents, M) :-
  parents(Parents, Es, M, Body),
  agenda(right, Hs, Agenda0, Agenda1),
  agenda(left, Es, Agenda1, []),
  Empty = side([], []),
  expand(Agenda0, branch(Empty, Empty, scope(Fresh, [], [])), Body).

% each parent is a hypothesis, of its formula or the type of its clause
parents([], [], M, M).
parents([P|Ps], [H-F|Es], let(H, F, app(P, [], []), M0), M) :-
  step(P, Conclusion, _),
  step_type(Conclusion, F0),
  canonical(F0, F),
  parents(Ps, Es, M0, M).

agenda(_, [], Agenda, Agenda).
agenda(Side, [H|Hs], [Side-H|Agenda0], Agenda) :- agenda(Side, Hs, Agenda0, Agenda).

% a side of the branch, and the other
sides(left, branch(L, R, _), L, R).
sides(right, branch(L, R, _), R, L).

% the branch with another side
replaced(left, L, branch(_, R, Scope), branch(L, R, Scope)).
replaced(right, R, branch(L, _, Scope), branch(L, R, Scope)).

% the formulas of the agenda join the branch, one at a time, until it and those that come of it are
% closed. If that instantiates no variable that was open before, it constrains nothing else, so any
% other way is as good, and this one is kept
expand(Agenda, Branch, M) :-
  Branch = branch(_, _, scope(_, Open, _)),
  term_variables(Open, Vs0),
  expanded(Agenda, Branch, M),
  term_variables(Open, Vs),
  ( Vs0 == Vs -> ! ; true ).

expanded([], Branch, M) :- develop(Branch, M).
expanded([Side-(X-F)|_], Branch, M) :-
  sides(Side, Branch, _, side(Kept, Waiting)),
  ( Others = Waiting ; Others = Kept ),
  closes(Others, X, F, M),
  scoped(Branch).
expanded([Side-H|Agenda], Branch, M) :- join(H, Side, Agenda, Branch, M).

% X : F closes the branch, by itself or against the formulas Hs of the other side
closes(_, X, '$false', X).
closes(_, X, ~'$true', app(X, [], [app('$trivial', [], [])])).
closes(Hs, X, F, M) :-
  matches(Hs, F, Refutation),
  applied(Refutation, X, M).

% the instances of the γ formulas are in scope: none has an eigenvariable of a δ developed after it,
% or a bound variable, from unifying quantified formulas
scoped(branch(_, _, scope(_, Open, Deltas))) :-
  each(member(E-Before, Deltas), \+ occurs(E, Before)),
  \+ binds(Open).

binds(T) :- nonvar(T), T = '$BOUND'(_), !.
binds(T) :- compound(T), T =.. [_|Ts], member(S, Ts), binds(S), !.

% X : F does not close the branch, and stays on its side: it is expanded, or waits
join(X-F, Side, Agenda, Branch0, M) :-
  sides(Side, Branch0, side(Kept, Waiting), _),
  (   expansion(F, X, Es, M, M1)
  ->  replaced(Side, side([X-F|Kept], Waiting), Branch0, Branch),
      agenda(Side, Es, Agenda1, Agenda)
  ;   kind(F, _)
  ->  replaced(Side, side(Kept, [X-F|Waiting]), Branch0, Branch),
      Agenda1 = Agenda, M = M1
  ;   replaced(Side, side([X-F|Kept], Waiting), Branch0, Branch),
      Agenda1 = Agenda, M = M1
  ),
  expand(Agenda1, Branch, M1).

% X : F is expanded at once, to the hypotheses Es: M is M1 : ⊥ with these bound
expansion(F, X, Es, app(Rule, [], [X, K]), M) :-
  alpha(F, Rule, Ts), !,
  entries(Ts, Es),
  lambdas(Es, M, K).
expansion(~(~F), X, [Y-F], app(X, [], [lam(Y, F, M)]), M) :- !.
expansion(~'?'(Bs, F), X, [Y-T], let(Y, T, app('$nex', [], [X]), M), M) :- T = '!'(Bs, ~F).

% a hypothesis for each formula
entries([], []).
entries([T|Ts], [_-T|Es]) :- entries(Ts, Es).

% the formulas that wait, by what developing them does; a γ formula is eigen if a δ formula
% occurs in its instance, or would if that were expanded
kind('!'(_, F), Kind) :- !, ( eigen(F) -> Kind = eigen ; Kind = gamma ).
kind(F, delta) :- delta(F, _, _, _), !.
kind(F, beta) :- beta(F, _, _, _).

eigen(F) :- delta(F, _, _, _), !.
eigen('!'(_, F)) :- !, eigen(F).
eigen(~'?'(_, F)) :- !, eigen(~F).
eigen(~(~F)) :- !, eigen(F).
eigen(F) :- alpha(F, _, Ts), !, member(T, Ts), eigen(T), !.
eigen(F) :- beta(F, _, Ts1, Ts2), ( member(T, Ts1) ; member(T, Ts2) ), eigen(T), !.

% no formula is left to join, so one that waits is developed. Where several wait on a side, it is
% first narrowed to one of them, or else a formula that waits alone on the other side is developed
% regardless: a β formula before narrowing, as its counterpart is a conjunction, of the several
develop(Branch0, M) :-
  Branch0 = branch(side(_, Ls), side(_, Rs), _),
  (   \+ several(Ls), \+ several(Rs)
  ->  append(Ls, Rs, Ws),
      advance(Ws, Branch0, M)
  ;   alone(Ls, Rs, Ws), Ws = [_-F], kind(F, beta)
  ->  ( advance(Ws, Branch0, M) ; narrow(Ls, Rs, Branch0, M) )
  ;   narrow(Ls, Rs, Branch0, M)
  ;   alone(Ls, Rs, Ws),
      advance(Ws, Branch0, M)
  ).

narrow(Ls, Rs, Branch0, M) :-
  narrowed(Ls, Rs, Branch0, Branch),
  develop(Branch, M).

several([_, _|_]).

alone([L], [_, _|_], [L]).
alone([_, _|_], [R], [R]).

% a side where several formulas wait is left with one of them; where several wait on both sides,
% one side at a time, as the counterpart of the one may itself be several of the other: first the
% side where more wait, as these are all the parts of a conjunction, and the fewer come of one
narrowed(Ls0, Rs0, branch(side(Lk, _), side(Rk, _), Scope), branch(side(Lk, Ls), side(Rk, Rs), Scope)) :-
  (   several(Ls0), several(Rs0)
  ->  length(Ls0, N),
      length(Rs0, K),
      member(Side, [left, right]),
      ( first(Side, N, K) -> Rs = Rs0, one(Ls0, Rk, Rs0, Ls) ; Ls = Ls0, one(Rs0, Lk, Ls0, Rs) )
  ;   one(Rs0, Lk, Ls0, Rs),
      one(Ls0, Rk, Rs, Ls)
  ).

% the left side is narrowed before the right, or after
first(left, N, K) :- N >= K.
first(right, N, K) :- N < K.

% one of the formulas Ws, if any: first those that have the literals to close against the other
% side, of which some are Kept and the others wait
one([], _, _, []) :- !.
one([W], _, _, [W]) :- !.
one(Ws, Kept, Waiting, [W]) :-
  findall(L, ( wanted(Kept, Waiting, F), signed(F, pos, L) ), Ls),
  sort(Ls, Wanted),
  (   member(W, Ws), likely(W, Wanted)
  ;   member(W, Ws), \+ likely(W, Wanted)
  ).

% what the other side has to close against: its literals, and what waits there
wanted(Kept, Waiting, F) :- ( member(_-F, Waiting) ; member(_-F, Kept), literal(F) ).

% X : F has a literal against each of those Wanted, by its sign and symbol
likely(_-F, Wanted) :-
  findall(L, signed(F, pos, L), Ls),
  each(member(S-P, Wanted), ( opposite(S, T), memberchk(T-P, Ls) )).

% a literal of F, one at a time, as Sign-Symbol: its sign, where F has the sign Sign0
signed(~F, S0, L) :- !, opposite(S0, S), signed(F, S, L).
signed((F => G), S0, L) :- !, ( opposite(S0, S), signed(F, S, L) ; signed(G, S0, L) ).
signed((F <=> G), _, L) :- !, member(S, [pos, neg]), ( signed(F, S, L) ; signed(G, S, L) ).
signed(F, S, L) :- connective(F, Gs), !, member(G, Gs), signed(G, S, L).
signed(A, S, S-N/K) :- functor(A, N, K).

opposite(pos, neg).
opposite(neg, pos).

% one of the formulas Ws is developed, and waits no longer: any δ or β formula will do, as these
% can be developed in any order, but the order of the γ formulas matters
advance(Ws, Branch0, M) :-
  next(Ws, Kind, X-F),
  waits(X, Branch0, Side, Kept, Waiting),
  replaced(Side, side([X-F|Kept], Waiting), Branch0, Branch),
  developed(Kind, F, X, Side, Branch, M).

% X waits on a side, with the others Waiting
waits(X, Branch, Side, Kept, Waiting) :-
  member(Side, [left, right]),
  sides(Side, Branch, side(Kept, Waiting0), _),
  removed(Waiting0, X, Waiting), !.

next(Ws, Kind, X-F) :- member(Kind, [beta, delta]), member(X-F, Ws), kind(F, Kind), !.
next(Ws, Kind, X-F) :- member(Kind, [eigen, gamma]), member(X-F, Ws), kind(F, Kind).

removed([Y-F|Hs0], X, Hs) :- ( Y == X -> Hs = Hs0 ; Hs = [Y-F|Hs1], removed(Hs0, X, Hs1) ).

% the two branches of a β formula
developed(beta, F, X, Side, Branch, app(Rule, [], [X, K1, K2])) :-
  beta(F, Rule, Ts1, Ts2),
  entries(Ts1, Es1),
  entries(Ts2, Es2),
  lambdas(Es1, M1, K1),
  lambdas(Es2, M2, K2),
  ordered(Es1-M1, Es2-M2, First-M3, Second-M4),
  branch(First, Side, Branch, M3),
  branch(Second, Side, Branch, M4).
% the body of a δ formula, for eigenvariables, and with it an instance of its counterpart, a γ
% formula that waits alone on the other side: so neither side runs ahead of the other
developed(delta, F, X, Side, Branch0, M) :-
  Branch0 = branch(L, R, Scope0),
  eigenvariables(F, X, Scope0, H, Scope, M, M1),
  Branch1 = branch(L, R, Scope),
  (   counterpart(Side, Branch1, Other, Branch, I, M1, M2)
  ->  Agenda = [Side-H, Other-I]
  ;   Agenda = [Side-H], Branch = Branch1, M2 = M1
  ),
  expand(Agenda, Branch, M2).
% an instance of a γ formula
developed(eigen, F, X, Side, Branch, M) :- developed(gamma, F, X, Side, Branch, M).
developed(gamma, F, X, Side, Branch0, M) :-
  instantiated(F, X, Branch0, Branch, H, M, M1),
  expand([Side-H], Branch, M1).

% X : F with an eigenvariable for each of the variables bound outermost is H: M is M1 : ⊥ with
% these bound
eigenvariables(F, X, scope(Fresh0, Open, Deltas), H, Scope, app(Rule, [], [X, lam(E, S, lam(Y, T, M0))]), M) :-
  delta(F, Rule, B:S, T0),
  E = '$VAR'(Fresh0),
  Fresh is Fresh0 + 1,
  substitute(B, E, T0, T),
  Scope1 = scope(Fresh, Open, [E-Open|Deltas]),
  (   delta(T, _, _, _)
  ->  eigenvariables(T, Y, Scope1, H, Scope, M0, M)
  ;   H = Y-T, Scope = Scope1, M0 = M
  ).

% the γ formula that waits alone on the other side has the instance I
counterpart(Side, Branch0, Other, Branch, I, M, M1) :-
  sides(Side, Branch0, _, side(Kept, [X-F])),
  kind(F, Kind),
  memberchk(Kind, [eigen, gamma]),
  sides(Other, Branch0, side(Kept, [X-F]), _),
  Other \== Side,
  replaced(Other, side([X-F|Kept], []), Branch0, Branch1),
  instantiated(F, X, Branch1, Branch, I, M, M1).

% X : F with its bound variables open is the instance H: M is M1 : ⊥ with this bound
instantiated('!'(Bs, F), X, Branch0, Branch, Y-T, let(Y, T, app(X, Us, []), M), M) :-
  Branch0 = branch(L, R, scope(Fresh, Open0, Deltas)),
  instance(Bs, F, Us, T),
  append(Us, Open0, Open),
  Branch = branch(L, R, scope(Fresh, Open, Deltas)).

% a branch of literals is closed after the other, whose literals lie deeper, among more of their
% own kind: they say more about the variables of the γ instances, which are then found sooner
ordered(Es1-M1, Es2-M2, Es2-M2, Es1-M1) :- literals(Es1), \+ literals(Es2), !.
ordered(B1, B2, B1, B2).

literals(Es) :- each(member(_-F, Es), literal(F)).

literal(~A) :- !, \+ connective(A, _).
literal(A) :- \+ connective(A, _).

branch(Es, Side, Branch, M) :-
  agenda(Side, Es, Agenda, []),
  expand(Agenda, Branch, M).

% the body F of a quantifier with its bound variables replaced by fresh variables Us
instance([], F, [], F).
instance([X:_|Bs0], F0, [U|Us], F) :-
  substitute(X, U, Bs0-F0, Bs-F1),
  instance(Bs, F1, Us, F).

% the expansion rules (see ir.pl), by the formulas that they add to each branch
alpha((F & G), '$and', [F, G]).
alpha(~((F | G)), '$nor', [~F, ~G]).
alpha(~((F => G)), '$nimp', [F, ~G]).

beta((F | G), '$or', [F], [G]).
beta((F => G), '$imp', [~F], [G]).
beta(~((F & G)), '$nand', [~F], [~G]).
beta((F <=> G), '$iff', [F, G], [~F, ~G]).
beta(~((F <=> G)), '$niff', [F, ~G], [~F, G]).

% T is to be refuted for the first bound variable B, an eigenvariable
delta(F, Rule, B, T) :-
  ( Rule = '$ex' ; Rule = '$nall' ),
  rule_type(Rule, F, ('!'([B], (T => '$false')) => '$false')), !.
