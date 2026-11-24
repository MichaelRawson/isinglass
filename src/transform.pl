/*
The tactics for steps between formulas, with the interface of reconstruct.pl's; the parent is a
hypothesis of its formula, or of the type of its clause.

transform(Mode): the parent and the conclusion have the same key for the Mode (normal.pl), and are
taken apart in lockstep, the keys saying which parts go together. pair(Ctx, X-F, Y-G, M) refutes
X : F and Y : G, where G's key is that of ~F: literals close, δ eigenvariables instantiate their γ
counterparts, and otherwise a conjunction is expanded into a pool of parts, by key, in which each
branch of the other side is looked up. Skolemisation (Mode skolem) opens a δ formula by the choice
axiom of a Skolem term read off its counterpart, recording the definition as a step.

clausify: the clause's literals refute the parent, by one part of each conjunction and every branch
of each disjunction; the only search is the choice of part.
*/
:- module(transform, [transform/5, clausify/4]).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(matching).
:- use_module(normal).
:- use_module(signature).
:- use_module(utils).

% the parent is a hypothesis X : F; in definition folding, both it and the conclusion are unfolded
% (ir:expanded/2), types that redexes state
transform(fold, Fresh, Hs0, [Parent|_], M) :- !,
  expanded_hypotheses(Hs0, Hs, M, '$lam'(X, '$proof'(F), M1) @ Parent),
  parent_formula(Parent, F0),
  expanded(F0, F),
  transformed_from(base, Fresh, Hs, X-F, M1).
transform(Mode, Fresh, Hs, [Parent], '$lam'(X, '$proof'(F), M) @ Parent) :-
  parent_formula(Parent, F),
  transformed_from(Mode, Fresh, Hs, X-F, M).

% a clause conclusion whose variables are not the parent's outermost universal ones, as in Vampire's
% AVATAR shape (! [X] : C) | ~split, is refuted as in clausification
transformed_from(Mode0, Fresh, Hs, X-F, M1) :-
  eigenvariables(Hs, Es),
  goal(Hs, G),
  context(Mode0, F, G, Fresh, Ctx),
  (   instantiated(Ctx, Es, Hs, X-F, H, M1, M2)
  ->  transformed(Ctx, H, G, Hs, M2),
      Ctx = ctx(_, _, Defs),
      choices(Defs)
  ;   refuted(X-F, Hs, M1)
  ).

% M binds the hypotheses Hs, which are Hs0 with their types unfolded, and then is M1
expanded_hypotheses([], [], M, M).
expanded_hypotheses([X-T|Hs0], [H|Hs], M, M1) :-
  expanded(T, T1),
  ( T1 == T -> H = X-T, M = M0 ; H = Y-T1, M = '$lam'(Y, '$proof'(T1), M0) @ X ),
  expanded_hypotheses(Hs0, Hs, M0, M1).

% Ctx is ctx(Mode, Fresh, Defs), with Defs the Skolem definitions so far, an open list; the Skolem
% symbols are those of the conclusion G that are not in the parent F
context(skolem, F, G, Fresh, ctx(skolem(Ss), Fresh, _)) :- !, skolem_symbols(F, G, Ss).
context(Mode, _, _, Fresh, ctx(Mode, Fresh, _)).

transformed(ctx(Mode0, Fresh, Defs), H, G, Hs, M) :-
  H = _-F,
  weakened(Mode0, F, G, F1, Mode),
  normal(Mode, G, K),
  normal(Mode, F1, K), !,
  conclusion(ctx(Mode, Fresh, Defs), H, Hs, M).

% the formula of the parent, or the type of its clause
parent_formula(Parent, F) :-
  step(Parent, Conclusion, _),
  step_type(Conclusion, '$proof'(F0)),
  canonical(F0, F).

% the eigenvariables of a clause conclusion, in order
eigenvariables(Hs, Es) :- eigenvariables_in(Hs, Es0, []), sort(Es0, Es).

eigenvariables_in(T, [T|Es], Es) :- nonvar(T), T = '$VAR'(_), !.
eigenvariables_in(T, Es0, Es) :- compound(T), !, T =.. [_|Ts], foldl(eigenvariables_in, Ts, Es0, Es).
eigenvariables_in(_, Es, Es).

% a clause conclusion instantiates the outermost universal variables of the parent, in order, but
% for those of its δ formulas that are Skolemised by the conclusion's hypotheses Hs
instantiated(_, [], _, H, H, M, M) :- !.
instantiated(Ctx, Es, Hs, H0, H, M, M2) :-
  universals(H0, [V|Vs], H1, M, M1), !,
  H1 = _-F,
  occurring([V|Vs], F, Os),
  append(Os, Es1, Es),
  instantiated(Ctx, Es1, Hs, H1, H, M1, M2).
instantiated(Ctx, Es, Hs, H0, H, M, M2) :-
  findall(F, member(_-F, Hs), Fs),
  skolemised(Ctx, H0, Fs, H1, M, M1),
  instantiated(Ctx, Es, Hs, H1, H, M1, M2).

% the variables Vs that occur in F
occurring([], _, []).
occurring([V|Vs], F, Os) :- ( occurs(V, F) -> Os = [V|Os1] ; Os = Os1 ), occurring(Vs, F, Os1).

% the conclusion, of which the hypotheses Hs are the refutation
goal(Hs, G) :- findall(L, member(_-(~L), Hs), Ls), disjunction(Ls, G).

weakened(pure, F, G, F, pure(Ss)) :- !, pure_symbols(F, G, Ss).
weakened(definition, F, _, F1, base) :- !, weaken_definition(F, F1).
weakened(Mode, F, _, F, Mode).

% the predicates of F that are not in G, each replaced by $true where it occurs positively, else $false
pure_symbols(F, G, Ss) :-
  findall(P, ( signed_atom(G, pos, A, _), functor(A, N, K), P = N/K ), Ps0),
  sort(Ps0, Ps),
  findall(N/K-V, ( signed_atom(F, pos, A, S), functor(A, N, K), \+ memberchk(N/K, Ps), value(S, V) ), Ss0),
  sort(Ss0, Ss).

value(pos, '$true').
value(neg, '$false').

% the Skolem symbols of G that are not in F, as an assoc to true: many terms are tested against them
skolem_symbols(F, G, Ss) :-
  symbols(F, Fs),
  symbols(G, Gs),
  findall(S-true, ( member(S, Gs), introduced(S, skolem), \+ memberchk(S, Fs) ), Pairs),
  list_to_assoc(Pairs, Ss).

symbols(F, Ss) :- findall(S, ( subterm(F, T), functor(T, S, _) ), Ss0), sort(Ss0, Ss).

% one definition F <=> G of the formula is weakened to F => G, or G => F
weaken_definition((F <=> G), (F => G)).
weaken_definition((F <=> G), (G => F)).
weaken_definition(F, F1) :-
  compound(F),
  F =.. [C|As],
  connective(F, _),
  append(Before, [A|After], As),
  weaken_definition(A, A1),
  append(Before, [A1|After], As1),
  F1 =.. [C|As1].

% a formula conclusion is refuted by one hypothesis, its counterpart; a clause by its literals
conclusion(Ctx, H, [Y-G], M) :- !, pair(Ctx, H, Y-G, M).
conclusion(Ctx, H, Hs, M) :- keyed(Ctx, Hs, Pool), close(Ctx, H, Pool, M).

/********************************************************************************
 * pairing counterparts: Ctx is ctx(Mode, Fresh, Defs), with Fresh the next eigenvariable
 ********************************************************************************/

pair(_, X-F, _, M) :- closes(F, X, M), !.
pair(_, _, Y-G, M) :- closes(G, Y, M), !.
% ...or the one is the negation of the other, as they are (canonical), before either is taken apart:
% a chain of <=> splits into exponentially many branches
pair(_, X-F, Y-G, Y @ X) :- G == ~F, !.
pair(_, X-F, Y-G, X @ Y) :- F == ~G, !.
pair(_, X-F, Y-G, M) :- literal(F), literal(G), !, refutes(G, Y, F, R), !, applied(R, X, M).
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, X-F, Y-G, M), !.
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, Y-G, X-F, M), !.
pair(Ctx, X-F, Y-G, M) :- skolemised(Ctx, X-F, [G], H, M, M1), pair(Ctx, H, Y-G, M1), !.
pair(Ctx, X-F, Y-G, M) :- skolemised(Ctx, Y-G, [F], H, M, M1), pair(Ctx, X-F, H, M1), !.
pair(Ctx, X-F, Y-G, M) :- alpha_like(F), !, pool(Ctx, [X-F], Pool, M, M1), close(Ctx, Y-G, Pool, M1).
pair(Ctx, X-F, Y-G, M) :- alpha_like(G), !, pool(Ctx, [Y-G], Pool, M, M1), close(Ctx, X-F, Pool, M1).
pair(Ctx, X-F, Y-G, M) :- split(X-F, Branches, M), !, ordered(Ctx, Branches, Bs), branches(Ctx, Bs, Y-G).
pair(Ctx, X-F, Y-G, M) :- split(Y-G, Branches, M), ordered(Ctx, Branches, Bs), branches(Ctx, Bs, X-F).

% the parts of each branch are the pool of the other formula
branches(_, [], _).
branches(Ctx, [Es-M|Branches], H) :-
  pool(Ctx, Es, Pool, M, M1),
  close(Ctx, H, Pool, M1),
  branches(Ctx, Branches, H).

% D : δ formula, and G its counterpart, a γ formula: the eigenvariables of the one, but for those
% that are vacuous, are the variables of the other, in order. Either may be vacuous, and the other
% not a quantifier at all. In Skolemisation, a ? of the parent may come between its universals, so
% only as many δ formulas are opened as there are universals. So too elsewhere if all of them do not
% pair: a unit may come between the universals, as in ![X] : ($true & ![Y] : p(X,Y))
quantifiers(ctx(Mode, Fresh0, Defs), D, G, M) :-
  universals(G, Vs0, G1, M1, M2),
  limit(Mode, Vs0, Limit),
  existentials(Mode, Fresh0-Fresh, Limit, D, Es0, D1, M, M1),
  ( Es0 = [_|_] ; Vs0 = [_|_] ),
  D1 = _-F1, G1 = _-T1,
  same_occurring(Mode, Es0, F1, Vs0, T1), !,
  pair(ctx(Mode, Fresh, Defs), G1, D1, M2).

% the eigenvariables Es that occur in F are the variables Vs that occur in T, in order; or failing
% that, those that occur in their keys: so a variable of pure atoms only is vacuous, as is one beside
% $true in a disjunction. Skolem keys blur Skolem terms, so there it is any occurrence
same_occurring(_, Es0, F, Vs0, T) :- occurring(Es0, F, Es), occurring(Vs0, T, Es), !.
same_occurring(Mode, Es0, F, Vs0, T) :-
  Mode \= skolem(_),
  normal(Mode, F, KF), occurring(Es0, KF, Es),
  normal(Mode, T, KT), occurring(Vs0, KT, Es).

limit(skolem(_), Vs, Vs) :- !.
limit(_, _, unlimited).
limit(_, Vs, Vs).

% the δ formulas nested outermost in X : F, up to the Limit, with an eigenvariable for each
% variable, are Y : G; a conjunction of one part and units of the key (a pure atom, as $true) is that
% part, so ?[X] : (p(X) & ?[Y] : q(X,Y)) opens as ?[X,Y] : q(X,Y), and so is ~~F, as ~! [X] : ~?[Y]
% is opened as its γ counterpart ![X] : ~?[Y] is instantiated
existentials(Mode, Fresh0-Fresh, Limit0, X-F, [E|Es], H, Rule @ X @ '$lam'(E, S, '$lam'(Y, '$inferred', M0)), M) :-
  fewer(Limit0, Limit),
  delta(F, Rule, B:S, T0), !,
  E = '$VAR'(Fresh0),
  Fresh1 is Fresh0 + 1,
  substitute(B, E, T0, T),
  existentials(Mode, Fresh1-Fresh, Limit, Y-T, Es, H, M0, M).
existentials(Mode, Fresh0-Fresh, Limit, X-F, Es, H, M, M1) :-
  alpha_like(F),
  expansion(F, X, Parts, M, M0),
  partition(unit(Mode), Parts, _, [Part]), !,
  existentials(Mode, Fresh0-Fresh, Limit, Part, Es, H, M0, M1).
existentials(_, Fresh-Fresh, _, H, [], H, M, M).

unit(Mode, _-F) :- normal(Mode, F, '$true').

fewer(unlimited, unlimited).
fewer([_|Limit], Limit).

% the γ formulas nested outermost in X : F, with fresh variables Vs, are Y : G
universals(X-F0, Vs, H, '$lam'(Y, '$proof'(G), M0) @ N, M) :-
  quantifier_prefix('!', F0, Bs, F), Bs = [_|_], !,
  opened_body(Bs, F, Us, G),
  curried(X, Us, N),
  universals(Y-G, Ws, H, M0, M),
  append(Us, Ws, Vs).
universals(X-(~'?'(B, F)), Vs, H, Rule @ X @ '$lam'(Y, '$inferred', M0), M) :- !,
  not_exists_rule(B, Rule),
  universals(Y-'!'(B, ~F), Vs, H, M0, M).
universals(H, [], H, M, M).

% the γ rule for ~? over the binder B: one over types has its own
not_exists_rule(_:S, '$nex_t') :- S == '$tType', !.
not_exists_rule(_, '$nex').

% the body F of a quantifier with its bound variables replaced by fresh variables Us
opened_body([], F, [], F).
opened_body([X:_|Bs0], F0, [U|Us], F) :-
  substitute(X, U, Bs0-F0, Bs-F1),
  opened_body(Bs, F1, Us, F).

% the pool: the parts of conjunctions, each with the key of its complement (and in nnf, its own), and
% whether it is a δ formula, as keys(K, K1, Kind)
pool(Ctx, Hs, Pool, M, M1) :- parts(Hs, Ps, M, M1), keyed(Ctx, Ps, Pool).

keyed(_, [], []).
keyed(Ctx, [X-F|Hs], [keys(K, K1, Kind)-X-F|Pool]) :-
  Ctx = ctx(Mode, _, _),
  normal(Mode, ~F, K),
  ( Mode == nnf -> normal(Mode, F, K1) ; true ),
  ( delta(F, _, _, _) -> Kind = delta ; Kind = other ),
  keyed(Ctx, Hs, Pool).

% the counterpart Y : G of F in the pool, whose key is that of ~F. In nnf, the negation of an expanded
% <=> is a disjunction of conjunctions, but ~(F <=> G) is expanded as a conjunction, so F is also
% compared the other way round
counterpart(Mode, F, Pool, Y-G) :- normal(Mode, F, K), memberchk(keys(K, _, _)-Y-G, Pool), !.
counterpart(nnf, F, Pool, Y-G) :- normal(nnf, ~F, K), memberchk(keys(_, K, _)-Y-G, Pool).

% the hypotheses Hs expanded as conjunctions, as far as they go
parts([], [], M, M).
parts([X-F|Hs], Ps, M, M1) :-
  (   expansion(F, X, Es, M, M0)
  ->  append(Es, Hs, Hs1), parts(Hs1, Ps, M0, M1)
  ;   Ps = [X-F|Ps1], parts(Hs, Ps1, M, M1)
  ).

% the branch X : F is closed against the pool: a part of the pool closes by itself, or else the
% branch does (closed/4)
close(_, _, Pool, M) :- member(_-X-F, Pool), closes(F, X, M), !.
% ...or a part of the pool is false by its key, as is ~($true & $true), and is refuted by itself
close(Ctx, _, Pool, M) :- member(keys('$true', _, _)-X-F, Pool), closed(Ctx, [X-F], [], M), !.
close(Ctx, H, Pool, M) :- closed(Ctx, [H], Pool, M).

% the Branch is closed: one of its formulas closes by itself, or has a counterpart in the pool, or
% else one of them is taken apart. A disjunction is looked up only if its counterpart is a δ formula,
% whose binders are vacuous (~![X] : (b => c) for b => c): otherwise it is a conjunction, whose parts
% are in the pool already. In Skolemisation, it may be a ? of the parent, not yet opened, and as keys
% forget terms, each counterpart is tried, and then the other ways to close the branch
closed(_, Branch, _, M) :- member(X-F, Branch), closes(F, X, M), !.
closed(Ctx, Branch, Pool, M) :-
  Ctx = ctx(skolem(Ss), _, _),
  member(X-F, Branch),
  normal(skolem(Ss), F, K),
  member(keys(K, _, _)-Y-G, Pool),
  pair(Ctx, X-F, Y-G, M), !.
closed(Ctx, Branch, Pool, M) :-
  Ctx = ctx(Mode, _, _),
  Mode \= skolem(_),
  member(X-F, Branch),
  lookup_pool(Mode, F, Pool, Pool1),
  counterpart(Mode, F, Pool1, Y-G), !,
  pair(Ctx, X-F, Y-G, M).
closed(Ctx, Branch, Pool, M) :- taken_apart(Ctx, Branch, Pool, M).

% a formula of the branch is expanded, opened or split, its parts replacing it
taken_apart(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  expansion(F, X, Es, M, M1), !,
  append(Es, Rest, Branch1),
  closed(Ctx, Branch1, Pool, M1).
taken_apart(Ctx, Branch, Pool, M) :-
  Ctx = ctx(skolem(_), _, _),
  findall(G, member(_-_-G, Pool), Gs),
  select(X-F, Branch, Rest),
  skolemised(Ctx, X-F, Gs, H, M, M1),
  closed(Ctx, [H|Rest], Pool, M1), !.
taken_apart(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  split(X-F, Branches0, M), !,
  ordered(Ctx, Branches0, Branches),
  close_branches(Ctx, Branches, Rest, Pool).

% the part of the pool where F is looked up: for a disjunction, only δ formulas, if any
lookup_pool(Mode, F, Pool, Pool1) :-
  disjunctive(Mode, F), !,
  partition(delta_entry, Pool, Pool1, _),
  Pool1 = [_|_].
lookup_pool(_, _, Pool, Pool).

delta_entry(keys(_, _, delta)-_-_).

close_branches(_, [], _, _).
close_branches(Ctx, [Es-M|Branches], Rest, Pool) :-
  append(Es, Rest, Branch),
  closed(Ctx, Branch, Pool, M),
  close_branches(Ctx, Branches, Rest, Pool).

/********************************************************************************
 * Skolemisation
 ********************************************************************************/

% the δ formula X : F is opened by the choice of a Skolem term sK(As), of a symbol Ss, in the
% formulas Gs, as Y : T[sK(As)/B]. Its arguments As are distinct eigenvariables, among them those of
% F, and sK is not in F, whose choice it is; its definition agrees with any other in Defs
skolemised(ctx(skolem(Ss), _, Defs), X-F, Gs, Y-T1, '$lam'(Y, '$proof'(T1), M) @ N, M) :-
  delta(F, '$ex', B:_, T),
  ground(F),
  eigenvariables_in(F, Vs, []),
  candidates(Ss, F, B, T, Gs, Us),
  member(Term, Us),
  Term =.. [Sk|As],
  distinct_eigenvariables(As),
  each_member(Vs, As),
  \+ ( subterm(F, U), functor(U, Sk, _) ),
  defined(Defs, Sk, As, F),
  substitute(B, Term, T, T1),
  definition_name(Sk, Name),
  append(As, [X], Args),
  curried(Name, Args, N).

% the candidate Skolem terms Us for the δ formula F, ? B : T, in the formulas Gs: if the prover hints
% at its choice of symbol (db.pl), only its terms, so a wrong counterpart fails at once (LCL652+1.015:
% chains of r1(X, Y) under nested ?); else, or for a vacuous B, each term of the symbols Ss
candidates(_, F, B, T, Gs, Us) :-
  occurs(B, T),
  findall(Sk, ( skolem_hint(Sk, D), D = F ), Hints),
  Hints = [_|_], !,
  findall(U, ( subterm(Gs, U), functor(U, Sk, _), memberchk(Sk, Hints) ), Us0),
  sort(Us0, Us).
candidates(Ss, _, _, _, Gs, Us) :-
  findall(U, ( subterm(Gs, U), functor(U, Sk, _), get_assoc(Sk, Ss, _) ), Us0),
  sort(Us0, Us).

distinct_eigenvariables([]).
distinct_eigenvariables([A|As]) :- nonvar(A), A = '$VAR'(_), \+ memberchk(A, As), distinct_eigenvariables(As).

each_member([], _).
each_member([V|Vs], As) :- memberchk(V, As), each_member(Vs, As).

% sK(As) is defined by F, as in Defs, or as a new definition at its end
defined(Defs, Sk, As, F) :- var(Defs), !, Defs = [def(Sk, As, F)|_].
defined([def(Sk1, As1, F1)|_], Sk, As, F) :- Sk1 == Sk, !, substitute_all(As1, Ws, F1, G), substitute_all(As, Ws, F, G).
defined([_|Defs], Sk, As, F) :- defined(Defs, Sk, As, F).

% each definition is recorded as a step, whose conclusion is its choice axiom, with its eigenvariables
% renumbered from 0, and of the sorts of the arguments of its symbol
choices(Defs) :- var(Defs), !, Defs = [].
choices([]).
choices([def(Sk, As, F0)|Defs]) :-
  substitute_all(As, Xs, F0, F1),
  number_vars(Xs, 0, _),
  canonical(F1, F),
  symbol_binders(Sk, Xs, Bs, _),
  choice_axiom(Sk, Bs, F, A0),
  canonical(A0, A),
  definition_name(Sk, Name),
  record(step(Name, formula(A), skolem_def(Sk, Bs, F))),
  record(ir_step(Name, formula(A), skolem_def(Sk, Bs, F))),
  choices(Defs).

/********************************************************************************
 * clausification
 ********************************************************************************/

clausify(_, Hs, [Parent], '$lam'(X, '$proof'(F), M) @ Parent) :-
  parent_formula(Parent, F),
  refuted(X-F, Hs, M).

% X : F is refuted by the hypotheses Hs
refuted(X-F, _, M) :- closes(F, X, M), !.
refuted(X-F, Hs, M) :- literal(F), !, matches(Hs, F, R), applied(R, X, M).
refuted(H, Hs, M) :- universals(H, [_|_], H1, M, M1), !, refuted(H1, Hs, M1).
refuted(X-F, Hs, M) :-
  expansion(F, X, Es, M, M1), !,
  refute_one(Es, Hs, M1).
refuted(H, Hs, M) :-
  split(H, Branches, M),
  refute_branches(Branches, Hs).

% one of the parts Ps is refuted
refute_one(Ps, Hs, M) :- member(P, Ps), refuted(P, Hs, M).

refute_branches([], _).
refute_branches([Es-M|Branches], Hs) :-
  refute_one(Es, Hs, M),
  refute_branches(Branches, Hs).

/********************************************************************************
 * the expansion rules (see ir.pl)
 ********************************************************************************/

closes('$false', X, X).
closes(~'$true', X, X @ '$trivial').

alpha_like(F) :- alpha(F, _, _), !.
alpha_like(~(~_)).

% a disjunction, whose counterpart is a conjunction (but in nnf, <=> is a conjunction when expanded)
disjunctive(Mode, F) :- Mode \== nnf, beta(F, Rule, _, _), Rule \== '$iff', Rule \== '$niff'.

% X : F is expanded at once, to the hypotheses Es: M is M1 : ⊥ with these bound
expansion(F, X, Es, Rule @ X @ K, M) :-
  alpha(F, Rule, Ts), !,
  entries(Ts, Es),
  inferred_lambdas(Es, M, K).
expansion(~(~F), X, [Y-F], X @ '$lam'(Y, '$inferred', M), M).

% in Skolemisation, the branches smallest first: a wrong counterpart, as Skolem keys allow, fails on
% its smallest branch before the others are taken apart. Otherwise ~(C & p(sK1)) against
% ?[X] : (D & p(X)), with sK0 for X, closes C against D first, and with it each δ formula nested in
% them, again for each wrong counterpart of the levels around them (ITP009+2). Elsewhere a counterpart is
% the only one, and sizes would be quadratic in the nesting of a formula
ordered(ctx(skolem(_), _, _), Branches, Sorted) :- !,
  maplist(sized, Branches, Keyed),
  keysort(Keyed, Pairs),
  pairs_values(Pairs, Sorted).
ordered(_, Branches, Branches).

% N is the number of connectives and atoms of the formulas of the branch
sized(Es-M, N-(Es-M)) :- foldl(entry_size, Es, 0, N).

entry_size(_-F, N0, N) :- formula_size(F, N0, N).

formula_size(F, N0, N) :- connective(F, Gs), !, N1 is N0 + 1, foldl(formula_size, Gs, N1, N).
formula_size(_, N0, N) :- N is N0 + 1.

% X : F is split into branches Es-M, each M : ⊥ with the hypotheses Es bound
split(X-F, [Es1-M1, Es2-M2], Rule @ X @ K1 @ K2) :-
  beta(F, Rule, Ts1, Ts2),
  entries(Ts1, Es1),
  entries(Ts2, Es2),
  inferred_lambdas(Es1, M1, K1),
  inferred_lambdas(Es2, M2, K2).

% M abstracted over the hypotheses Es, whose types follow from the rule (see ir.pl): annotating each
% with its formula would make terms quadratic in the size of a conjunction
inferred_lambdas([], M, M).
inferred_lambdas([X-_|Es], M, '$lam'(X, '$inferred', N)) :- inferred_lambdas(Es, M, N).

% a hypothesis for each formula
entries([], []).
entries([T|Ts], [_-T|Es]) :- entries(Ts, Es).

% an expansion rule of one branch (α), or of two (β), see ir.pl
% ~? is a γ formula, whose rule is applied as it is instantiated (universals/5)
alpha(F, Rule, Ts) :- F \= ~'?'(_, _), rule_branches(F, Rule, [Ts]).

beta(F, Rule, Ts1, Ts2) :- rule_branches(F, Rule, [Ts1, Ts2]).

% T is to be refuted for the first bound variable B, an eigenvariable
delta(F, Rule, B, T) :-
  ( Rule = '$ex' ; Rule = '$nall' ),
  head_type(Rule, '$proof'((F => ('!'(B, (T => '$false')) => '$false')))), !.
