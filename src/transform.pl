/*
The tactics for preprocessing steps and clausification, each specific to what the step does.

  transform(Mode, Fresh, Hs, Parents, M)
  clausify(Fresh, Hs, Parents, M)

As in reconstruct.pl, M : ⊥ is found from the hypotheses Hs, which refute the conclusion, and the
parent, a hypothesis of its formula, or the type of its clause.

transform: the parent and the conclusion have the same normal form for the Mode of the step
(normal.pl), or else the step fails at once. The proof takes the two apart in lockstep, and the
keys say which parts go together, so there is no search. pair(X-F, Y-G) refutes X : F and Y : G,
where the key of G is that of ~F:

  - a formula that closes by itself ($false, ~$true) closes the branch;
  - two literals are complementary, modulo symmetry of equality (matching.pl);
  - a δ formula (?, ~!) has eigenvariables, which instantiate its counterpart, a γ formula (!, ~?),
    variable by variable, apart from vacuous ones;
  - otherwise one is a conjunction (α, ~~), which is expanded into a pool of its parts, by key; the
    other is split (β) into branches, and each part of a branch is looked up in the pool, or
    expanded or split further. Where both are split (<=> against ~(<=>)), the branches of one are
    the pool of the other.

Some steps only weaken their parent: the pure predicates are those of the parent but not of the
conclusion, and an unused definition F <=> G is weakened to F => G or G => F.

Skolemisation is an entailment once each Skolem symbol is defined by choice: sK(xs) := ε Y. T, for
a δ formula of the parent ?[Y] : T (or ~![Y] : G, where T is ~G). The Skolem symbols are those of
the conclusion that are not in the parent; their keys forget them (normal.pl). A δ formula of the
parent is opened by the choice axiom of a Skolem term in its counterpart (skolem_def, see ir.pl):
the term is read off the conclusion, so no convention of the prover is assumed. The definitions
that the proof uses are recorded as steps, before the step itself.

clausify: the conclusion is a clause of the conjunctive normal form of the parent. The literals of the
conclusion refute the parent: one part of a conjunction, every branch of a disjunction, and a literal
by unification. The only search is the choice of part, of those that can be refuted by literals of
the clause's predicates and signs.
*/
:- module(transform, [transform/5, clausify/4]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(matching).
:- use_module(normal).

% a clause conclusion whose variables are not those of the outermost universal quantifiers of the parent,
% as in Vampire's AVATAR shape (! [X] : C) | ~split, is refuted as in clausification
% definition folding: the parent and the conclusion are the same once the defined predicates of both
% are unfolded (see ir.pl), and these unfolded types are stated by lets
transform(fold, Fresh, Hs0, [Parent|_], M) :- !,
  expanded_hypotheses(Hs0, Hs, M, M0),
  step(Parent, Conclusion, _),
  step_type(Conclusion, F0),
  canonical(F0, F1),
  expanded(F1, F),
  M0 = let(X, F, app(Parent, [], []), M1),
  transformed_from(base, Fresh, Hs, X-F, M1).
transform(Mode, Fresh, Hs, [Parent], M) :-
  parent(Parent, X, F, M, M1),
  transformed_from(Mode, Fresh, Hs, X-F, M1).

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
  ( T1 == T -> H = X-T, M = M0 ; H = Y-T1, M = let(Y, T1, X, M0) ),
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

% the parent is the hypothesis X : F, its formula or the type of its clause
parent(Parent, X, F, let(X, F, app(Parent, [], []), M), M) :-
  step(Parent, Conclusion, _),
  step_type(Conclusion, F0),
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

% the Skolem symbols of G that are not in F
skolem_symbols(F, G, Ss) :-
  findall(S, ( subterm(G, T), functor(T, S, _), introduced(S, skolem), \+ ( subterm(F, U), functor(U, S, _) ) ), Ss0),
  sort(Ss0, Ss).

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

% an atom A of F, and its sign S, where F has the sign S0
signed_atom(~F, S0, A, S) :- !, opposite(S0, S1), signed_atom(F, S1, A, S).
signed_atom((F => G), S0, A, S) :- !, ( opposite(S0, S1), signed_atom(F, S1, A, S) ; signed_atom(G, S0, A, S) ).
signed_atom((F <=> G), _, A, S) :- !, member(S1, [pos, neg]), ( signed_atom(F, S1, A, S) ; signed_atom(G, S1, A, S) ).
signed_atom(F, S0, A, S) :- connective(F, Gs), !, member(G, Gs), signed_atom(G, S0, A, S).
signed_atom(A, S, A, S).

opposite(pos, neg).
opposite(neg, pos).

% a formula conclusion is refuted by one hypothesis, its counterpart; a clause by its literals
conclusion(Ctx, H, [Y-G], M) :- !, pair(Ctx, H, Y-G, M).
conclusion(Ctx, H, Hs, M) :- keyed(Ctx, Hs, Pool), close(Ctx, [H], Pool, M).

/********************************************************************************
 * pairing counterparts: Ctx is ctx(Mode, Fresh, Defs), with Fresh the next eigenvariable
 ********************************************************************************/

pair(_, X-F, _, M) :- closes(F, X, M), !.
pair(_, _, Y-G, M) :- closes(G, Y, M), !.
pair(_, X-F, Y-G, M) :- literal(F), literal(G), !, refutes(G, Y, F, R), !, applied(R, X, M).
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, X-F, Y-G, M), !.
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, Y-G, X-F, M), !.
pair(Ctx, X-F, Y-G, M) :- skolemised(Ctx, X-F, [G], H, M, M1), pair(Ctx, H, Y-G, M1), !.
pair(Ctx, X-F, Y-G, M) :- skolemised(Ctx, Y-G, [F], H, M, M1), pair(Ctx, X-F, H, M1), !.
pair(Ctx, X-F, Y-G, M) :- alpha_like(F), !, pool(Ctx, [X-F], Pool, M, M1), close(Ctx, [Y-G], Pool, M1).
pair(Ctx, X-F, Y-G, M) :- alpha_like(G), !, pool(Ctx, [Y-G], Pool, M, M1), close(Ctx, [X-F], Pool, M1).
pair(Ctx, X-F, Y-G, M) :- split(X-F, Branches, M), !, branches(Ctx, Branches, Y-G).
pair(Ctx, X-F, Y-G, M) :- split(Y-G, Branches, M), branches(Ctx, Branches, X-F).

% the parts of each branch are the pool of the other formula
branches(_, [], _).
branches(Ctx, [Es-M|Branches], H) :-
  pool(Ctx, Es, Pool, M, M1),
  close(Ctx, [H], Pool, M1),
  branches(Ctx, Branches, H).

% D : δ formula, and G its counterpart, a γ formula: the eigenvariables of the one, but for those
% that are vacuous, are the variables of the other, in order. Either may be vacuous, and the other
% not a quantifier at all. In Skolemisation, a ? of the parent may come between its universals, so
% only as many δ formulas are opened as there are universals
quantifiers(ctx(Mode, Fresh0, Defs), D, G, M) :-
  universals(G, Vs0, G1, M1, M2),
  limit(Mode, Vs0, Limit),
  existentials(Mode, Fresh0-Fresh, Limit, D, Es0, D1, M, M1),
  ( Es0 = [_|_] ; Vs0 = [_|_] ), !,
  D1 = _-F1, G1 = _-T1,
  occurring(Es0, F1, Es),
  occurring(Vs0, T1, Vs),
  Vs = Es,
  pair(ctx(Mode, Fresh, Defs), G1, D1, M2).

limit(skolem(_), Vs, Vs) :- !.
limit(_, _, unlimited).

% the δ formulas nested outermost in X : F, up to the Limit, with an eigenvariable for each
% variable, are Y : G; a conjunction of one part and units of the key (a pure atom, as $true) is that
% part, so ?[X] : (p(X) & ?[Y] : q(X,Y)) opens as ?[X,Y] : q(X,Y)
existentials(Mode, Fresh0-Fresh, Limit0, X-F, [E|Es], H, app(Rule, [], [X, lam(E, S, lam(Y, '$inferred', M0))]), M) :-
  fewer(Limit0, Limit),
  delta(F, Rule, B:S, T0), !,
  E = '$VAR'(Fresh0),
  Fresh1 is Fresh0 + 1,
  substitute(B, E, T0, T),
  existentials(Mode, Fresh1-Fresh, Limit, Y-T, Es, H, M0, M).
existentials(Mode, Fresh0-Fresh, Limit, X-F, Es, H, M, M1) :-
  alpha(F, _, _),
  expansion(F, X, Parts, M, M0),
  partition(unit(Mode), Parts, [_|_], [Part]), !,
  existentials(Mode, Fresh0-Fresh, Limit, Part, Es, H, M0, M1).
existentials(_, Fresh-Fresh, _, H, [], H, M, M).

unit(Mode, _-F) :- normal(Mode, F, '$true').

fewer(unlimited, unlimited).
fewer([_|Limit], Limit).

% the γ formulas nested outermost in X : F, with fresh variables Vs, are Y : G
universals(X-'!'(Bs, F), Vs, H, let(Y, G, app(X, Us, []), M0), M) :- !,
  instance(Bs, F, Us, G),
  universals(Y-G, Ws, H, M0, M),
  append(Us, Ws, Vs).
universals(X-(~'?'(Bs, F)), Vs, H, let(Y, T, app('$nex', [], [X]), M0), M) :- !,
  T = '!'(Bs, ~F),
  universals(Y-T, Vs, H, M0, M).
universals(H, [], H, M, M).

% the body F of a quantifier with its bound variables replaced by fresh variables Us
instance([], F, [], F).
instance([X:_|Bs0], F0, [U|Us], F) :-
  substitute(X, U, Bs0-F0, Bs-F1),
  instance(Bs, F1, Us, F).

% the pool: the parts of conjunctions, each with the key of its complement (and in nnf, its own)
pool(Ctx, Hs, Pool, M, M1) :- parts(Hs, Ps, M, M1), keyed(Ctx, Ps, Pool).

keyed(_, [], []).
keyed(Ctx, [X-F|Hs], [keys(K, K1)-X-F|Pool]) :-
  Ctx = ctx(Mode, _, _),
  normal(Mode, ~F, K),
  ( Mode == nnf -> normal(Mode, F, K1) ; true ),
  keyed(Ctx, Hs, Pool).

% the counterpart Y : G of F in the pool, whose key is that of ~F. In nnf, the negation of an expanded
% <=> is a disjunction of conjunctions, but ~(F <=> G) is expanded as a conjunction, so F is also
% compared the other way round. Skolem keys forget terms, so there each counterpart is tried
counterpart(skolem(Ss), F, Pool, Y-G) :- !, normal(skolem(Ss), F, K), member(keys(K, _)-Y-G, Pool).
counterpart(Mode, F, Pool, Y-G) :- normal(Mode, F, K), memberchk(keys(K, _)-Y-G, Pool), !.
counterpart(nnf, F, Pool, Y-G) :- normal(nnf, ~F, K), memberchk(keys(_, K)-Y-G, Pool).

% the hypotheses Hs expanded as conjunctions, as far as they go
parts([], [], M, M).
parts([X-F|Hs], Ps, M, M1) :-
  (   expansion(F, X, Es, M, M0)
  ->  append(Es, Hs, Hs1), parts(Hs1, Ps, M0, M1)
  ;   Ps = [X-F|Ps1], parts(Hs, Ps1, M, M1)
  ).

% the branch closes by itself, or one of its formulas has a counterpart in the pool, or one of them
% is expanded or split. A disjunction is not looked up: its counterpart is a conjunction, whose parts
% are in the pool already. In Skolemisation, it may be a ? of the parent, not yet opened, and as keys
% forget terms, each counterpart is tried, and then the other ways to close the branch
close(_, Branch, _, M) :- member(X-F, Branch), closes(F, X, M), !.
close(_, _, Pool, M) :- member(_-X-F, Pool), closes(F, X, M), !.
close(Ctx, Branch, Pool, M) :-
  Ctx = ctx(skolem(Ss), _, _),
  member(X-F, Branch),
  counterpart(skolem(Ss), F, Pool, Y-G),
  pair(Ctx, X-F, Y-G, M), !.
close(Ctx, Branch, Pool, M) :-
  Ctx = ctx(Mode, _, _),
  Mode \= skolem(_),
  member(X-F, Branch),
  \+ disjunctive(Mode, F),
  counterpart(Mode, F, Pool, Y-G), !,
  pair(Ctx, X-F, Y-G, M).
close(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  expansion(F, X, Es, M, M1), !,
  append(Es, Rest, Branch1),
  close(Ctx, Branch1, Pool, M1).
close(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  findall(G, member(_-_-G, Pool), Gs),
  skolemised(Ctx, X-F, Gs, H, M, M1),
  close(Ctx, [H|Rest], Pool, M1), !.
close(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  split(X-F, Branches, M), !,
  close_branches(Ctx, Branches, Rest, Pool).

close_branches(_, [], _, _).
close_branches(Ctx, [Es-M|Branches], Rest, Pool) :-
  append(Es, Rest, Branch),
  close(Ctx, Branch, Pool, M),
  close_branches(Ctx, Branches, Rest, Pool).

/********************************************************************************
 * Skolemisation
 ********************************************************************************/

% the δ formula X : F is opened by the choice of a Skolem term sK(As), of a symbol Ss, in the
% formulas Gs, as Y : T[sK(As)/B]. Its arguments As are distinct eigenvariables, among them those of
% F, and sK is not in F, whose choice it is; its definition agrees with any other in Defs
skolemised(ctx(skolem(Ss), _, Defs), X-F, Gs, Y-T1, let(Y, T1, app(Name, As, [X]), M), M) :-
  delta(F, _, B:_, T),
  ground(F),
  eigenvariables_in(F, Vs, []),
  findall(U, ( subterm(Gs, U), functor(U, Sk, _), memberchk(Sk, Ss) ), Us0),
  sort(Us0, Us),
  member(Term, Us),
  Term =.. [Sk|As],
  distinct_eigenvariables(As),
  each_member(Vs, As),
  \+ ( subterm(F, U), functor(U, Sk, _) ),
  plausible(Ss, B, T, Term, Gs),
  defined(Defs, Sk, As, F),
  substitute(B, Term, T, T1),
  choice_name(Sk, Name).

% Term might be chosen for B in T: each atom of T in which B occurs is an atom of Gs with Term in
% its place, up to other Skolem terms, variables, and the orientation of equations. This
% prunes the choices early, as several ? may be Skolemised at once
plausible(Ss, B, T, Term, Gs) :-
  findall(K, ( signed_atom(T, pos, A, _), occurs(B, A), substitute(B, '$chosen', A, A1), blur(Ss, A1, K) ), Ks0),
  sort(Ks0, Ks),
  findall(K, ( member(G, Gs), signed_atom(G, pos, A, _), occurs(Term, A), substitute(Term, '$chosen', A, A1), blur(Ss, A1, K) ), Ls0),
  sort(Ls0, Ls),
  each_atom(Ks, Ls).

each_atom([], _).
each_atom([K|Ks], Ls) :- ( memberchk(K, Ls) -> true ; flip(K, K1), memberchk(K1, Ls) ), each_atom(Ks, Ls).

% variables (bound, or eigenvariables) and Skolem terms are '$skolem'
blur(_, '$BOUND'(_), '$skolem') :- !.
blur(_, '$VAR'(_), '$skolem') :- !.
blur(Ss, T, '$skolem') :- functor(T, F, _), memberchk(F, Ss), !.
blur(_, T, T) :- \+ compound(T), !.
blur(Ss, T0, T) :- T0 =.. [F|As0], maplist(blur(Ss), As0, As), T =.. [F|As].

distinct_eigenvariables([]).
distinct_eigenvariables([A|As]) :- nonvar(A), A = '$VAR'(_), \+ memberchk(A, As), distinct_eigenvariables(As).

each_member([], _).
each_member([V|Vs], As) :- memberchk(V, As), each_member(Vs, As).

% sK(As) is defined by F, as in Defs, or as a new definition at its end
defined(Defs, Sk, As, F) :- var(Defs), !, Defs = [def(Sk, As, F)|_].
defined([def(Sk1, As1, F1)|_], Sk, As, F) :- Sk1 == Sk, !, abstracted(As1, F1, Ws, G), abstracted(As, F, Ws, G).
defined([_|Defs], Sk, As, F) :- defined(Defs, Sk, As, F).

% F with the eigenvariables As replaced by the variables Ws
abstracted([], F, [], F).
abstracted([A|As], F0, [W|Ws], F) :- substitute(A, W, F0, F1), abstracted(As, F1, Ws, F).

choice_name(Sk, Name) :- atom_concat(Sk, '_def', Name).

% each definition is recorded as a step, whose conclusion is its choice axiom, with its eigenvariables
% renumbered from 0, and of the sorts of the arguments of its symbol
choices(Defs) :- var(Defs), !, Defs = [].
choices([]).
choices([def(Sk, As, F0)|Defs]) :-
  abstracted(As, F0, Xs, F1),
  number_vars(Xs, 0, _),
  canonical(F1, F),
  symbol(Sk, Ps, Args, _),
  append(Ps, _, Xs),
  findall('$tType', member(_, Ps), Ts),
  append(Ts, Args, Sorts),
  binders(Xs, Sorts, Bs),
  choice_axiom(Sk, Bs, F, A0),
  canonical(A0, A),
  choice_name(Sk, Name),
  record(step(Name, formula(A), skolem_def(Sk, Bs, F))),
  record(ir_step(Name, formula(A), skolem_def(Sk, Bs, F))),
  choices(Defs).

binders([], [], []).
binders([X|Xs], [S|Ss], [X:S|Bs]) :- binders(Xs, Ss, Bs).

/********************************************************************************
 * clausification
 ********************************************************************************/

clausify(_, Hs, [Parent], M) :-
  parent(Parent, X, F, M, M1),
  refuted(X-F, Hs, M1).

refuted(H, Hs, M) :-
  findall(S-N/K, ( member(_-(~L), Hs), signed_atom(L, pos, A, S), functor(A, N, K) ), Sig0),
  sort(Sig0, Sig),
  refute(H, Hs, Sig, M).

% X : F is refuted by the hypotheses Hs, for literals of the signs and predicates Sig
refute(X-F, _, _, M) :- closes(F, X, M), !.
refute(X-F, Hs, _, M) :- literal(F), !, matches(Hs, F, R), applied(R, X, M).
refute(H, Hs, Sig, M) :- universals(H, [_|_], H1, M, M1), !, refute(H1, Hs, Sig, M1).
refute(X-F, Hs, Sig, M) :-
  expansion(F, X, Es, M, M1), !,
  refute_one(Es, Hs, Sig, M1).
refute(H, Hs, Sig, M) :-
  split(H, Branches, M),
  refute_branches(Branches, Hs, Sig).

% one of the parts Ps is refuted: the last needs no check, as the others are tried first
refute_one(Ps, Hs, Sig, M) :-
  append(_, [X-F|Rest], Ps),
  ( Rest == [] -> true ; fits(F, Sig) ),
  refute(X-F, Hs, Sig, M).

refute_branches([], _, _).
refute_branches([Es-M|Branches], Hs, Sig) :-
  refute_one(Es, Hs, Sig, M),
  refute_branches(Branches, Hs, Sig).

% F might be refuted by literals of the signs and predicates Sig: a literal is, a conjunction if one
% of its parts is, and a disjunction if each branch is
fits('$false', _) :- !.
fits(~'$true', _) :- !.
fits(~'$='(_, _, _), _) :- !.
fits(F, Sig) :- literal(F), !, signed_atom(F, pos, A, S), functor(A, N, K), memberchk(S-N/K, Sig).
fits('!'(_, F), Sig) :- !, fits(F, Sig).
fits(~'?'(_, F), Sig) :- !, fits(~F, Sig).
fits(~(~F), Sig) :- !, fits(F, Sig).
fits(F, Sig) :- alpha(F, _, Ts), !, member(T, Ts), fits(T, Sig), !.
fits(F, Sig) :-
  beta(F, _, Ts1, Ts2),
  ( member(T, Ts1), fits(T, Sig) -> true ),
  ( member(U, Ts2), fits(U, Sig) -> true ).

/********************************************************************************
 * the expansion rules (see ir.pl)
 ********************************************************************************/

closes('$false', X, X).
closes(~'$true', X, app(X, [], [app('$trivial', [], [])])).

literal(~A) :- !, \+ connective(A, _).
literal(A) :- \+ connective(A, _).

alpha_like(F) :- alpha(F, _, _), !.
alpha_like(~(~_)).

% a disjunction, whose counterpart is a conjunction (but in nnf, <=> is a conjunction when expanded)
disjunctive(Mode, F) :- Mode \== nnf, beta(F, Rule, _, _), Rule \== '$iff', Rule \== '$niff'.

% X : F is expanded at once, to the hypotheses Es: M is M1 : ⊥ with these bound
expansion(F, X, Es, app(Rule, [], [X, K]), M) :-
  alpha(F, Rule, Ts), !,
  entries(Ts, Es),
  inferred_lambdas(Es, M, K).
expansion(~(~F), X, [Y-F], app(X, [], [lam(Y, '$inferred', M)]), M).

% X : F is split into branches Es-M, each M : ⊥ with the hypotheses Es bound
split(X-F, [Es1-M1, Es2-M2], app(Rule, [], [X, K1, K2])) :-
  beta(F, Rule, Ts1, Ts2),
  entries(Ts1, Es1),
  entries(Ts2, Es2),
  inferred_lambdas(Es1, M1, K1),
  inferred_lambdas(Es2, M2, K2).

% M abstracted over the hypotheses Es, whose types follow from the rule (see ir.pl): annotating each
% with its formula would make terms quadratic in the size of a conjunction
inferred_lambdas([], M, M).
inferred_lambdas([X-_|Es], M, lam(X, '$inferred', N)) :- inferred_lambdas(Es, M, N).

% a hypothesis for each formula
entries([], []).
entries([T|Ts], [_-T|Es]) :- entries(Ts, Es).

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
