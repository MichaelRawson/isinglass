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
a δ formula of the parent ?[Y] : T (the prover Skolemises in negation normal form, so not ~!). The
Skolem symbols are those of the conclusion that are not in the parent; their keys forget them
(normal.pl). A δ formula of the parent is opened by the choice axiom of a Skolem term in its counterpart (skolem_def, see ir.pl):
the term is read off the conclusion, so no convention of the prover is assumed. The definitions
that the proof uses are recorded as steps, before the step itself.

clausify: the conclusion is a clause of the conjunctive normal form of the parent. The literals of the
conclusion refute the parent: one part of a conjunction, every branch of a disjunction, and a literal
by unification. The only search is the choice of part, of those that can be refuted by literals of
the clause's predicates and signs.
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
conclusion(Ctx, H, Hs, M) :- keyed(Ctx, Hs, Pool), close(Ctx, H, Pool, M).

/********************************************************************************
 * pairing counterparts: Ctx is ctx(Mode, Fresh, Defs), with Fresh the next eigenvariable
 ********************************************************************************/

pair(_, X-F, _, M) :- closes(F, X, M), !.
pair(_, _, Y-G, M) :- closes(G, Y, M), !.
% ...or the one is the negation of the other, as they are (canonical), before either is taken apart:
% a chain of <=> splits into exponentially many branches
pair(_, X-F, Y-G, app(Y, [], [X])) :- G == ~F, !.
pair(_, X-F, Y-G, app(X, [], [Y])) :- F == ~G, !.
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
existentials(Mode, Fresh0-Fresh, Limit0, X-F, [E|Es], H, app(Rule, [], [X, lam(E, S, lam(Y, '$inferred', M0))]), M) :-
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
universals(X-F0, Vs, H, let(Y, G, app(X, Us, []), M0), M) :-
  quantifier_prefix('!', F0, Bs, F), Bs = [_|_], !,
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
% branch does (closed/5)
close(_, _, Pool, M) :- member(_-X-F, Pool), closes(F, X, M), !.
% ...or a part of the pool is false by its key, as is ~($true & $true), and is refuted by itself
close(Ctx, _, Pool, M) :- member(keys('$true', _, _)-X-F, Pool), closed(Ctx, [X-F], [], [], M), !.
close(Ctx, H, Pool, M) :- closed(Ctx, [H], [], Pool, M).

% the branch New and Old is closed: one of the New formulas closes by itself, or has a counterpart in
% the pool, or else one of the branch is taken apart. The Old ones have neither, and as the pool stays
% the same while the branch is taken apart, they are not looked up again: so each key is computed
% once. A disjunction is looked up only if its counterpart is a δ formula, whose binders are vacuous
% (~![X] : (b => c) for b => c): otherwise it is a conjunction, whose parts are in the pool already.
% In Skolemisation, it may be a ? of the parent, not yet opened, and as keys forget terms, each
% counterpart is tried, and then the other ways to close the branch
closed(_, New, _, _, M) :- member(X-F, New), closes(F, X, M), !.
closed(Ctx, New, _, Pool, M) :-
  Ctx = ctx(skolem(Ss), _, _),
  member(X-F, New),
  normal(skolem(Ss), F, K),
  member(keys(K, _, _)-Y-G, Pool),
  pair(Ctx, X-F, Y-G, M), !.
closed(Ctx, New, _, Pool, M) :-
  Ctx = ctx(Mode, _, _),
  Mode \= skolem(_),
  member(X-F, New),
  lookup_pool(Mode, F, Pool, Pool1),
  counterpart(Mode, F, Pool1, Y-G), !,
  pair(Ctx, X-F, Y-G, M).
closed(Ctx, New, Old, Pool, M) :-
  append(New, Old, Branch),
  taken_apart(Ctx, Branch, Pool, M).

% a formula of the branch is expanded, opened or split, and its parts are new. The opening of a δ
% formula whose term is the prover's choice (Hinted) is not undone, as the order in which δ formulas
% of a branch are opened does not matter, and backtracking over it would try them in every order when
% a branch does not close
taken_apart(Ctx, Branch, Pool, M) :-
  select(X-F, Branch, Rest),
  expansion(F, X, Es, M, M1), !,
  closed(Ctx, Es, Rest, Pool, M1).
taken_apart(Ctx, Branch, Pool, M) :-
  Ctx = ctx(skolem(_), _, _),
  findall(G, member(_-_-G, Pool), Gs),
  select(X-F, Branch, Rest),
  skolemised(Ctx, X-F, Gs, H, Hinted, M, M1),
  ( Hinted == true -> ! ; true ),
  closed(Ctx, [H], Rest, Pool, M1), !.
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
  closed(Ctx, Es, Rest, Pool, M),
  close_branches(Ctx, Branches, Rest, Pool).

/********************************************************************************
 * Skolemisation
 ********************************************************************************/

% the δ formula X : F is opened by the choice of a Skolem term sK(As), of a symbol Ss, in the
% formulas Gs, as Y : T[sK(As)/B]. Its arguments As are distinct eigenvariables, among them those of
% F, and sK is not in F, whose choice it is; its definition agrees with any other in Defs
skolemised(Ctx, H0, Gs, H, M, M1) :- skolemised(Ctx, H0, Gs, H, _, M, M1).

% ...and Hinted is true if the term is the prover's choice
skolemised(ctx(skolem(Ss), _, Defs), X-F, Gs, Y-T1, Hinted, let(Y, T1, app(Name, As, [X]), M), M) :-
  delta(F, '$ex', B:_, T),
  ground(F),
  eigenvariables_in(F, Vs, []),
  candidates(Ss, F, B, T, Gs, Hinted, Us),
  member(Term, Us),
  Term =.. [Sk|As],
  distinct_eigenvariables(As),
  each_member(Vs, As),
  \+ ( subterm(F, U), functor(U, Sk, _) ),
  ( Hinted == true -> true ; plausible(Ss, B, T, Term, Gs) ),
  defined(Defs, Sk, As, F),
  substitute(B, Term, T, T1),
  choice_name(Sk, Name).

% the candidate Skolem terms Us for the δ formula F (? B : T), of the symbols Ss in the
% formulas Gs. If the prover says which symbol is its choice (db.pl), only its terms, so that a δ formula
% paired with the wrong counterpart fails at once, without a search through all of Gs: this saves the
% search in a formula of many similar parts (LCL670+1.005: chains of r1(X, Y) under nested ?). Without
% a hint, or for a vacuous B (whose term need not be in the conclusion), every term of Gs, Hinted is
% false, and a term must be plausible. A term is still checked as any other
candidates(_, F, B, T, Gs, true, Us) :-
  occurs(B, T),
  findall(Sk, ( skolem_hint(Sk, D), D = F ), Hints),
  Hints = [_|_], !,
  findall(U, ( subterm(Gs, U), functor(U, Sk, _), memberchk(Sk, Hints) ), Us0),
  sort(Us0, Us).
candidates(Ss, _, _, _, Gs, false, Us) :-
  findall(U, ( subterm(Gs, U), functor(U, Sk, _), get_assoc(Sk, Ss, _) ), Us0),
  sort(Us0, Us).

% Term might be chosen for B in T: each atom of T in which B occurs is an atom of Gs with Term in
% its place, up to other Skolem terms, variables, and the orientation of equations. This
% prunes the choices early, as several ? may be Skolemised at once. Skolem terms already chosen,
% which are in T, are kept: so X1 = f(X0), with sK0 chosen for X0, is sK0's sK1 = f(sK0) only
plausible(Ss, B, T, Term, Gs) :-
  findall(S, ( subterm(T, U), functor(U, S, _), get_assoc(S, Ss, _) ), Chosen0),
  sort(Chosen0, Chosen),
  Open = Ss-Chosen,
  findall(K, ( signed_atom(T, pos, A, _), occurs(B, A), substitute(B, '$chosen', A, A1), blur(Open, A1, K) ), Ks0),
  sort(Ks0, Ks),
  findall(K, ( member(G, Gs), signed_atom(G, pos, A, _), occurs(Term, A), substitute(Term, '$chosen', A, A1), blur(Open, A1, K) ), Ls0),
  sort(Ls0, Ls),
  each_atom(Ks, Ls).

each_atom([], _).
each_atom([K|Ks], Ls) :- ( memberchk(K, Ls) -> true ; flip(K, K1), memberchk(K1, Ls) ), each_atom(Ks, Ls).

% variables (bound, or eigenvariables) and terms of the Skolem symbols Ss but not Chosen are '$skolem'
blur(_, '$BOUND'(_), '$skolem') :- !.
blur(_, '$VAR'(_), '$skolem') :- !.
blur(Ss-Chosen, T, '$skolem') :- functor(T, F, _), get_assoc(F, Ss, _), \+ memberchk(F, Chosen), !.
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
  head_type(Rule, (F => ('!'([B], (T => '$false')) => '$false'))), !.
