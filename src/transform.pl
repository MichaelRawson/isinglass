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
transform(Mode, Fresh, Hs, [Parent], M) :-
  parent(Parent, X, F, M, M1),
  eigenvariables(Hs, Es),
  (   instantiated(Es, X-F, H, M1, M2)
  ->  transformed(Mode, Fresh, H, Hs, M2)
  ;   refuted(X-F, Hs, M1)
  ).

transformed(Mode0, Fresh, H, Hs, M) :-
  H = _-F,
  goal(Hs, G),
  weakened(Mode0, F, G, F1, Mode),
  normal(Mode, G, K),
  normal(Mode, F1, K), !,
  conclusion(ctx(Mode, Fresh), H, Hs, M).

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

% a clause conclusion instantiates the outermost universal variables of the parent
instantiated([], H, H, M, M) :- !.
instantiated(Es, H0, H, M, M1) :-
  universals(H0, Vs, H, M, M1),
  H = _-F,
  occurring(Vs, F, Es).

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
 * pairing counterparts: Ctx is ctx(Mode, Fresh), with Fresh the next eigenvariable
 ********************************************************************************/

pair(_, X-F, _, M) :- closes(F, X, M), !.
pair(_, _, Y-G, M) :- closes(G, Y, M), !.
pair(_, X-F, Y-G, M) :- literal(F), literal(G), !, refutes(G, Y, F, R), !, applied(R, X, M).
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, X-F, Y-G, M), !.
pair(Ctx, X-F, Y-G, M) :- quantifiers(Ctx, Y-G, X-F, M), !.
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
% not a quantifier at all
quantifiers(ctx(Mode, Fresh0), D, G, M) :-
  existentials(Fresh0, D, Es0, D1, Fresh, M, M1),
  universals(G, Vs0, G1, M1, M2),
  ( Es0 = [_|_] ; Vs0 = [_|_] ), !,
  D1 = _-F1, G1 = _-T1,
  occurring(Es0, F1, Es),
  occurring(Vs0, T1, Vs),
  Vs = Es,
  pair(ctx(Mode, Fresh), G1, D1, M2).

% the δ formulas nested outermost in X : F, with an eigenvariable for each variable, are Y : G
existentials(Fresh0, X-F, [E|Es], H, Fresh, app(Rule, [], [X, lam(E, S, lam(Y, '$inferred', M0))]), M) :-
  delta(F, Rule, B:S, T0), !,
  E = '$VAR'(Fresh0),
  Fresh1 is Fresh0 + 1,
  substitute(B, E, T0, T),
  existentials(Fresh1, Y-T, Es, H, Fresh, M0, M).
existentials(Fresh, H, [], H, Fresh, M, M).

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
  Ctx = ctx(Mode, _),
  normal(Mode, ~F, K),
  ( Mode == nnf -> normal(Mode, F, K1) ; true ),
  keyed(Ctx, Hs, Pool).

% the counterpart Y : G of F in the pool, whose key is that of ~F. In nnf, the negation of an expanded
% <=> is a disjunction of conjunctions, but ~(F <=> G) is expanded as a conjunction, so F is also
% compared the other way round
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
% are in the pool already
close(_, Branch, _, M) :- member(X-F, Branch), closes(F, X, M), !.
close(_, _, Pool, M) :- member(_-X-F, Pool), closes(F, X, M), !.
close(Ctx, Branch, Pool, M) :-
  Ctx = ctx(Mode, _),
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
  split(X-F, Branches, M), !,
  close_branches(Ctx, Branches, Rest, Pool).

close_branches(_, [], _, _).
close_branches(Ctx, [Es-M|Branches], Rest, Pool) :-
  append(Es, Rest, Branch),
  close(Ctx, Branch, Pool, M),
  close_branches(Ctx, Branches, Rest, Pool).

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
