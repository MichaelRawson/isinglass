% Vampire front end: interpret TSTP statements as step/3 facts
:- module(vampire, [load_vampire/1]).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(utils).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(signature).
:- use_module(ir).

% type declarations first, so that every equation can be given its sort
load_vampire(Statements) :-
  each(member(annotated(_, _, type, Type, _), Statements), declare(Type)),
  polarity_flipping(Statements, Flipping),
  each(member(Statement, Statements), load_statement(Flipping, Statement)),
  skolem_hints(Statements).

load_statement(_, annotated(_, _, type, _, _)) :- !.
load_statement(Flipping, annotated(Language, Name, Role, Formula0, Source0)) :-
  typed([], Formula0, Formula1),
  flipped_statement(Flipping, Name, Source0, Formula1, Source, Formula2),
  definition_statement(Source, Formula2, Formula),
  how(Role, Source, Formula, How),
  conclusion(Language, How, Formula, Conclusion),
  record_introduced(Source),
  record(step(Name, Conclusion, How)).

% $false is the empty clause, and a clause-shaped cnf statement is a clause; variables are kept as
% Prolog variables. Vampire prints clauses as fof (or tff) statements, so one is a clause only
% if it is clause-shaped and either an input (back ends derive its clause type from its formula by
% cases, for any ⊥) or derived by clausal reasoning; the conjecture, its negation, preprocessing and
% definitions are formulas
conclusion(_, _, '$false', C) :- !, C = clause([], []).
conclusion(Language, How, F, C) :-
  clausal(Language, How),
  \+ quantified_disjunct(How, F),
  formula_clause(F, C0), !,
  C = C0.
conclusion(_, _, F, formula(F)).

% a Skolemised formula (! [X] : C) | L stays a formula, as the δ formula of its parent is under the
% disjunction too, and only formulas are paired part by part (transform.pl)
quantified_disjunct(tactic(transform(skolem), _), (F | G)) :- \+ \+ ( subterm((F | G), Q), Q = '!'(_, _) ).

clausal(cnf, _).
clausal(Language, How) :- ( Language == fof ; Language == tff ), clausal_step(How).

clausal_step(input(_, _)).
clausal_step(define(_)).
clausal_step(tactic(_, _)).
clausal_step(todo(cnf_transformation, _)) :- !.
% an unknown rule from clauses only
clausal_step(todo(Rule, Parents)) :-
  atom(Rule),
  Parents \== [],
  each(member(P, Parents), step(P, clause(_, _), _)).

% the conjecture is a goal, proved by refuting its negation, a hypothesis (see reconstruct.pl);
% steps that only preserve satisfiability (status esa) introduce symbols, and are not entailments,
% unless a tactic defines the symbols (Skolemisation, by choice: see transform.pl)
how(conjecture, file(_, Input), _, conjecture(Input)) :- !.
how(Role, file(_, Input), _, input(Role, Input)) :- !.
how(_, introduced(definition, Info, [Kind]), _, define(Symbol)) :-
  ( Kind == function_definition ; Kind == avatar_definition ),
  new_symbols(Info, [Symbol]), !.
how(_, introduced(definition, Info, [Kind]), F, tactic(Tactic, [Name])) :-
  new_symbols(Info, [Symbol]),
  predicate_definition(Kind, F, Symbol, _, Tactic), !,
  definition_name(Symbol, Name).
how(_, introduced(theory, [theory_tautology_sat_conflict], []), _, tactic(tautology, [])) :- !.
how(_, introduced(definition, Info, _), _, todo(esa(definition, Symbols), [])) :- !,
  new_symbols(Info, Symbols).
how(_, inference(Rule, _, [Conjecture]), _, negated_conjecture(Conjecture)) :-
  negation_rule(Rule), !.
how(_, inference(definition_folding, _, [Parent|Definitions]), _, tactic(fold, [Parent|Definitions])) :-
  step(Parent, clause(_, _), _),
  Definitions \== [],
  each(member(D, Definitions), function_definition(D)), !.
how(_, inference(definition_folding, _, [Parent|Definitions]), _, tactic(transform(fold), [Parent|Definitions])) :-
  step(Parent, formula(_), _),
  Definitions \== [],
  each(member(D, Definitions), from_definition(D)), !.
how(_, inference(Rule, Info, Parents), _, todo(esa(Rule, Symbols), Parents)) :-
  \+ tactic(Rule, _),
  ( memberchk(status(esa), Info) ; esa(Rule) ), !,
  new_symbols(Info, Symbols).
how(_, inference(cnf_transformation, _, [Parent]), _, How) :-
  clausification(Parent, How), !.
how(_, inference(Rule, _, [Parent]), ~A, How) :-
  tactic(Rule, transform(_)),
  \+ connective(A, _),
  denied(Parent, Negated), !,
  How = tactic(deny, [Negated]).
how(_, inference(Rule, _, Parents), _, How) :-
  tactic(Rule, Tactic), !,
  How = tactic(Tactic, Parents).
how(_, inference(Rule, _, Parents), _, todo(Rule, Parents)) :- !.
how(_, Source, _, todo(Source, [])).

% clausification of a clause only reorders it, and the negated conjecture of an atom is denied
% directly, as is its preprocessing, so that these steps stay constructive; otherwise clausification
% and preprocessing are steps between formulas (transform.pl)
clausification(Parent, tactic(variant, [Parent])) :- step(Parent, clause(_, _), _), !.
clausification(Parent, tactic(deny, [Negated])) :- denied(Parent, Negated), !.
clausification(Parent, tactic(clausify, [Parent])).

% Name is the negated conjecture Negated, of an atom, or denies it
denied(Name, Negated) :-
  denial(Name, Negated),
  step(Negated, formula(~G), _),
  \+ connective(G, _).

denial(Name, Name) :- step(Name, _, negated_conjecture(_)), !.
denial(Name, Negated) :- step(Name, _, tactic(deny, [Negated])), !.
denial(Name, Negated) :- step(Name, formula(_), todo(_, [Parent])), denial(Parent, Negated).

% a unit equation, one side of which is a term of a function symbol introduced by definition
function_definition(Name) :-
  step(Name, clause(_, ['$='(_, A, B)]), _),
  ( defined_term(A) ; defined_term(B) ), !.

defined_term(T) :- nonvar(T), functor(T, F, _), introduced(F, definition).

% a step that follows from the definition of a predicate
from_definition(Name) :- step(Name, _, tactic(_, [D])), step(D, formula(_), define(_)).

/*
A predicate definition is printed as Vampire uses it: as Symbol(Xs) <=> Body, in one direction only,
Body | ~Symbol(Xs), for an inequality split, ~Symbol(T), where Symbol(X) is X != T, or for a general
split, C <=> ~Symbol(Xs). The definition itself, ![Xs] : (Symbol(Xs) <=> Body), is recorded first, as
the step Symbol_def, and the printed statement is proved from it by the Tactic.
An AVATAR split Symbol <=> C is a definition itself, once restated as Symbol <=> T, for the type T of the
clause C (ir:clause_type/2); C is recorded for the AVATAR tactics, as split(Symbol, C)
*/
definition_statement(introduced(definition, _, [avatar_definition]), (Symbol <=> Component), F) :-
  formula_clause(Component, C), !,
  record(split(Symbol, C)),
  clause_type(C, T),
  F = (Symbol <=> T).
definition_statement(introduced(definition, Info, [Kind]), F0, F) :-
  new_symbols(Info, [Symbol]),
  predicate_definition(Kind, F0, Symbol, Definition0, _), !,
  argument_order(Definition0, Definition),
  same_binders(F0, Definition, F),
  definition_name(Symbol, Name),
  record(step(Name, formula(Definition), define(Symbol))).
definition_statement(_, F, F).

% the binders of a definition, in the order of the arguments of its atom; the printed statement has its
% binders in the same order, as grouped binders commute
argument_order(D0, D) :-
  quantifier_prefix('!', D0, Bs0, (A <=> B)), Bs0 = [_|_], !,
  A =.. [_|Xs],
  maplist(binder_of(Bs0), Xs, Bs),
  quantify('!', Bs, (A <=> B), D).
argument_order(D, D).

binder_of(Bs, X, Y:S) :- member(Y:S, Bs), Y == X, !.

same_binders(F0, D, F) :-
  quantifier_prefix('!', D, Bs, _),
  length(Bs, N), N > 0,
  quantifier_prefix('!', N, F0, _, G), !,
  quantify('!', Bs, G, F).
same_binders(F, _, F).

definition_name(Symbol, Name) :- atom_concat(Symbol, '_def', Name).

predicate_definition(general_splitting_component_introduction, F, Symbol, D, transform(nnf)) :- !,
  quantifier_prefix('!', F, Bs, (C <=> ~A)),
  binder_variables(Bs, Xs),
  definiendum(A, Symbol, Xs),
  component_type(C, T),
  quantify('!', Bs, (A <=> ~T), D).
predicate_definition(_, F0, Symbol, D, Tactic) :-
  quantifier_prefix('!', F0, Bs, F), Bs = [_|_], !,
  binder_variables(Bs, Xs),
  definition_shape(F, Symbol, Xs, D0, Tactic),
  quantify('!', Bs, D0, D).
predicate_definition(inequality_splitting_name_introduction, ~A, Symbol, '!'(X:S, D), defined(tautology)) :-
  A =.. [Symbol, T],
  term_sort([], T, S), !,
  D = (B <=> ~'$='(S, X, T)),
  B =.. [Symbol, X].
predicate_definition(_, F, Symbol, D, Tactic) :- definition_shape(F, Symbol, [], D, Tactic).

% general splitting names a component C of a clause, over the variables Xs that it shares with the
% rest, by ![Xs] : (C <=> ~Symbol(Xs)): Symbol(Xs) is defined as the negation of the type of the clause
% C (ir:clause_type/2), so that a proof refutes ~~Symbol(Xs) as it does an AVATAR split
component_type(C, T) :-
  quantifier_prefix('!', C, Ys, G),
  disjuncts(G, Ls),
  clause_type(clause(Ys, Ls), T).

% Symbol(Xs) <=> Body, where the arguments of the atom are the variables Xs
definition_shape((A <=> B), Symbol, Xs, (A <=> B), transform(base)) :- definiendum(A, Symbol, Xs), !.
definition_shape((B <=> A), Symbol, Xs, (A <=> B), transform(base)) :- definiendum(A, Symbol, Xs), !.
% ...or one way: a disjunction of ~Symbol(Xs) and the disjuncts of Body, anywhere among them
definition_shape(F, Symbol, Xs, (A <=> B), transform(definition)) :-
  disjuncts(F, Ds),
  select(~A, Ds, Bs),
  definiendum(A, Symbol, Xs), !,
  disjunction(Bs, B).

disjuncts((F | G), Ds) :- !, disjuncts(F, Ds0), disjuncts(G, Ds1), append(Ds0, Ds1, Ds).
disjuncts(F, [F]).

definiendum(A, Symbol, Xs) :-
  nonvar(A),
  A =.. [Symbol|As],
  maplist(var, As),
  sort(As, Vs),
  sort(Xs, Vs),
  same_length(As, Vs).

new_symbols(Info, Symbols) :- findall(S, (member(I, Info), introduced_symbol(I, _, S)), Symbols).

% rules that are not entailments, though Vampire does not say so: folding needs the definitions of the
% folded symbols, which are reconstructed above, for functions in clauses and predicates in formulas
esa(definition_folding).

% the rule of the negated conjecture, renamed in later versions of Vampire
negation_rule(negated_conjecture).
negation_rule(conjecture_negation).

/*
Consistent polarity flipping replaces a predicate P by its negation, but keeps its name: so the steps
after it are stated with P_flipped for P, where P_flipped is defined as ~P (the step P_flipped_def).
A flipped predicate of a flipping step is one whose literals in the parent and conclusion differ in
sign. Flipping is flips(Predicates, Before), with Before the steps before flipping (see before/4)
*/
polarity_flipping(Statements, flips(Predicates, Before)) :-
  findall(P-F, member(annotated(_, _, _, F, inference(consistent_polarity_flipping, _, [P])), Statements), Flips),
  findall(Q, ( member(P-F, Flips), memberchk(annotated(_, P, _, F0, _), Statements), flipped_predicate(F0, F, Q) ), Qs),
  sort(Qs, Predicates),
  each(member(Q, Predicates), record_flipped(Q)),
  pairs_keys(Flips, Parents),
  ancestors(Parents, Statements, [], Ancestors),
  empty_assoc(Empty),
  (   Predicates == []
  ->  Before = Empty
  ;   foldl(before(Ancestors), Statements, Empty, Before)
  ).

% a step is before flipping, and so not renamed, if it is an input or an ancestor of a flipping step,
% or derived only from steps before it (e.g. preprocessing of a formula whose clauses are not
% flipped), but for a flipping step. Other steps without parents, such as AVATAR definitions, are
% after it. Vampire prints parents first
before(Ancestors, annotated(_, Name, _, _, Source), Before0, Before) :-
  (   ( memberchk(Name, Ancestors) ; before_source(Source, Before0) )
  ->  put_assoc(Name, Before0, true, Before)
  ;   Before = Before0
  ).

before_source(file(_, _), _).
before_source(inference(Rule, _, [P|Ps]), Before) :-
  Rule \== consistent_polarity_flipping,
  each(member(Q, [P|Ps]), get_assoc(Q, Before, true)).

% the predicate P/N has different signed literals in F0 and F, whose variables are numbered in order:
% flipping changes the sign of each, and a clause has no literal with its complement. Counting the signs
% is not enough, as when one literal of each sign is flipped
flipped_predicate(F0, F, P/N) :-
  setof(P/N, S^A^( signed_atom(F0, S, A), functor(A, P, N) ), Ps),
  member(P/N, Ps),
  signed_literals(F0, P/N, Ls0),
  signed_literals(F, P/N, Ls),
  Ls0 \== Ls.

signed_literals(F0, P/N, Ls) :-
  copy_term(F0, F),
  term_variables(F, Vs),
  number_vars(Vs, 0, _),
  findall(S-A, ( signed_atom(F, S, A), functor(A, P, N) ), Ls1),
  msort(Ls1, Ls).

% a predicate atom A of a formula, positive (+) or negative (-)
signed_atom(F, S, A) :- signed_atom(F, +, S, A).

signed_atom(~F, S0, S, A) :- !, opposite(S0, S1), signed_atom(F, S1, S, A).
signed_atom(F, S0, S, A) :- connective(F, Gs), !, member(G, Gs), signed_atom(G, S0, S, A).
signed_atom(A, S, S, A) :- A \= (_ = _).

opposite(+, -).
opposite(-, +).

% P_flipped(As, Xs) is defined as ~P(As, Xs), of the signature of P, with type parameters As, or of
% individuals if P is untyped
record_flipped(P/N) :-
  flipped_name(P, P1),
  (   symbol(P, As, Ss, '$o')
  ->  record(symbol(P1, As, Ss, '$o'))
  ;   As = [], length(Ss, N), maplist(=('$i'), Ss)
  ),
  same_length(Ss, Xs),
  findall('$tType', member(_, As), Ts),
  maplist(binder, As, Ts, Bs0),
  maplist(binder, Xs, Ss, Bs1),
  append(Bs0, Bs1, Bs),
  append(As, Xs, Args),
  A =.. [P|Args],
  A1 =.. [P1|Args],
  quantify('!', Bs, (A1 <=> ~A), D),
  record(introduced(P1, definition)),
  definition_name(P1, Name),
  record(step(Name, formula(D), define(P1))).

flipped_name(P, P1) :- atom_concat(P, '_flipped', P1).

binder(X, S, X:S).

% the names of the ancestors of steps Ns, by their parents
ancestors([], _, As, As).
ancestors([N|Ns], Statements, As0, As) :-
  (   memberchk(N, As0)
  ->  ancestors(Ns, Statements, As0, As)
  ;   ( memberchk(annotated(_, N, _, _, inference(_, _, Ps)), Statements) -> true ; Ps = [] ),
      append(Ps, Ns, Ns1),
      ancestors(Ns1, Statements, [N|As0], As)
  ).

% a step after flipping is stated with the flipped predicates renamed; inputs and other steps before
% flipping are not; a flipping step cites the definitions too
flipped_statement(flips([], _), _, Source, F, Source, F) :- !.
flipped_statement(_, _, file(N, I), F, file(N, I), F) :- !.
flipped_statement(flips(_, Before), Name, Source, F, Source, F) :- get_assoc(Name, Before, true), !.
flipped_statement(flips(Ps, _), _, Source0, F0, Source, F) :-
  flipped_source(Ps, Source0, Source),
  flipped_formula(Ps, F0, F).

flipped_source(Ps, inference(consistent_polarity_flipping, Info, [Parent]), Source) :- !,
  findall(D, ( member(P/_, Ps), flipped_name(P, P1), definition_name(P1, D) ), Ds),
  Source = inference(consistent_polarity_flipping, Info, [Parent|Ds]).
flipped_source(_, Source, Source).

flipped_formula(Ps, F0, F) :-
  quantifier(F0, Q, B, G0), !,
  flipped_formula(Ps, G0, G),
  F =.. [Q, B, G].
flipped_formula(Ps, F0, F) :-
  connective(F0, _), !,
  F0 =.. [C|Gs0],
  maplist(flipped_formula(Ps), Gs0, Gs),
  F =.. [C|Gs].
flipped_formula(Ps, A0, A) :-
  functor(A0, P, N),
  memberchk(P/N, Ps), !,
  flipped_name(P, P1),
  A0 =.. [P|Ts],
  A =.. [P1|Ts].
flipped_formula(_, A, A).

/*
Skolemisation lists its choices skolemize(X, sK(Ys)), one for each δ binder of the parent, in
preorder: left to right, outermost first (as Vampire does, in negation normal form; the names X and Ys are the
parent's, but read/1 does not keep them). Each is recorded as a hint (db.pl): the δ formula that the
choice of sK opens, the quantifier of X, with the δ formulas around it replaced by their Skolem terms
(of fresh arguments). If the counts differ, the
step has no hints, and transform.pl searches as without them.
*/
skolem_hints(Statements) :-
  each(( member(annotated(_, _, _, _, inference(skolemize, Info, [Parent])), Statements),
         step(Parent, formula(F), _),
         delta_binders(F, Xs, []),
         skolem_symbols(Info, Ts),
         same_length(Xs, Ts),
         pairs_keys_values(Choices, Xs, Ts),
         member(X-T, Choices),
         delta_formula(F, X, D0),
         chosen(Choices, X, D0, D1),
         canonical(D1, D),
         functor(T, Sk, _) ),
       record(skolem_hint(Sk, D))).

% the binders of the ? formulas of F, a formula in negation normal form, in preorder
delta_binders('?'(X:_, G), [X|Xs0], Xs) :- !, delta_binders(G, Xs0, Xs).
delta_binders('!'(_, G), Xs0, Xs) :- !, delta_binders(G, Xs0, Xs).
delta_binders((F | G), Xs0, Xs) :- !, delta_binders(F, Xs0, Xs1), delta_binders(G, Xs1, Xs).
delta_binders((F & G), Xs0, Xs) :- !, delta_binders(F, Xs0, Xs1), delta_binders(G, Xs1, Xs).
delta_binders(_, Xs, Xs).

% the Skolem terms of skolemize(_, T) in Info, in order, each of fresh arguments
skolem_symbols([], []).
skolem_symbols([I|Is], Ts) :-
  (   nonvar(I), I = skolemize(_, T0), callable(T0)
  ->  functor(T0, Sk, N), functor(T, Sk, N), Ts = [T|Ts1]
  ;   Ts = Ts1
  ),
  skolem_symbols(Is, Ts1).

% the δ formula of F that is opened for its binder X: the quantifier of X
delta_formula(F, X, F) :- F = '?'(Y:_, _), Y == X, !.
delta_formula(F, X, D) :- connective(F, Fs), member(G, Fs), delta_formula(G, X, D), !.

% the other choices that are free in the δ formula D (those around it), replaced by their Skolem terms
chosen([], _, D, D).
chosen([Y-T|Choices], X, D0, D) :-
  (   Y \== X, occurs(Y, D0), \+ bound_in(Y, D0)
  ->  substitute(Y, T, D0, D1)
  ;   D1 = D0
  ),
  chosen(Choices, X, D1, D).

bound_in(Y, F) :- quantifier(F, _, Z:_, G), !, ( Z == Y -> true ; bound_in(Y, G) ).
bound_in(Y, F) :- connective(F, Fs), member(G, Fs), bound_in(Y, G), !.

% Vampire inference rules and the generic tactics that reconstruct them
tactic(resolution, resolve).
tactic(forward_subsumption_resolution, resolve).
tactic(backward_subsumption_resolution, resolve).
tactic(unit_resulting_resolution, resolve).
tactic(forward_literal_rewriting, resolve).
tactic(extensionality_resolution, resolve).
tactic(equality_proxy_replacement, defined(variant)).
tactic(inequality_splitting, defined(variant)).
tactic(consistent_polarity_flipping, defined(variant)).
tactic(general_splitting, components).
tactic(equality_proxy_axiom, defined(tautology)).
tactic(factoring, variant).
tactic(duplicate_literal_removal, variant).
tactic(sat_conversion, first([variant, avatar_split])).
tactic(avatar_contradiction_clause, variant).
tactic(avatar_sat_refutation, variant).
tactic(avatar_split_clause, avatar_split).
tactic(avatar_component_clause, avatar_component).
tactic(rat, rup).
tactic(reorient_equations, variant).
tactic(trivial_inequality_removal, variant).
tactic(equality_resolution, variant).
tactic(condensation, variant).
tactic(superposition, paramodulate).
tactic(forward_demodulation, paramodulate).
tactic(backward_demodulation, paramodulate).
tactic(forward_subsumption_demodulation, paramodulate).
tactic(backward_subsumption_demodulation, paramodulate).
tactic(equality_factoring, equality_factor).
tactic(inner_rewriting, equality_factor).
tactic(definition_unfolding, unfold).
tactic(rectify, transform(base)).
tactic(flattening, transform(base)).
tactic(ennf_transformation, transform(ennf)).
tactic(nnf_transformation, transform(nnf)).
tactic(true_and_false_elimination, transform(simplify)).
tactic(pure_predicate_removal, transform(pure)).
tactic(unused_predicate_definition_removal, transform(definition)).
tactic(skolemize, transform(skolem)).

record_introduced(Source) :-
  each(introduced_symbol(Source, Kind, Symbol), record(introduced(Symbol, Kind))).

introduced_symbol(new_symbols(Kind, Symbols), Kind, Symbol) :- member(Symbol, Symbols).
introduced_symbol(inference(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
introduced_symbol(introduced(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
