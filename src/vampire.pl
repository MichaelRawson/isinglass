% Vampire front end: interpret TSTP statements as step/3 facts
:- module(vampire, [load_vampire/1]).
:- use_module(library(lists)).
:- use_module(library(pairs)).
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
  each(member(Statement, Statements), load_statement(Flipping, Statement)).

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
how(_, introduced(definition, _, [avatar_definition]), (Symbol <=> Component), split_def(Symbol, C)) :-
  formula_clause(Component, C), !.
how(_, introduced(definition, Info, [function_definition]), _, define(Symbol)) :-
  new_symbols(Info, [Symbol]), !.
how(_, introduced(definition, Info, [Kind]), F, tactic(Tactic, [Name])) :-
  new_symbols(Info, [Symbol]),
  predicate_definition(Kind, F, Symbol, _, Tactic), !,
  definition_name(Symbol, Name).
how(_, introduced(theory, [theory_tautology_sat_conflict], []), _, tactic(tautology, [])) :- !.
how(_, introduced(definition, Info, _), _, todo(esa(definition, Symbols), [])) :- !,
  new_symbols(Info, Symbols).
how(_, inference(negated_conjecture, _, [Conjecture]), _, negated_conjecture(Conjecture)) :- !.
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
the step Symbol_def, and the printed statement is proved from it by the Tactic
*/
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
argument_order('!'(Bs0, (A <=> B)), '!'(Bs, (A <=> B))) :- !,
  A =.. [_|Xs],
  maplist(binder_of(Bs0), Xs, Bs).
argument_order(D, D).

binder_of(Bs, X, Y:S) :- member(Y:S, Bs), Y == X, !.

same_binders('!'(_, G), '!'(Bs, _), '!'(Bs, G)) :- !.
same_binders(F, _, F).

definition_name(Symbol, Name) :- atom_concat(Symbol, '_def', Name).

predicate_definition(general_splitting_component_introduction, F, Symbol, D, transform(nnf)) :- !,
  ( F = '!'(Bs, (C <=> ~A)) -> true ; F = (C <=> ~A), Bs = [] ),
  binder_variables(Bs, Xs),
  definiendum(A, Symbol, Xs),
  component_type(C, T),
  ( Bs == [] -> D = (A <=> ~T) ; D = '!'(Bs, (A <=> ~T)) ).
predicate_definition(_, '!'(Bs, F), Symbol, '!'(Bs, D), Tactic) :- !,
  binder_variables(Bs, Xs),
  definition_shape(F, Symbol, Xs, D, Tactic).
predicate_definition(inequality_splitting_name_introduction, ~A, Symbol, '!'([X:S], D), defined(tautology)) :-
  A =.. [Symbol, T],
  term_sort([], T, S), !,
  D = (B <=> ~'$='(S, X, T)),
  B =.. [Symbol, X].
predicate_definition(_, F, Symbol, D, Tactic) :- definition_shape(F, Symbol, [], D, Tactic).

% general splitting names a component C of a clause, over the variables Xs that it shares with the
% rest, by ![Xs] : (C <=> ~Symbol(Xs)): Symbol(Xs) is defined as the negation of the type of the clause
% C (ir:clause_type/2), so that a proof refutes ~~Symbol(Xs) as it does an AVATAR split
component_type(C, T) :-
  ( C = '!'(Ys, G) -> true ; Ys = [], G = C ),
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

/*
Consistent polarity flipping replaces a predicate P by its negation, but keeps its name: so the steps
after it, all but its ancestors, are stated with P_flipped for P, where P_flipped is defined as ~P
(the step P_flipped_def). A flipped predicate of a flipping step is one whose literals in the parent
and conclusion differ in sign. Flipping is flips(Predicates, Ancestors)
*/
polarity_flipping(Statements, flips(Predicates, Ancestors)) :-
  findall(P-F, member(annotated(_, _, _, F, inference(consistent_polarity_flipping, _, [P])), Statements), Flips),
  findall(Q, ( member(P-F, Flips), memberchk(annotated(_, P, _, F0, _), Statements), flipped_predicate(F0, F, Q) ), Qs),
  sort(Qs, Predicates),
  each(member(Q, Predicates), record_flipped(Q)),
  pairs_keys(Flips, Parents),
  ancestors(Parents, Statements, [], Ancestors).

% the predicate P/N, monomorphic, has a different number of positive literals in F0 and F
flipped_predicate(F0, F, P/N) :-
  setof(P/N, S^A^( signed_atom(F0, S, A), functor(A, P, N) ), Ps),
  member(P/N, Ps),
  \+ symbol(P, [_|_], _, _),
  positive_literals(F0, P/N, K0),
  positive_literals(F, P/N, K),
  K0 =\= K.

positive_literals(F, P/N, K) :- findall(A, ( signed_atom(F, +, A), functor(A, P, N) ), As), length(As, K).

% a predicate atom A of a formula, positive (+) or negative (-)
signed_atom(F, S, A) :- signed_atom(F, +, S, A).

signed_atom(~F, S0, S, A) :- !, opposite(S0, S1), signed_atom(F, S1, S, A).
signed_atom(F, S0, S, A) :- connective(F, Gs), !, member(G, Gs), signed_atom(G, S0, S, A).
signed_atom(A, S, S, A) :- A \= (_ = _).

opposite(+, -).
opposite(-, +).

% P_flipped(Xs) is defined as ~P(Xs), of the signature of P, or of individuals if P is untyped
record_flipped(P/N) :-
  flipped_name(P, P1),
  length(Xs, N),
  (   symbol(P, [], Ss, '$o')
  ->  record(symbol(P1, [], Ss, '$o'))
  ;   length(Ss, N), maplist(=('$i'), Ss)
  ),
  maplist(binder, Xs, Ss, Bs),
  A =.. [P|Xs],
  A1 =.. [P1|Xs],
  ( Bs == [] -> D = (A1 <=> ~A) ; D = '!'(Bs, (A1 <=> ~A)) ),
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

% a step after flipping is stated with the flipped predicates renamed; inputs and the ancestors of the
% flipping steps are not; a flipping step cites the definitions too
flipped_statement(flips([], _), _, Source, F, Source, F) :- !.
flipped_statement(_, _, file(N, I), F, file(N, I), F) :- !.
flipped_statement(flips(_, Ancestors), Name, Source, F, Source, F) :- memberchk(Name, Ancestors), !.
flipped_statement(flips(Ps, _), _, Source0, F0, Source, F) :-
  flipped_source(Ps, Source0, Source),
  flipped_formula(Ps, F0, F).

flipped_source(Ps, inference(consistent_polarity_flipping, Info, [Parent]), Source) :- !,
  findall(D, ( member(P/_, Ps), flipped_name(P, P1), definition_name(P1, D) ), Ds),
  Source = inference(consistent_polarity_flipping, Info, [Parent|Ds]).
flipped_source(_, Source, Source).

flipped_formula(Ps, F0, F) :-
  compound(F0),
  F0 =.. [Q, Bs, G0],
  ( Q == '!' ; Q == '?' ), !,
  flipped_formula(Ps, G0, G),
  F =.. [Q, Bs, G].
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
