% Vampire front end: interpret TSTP statements as step/3 facts
:- module(vampire, [load_vampire/1]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(signature).

% type declarations first, so that every equation can be given its sort
load_vampire(Statements) :-
  each(member(annotated(_, _, type, Type, _), Statements), declare(Type)),
  each(member(Statement, Statements), load_statement(Statement)).

load_statement(annotated(_, _, type, _, _)) :- !.
load_statement(annotated(Language, Name, Role, Formula0, Source)) :-
  typed([], Formula0, Formula),
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
conclusion(Language, How, F, C) :- clausal(Language, How), formula_clause(F, C0), !, C = C0.
conclusion(_, _, F, formula(F)).

clausal(cnf, _).
clausal(Language, How) :- ( Language == fof ; Language == tff ), clausal_step(How).

clausal_step(input(_, _)).
clausal_step(tactic(_, _)).
clausal_step(todo(cnf_transformation, _)) :- !.
% an unknown rule from clauses only
clausal_step(todo(Rule, Parents)) :-
  atom(Rule),
  Parents \== [],
  each(member(P, Parents), step(P, clause(_, _), _)).

% the conjecture is a goal, proved by refuting its negation, a hypothesis (see reconstruct.pl);
% steps that only preserve satisfiability (status esa) introduce symbols, and are not entailments
how(conjecture, file(_, Input), _, conjecture(Input)) :- !.
how(Role, file(_, Input), _, input(Role, Input)) :- !.
how(_, introduced(definition, _, [avatar_definition]), (Symbol <=> Component), split_def(Symbol, C)) :-
  formula_clause(Component, C), !.
how(_, introduced(definition, Info, _), _, todo(esa(definition, Symbols), [])) :- !,
  new_symbols(Info, Symbols).
how(_, inference(negated_conjecture, _, [Conjecture]), _, negated_conjecture(Conjecture)) :- !.
how(_, inference(Rule, Info, Parents), _, todo(esa(Rule, Symbols), Parents)) :-
  ( memberchk(status(esa), Info) ; esa(Rule) ), !,
  new_symbols(Info, Symbols).
how(_, inference(cnf_transformation, _, [Parent]), _, How) :-
  clausification(Parent, How), !.
how(_, inference(Rule, _, [Parent]), ~A, How) :-
  tactic(Rule, descent),
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
% and preprocessing are steps between formulas (descent.pl)
clausification(Parent, tactic(variant, [Parent])) :- step(Parent, clause(_, _), _), !.
clausification(Parent, tactic(deny, [Negated])) :- denied(Parent, Negated), !.
clausification(Parent, tactic(descent, [Parent])).

% Name is the negated conjecture Negated, of an atom, or denies it
denied(Name, Negated) :-
  denial(Name, Negated),
  step(Negated, formula(~G), _),
  \+ connective(G, _).

denial(Name, Name) :- step(Name, _, negated_conjecture(_)), !.
denial(Name, Negated) :- step(Name, _, tactic(deny, [Negated])), !.
denial(Name, Negated) :- step(Name, formula(_), todo(_, [Parent])), denial(Parent, Negated).

new_symbols(Info, Symbols) :- findall(S, (member(I, Info), introduced_symbol(I, _, S)), Symbols).

% rules that are not entailments, though Vampire does not say so: a predicate definition is
% printed in one direction only, and folding needs the other
esa(definition_folding).

% Vampire inference rules and the generic tactics that reconstruct them
tactic(resolution, resolve).
tactic(forward_subsumption_resolution, resolve).
tactic(backward_subsumption_resolution, resolve).
tactic(factoring, variant).
tactic(duplicate_literal_removal, variant).
tactic(sat_conversion, variant).
tactic(avatar_contradiction_clause, variant).
tactic(avatar_sat_refutation, variant).
tactic(avatar_split_clause, avatar_split).
tactic(avatar_component_clause, avatar_component).
tactic(rat, rup).
tactic(reorient_equations, variant).
tactic(trivial_inequality_removal, variant).
tactic(equality_resolution, variant).
tactic(superposition, paramodulate).
tactic(forward_demodulation, paramodulate).
tactic(backward_demodulation, paramodulate).
tactic(equality_factoring, equality_factor).
tactic(definition_unfolding, unfold).
tactic(rectify, descent).
tactic(flattening, descent).
tactic(ennf_transformation, descent).
tactic(nnf_transformation, descent).
tactic(true_and_false_elimination, descent).
tactic(pure_predicate_removal, descent).
tactic(unused_predicate_definition_removal, descent).

record_introduced(Source) :-
  each(introduced_symbol(Source, Kind, Symbol), record(introduced(Symbol, Kind))).

introduced_symbol(new_symbols(Kind, Symbols), Kind, Symbol) :- member(Symbol, Symbols).
introduced_symbol(inference(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
introduced_symbol(introduced(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
