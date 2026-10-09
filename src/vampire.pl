% Vampire front end: interpret TSTP statements as step/3 facts
:- module(vampire, [load_vampire/1]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

load_vampire(Statements) :- maplist(load_statement, Statements).

load_statement(annotated(_, Name, type, _, _)) :- !,
  format(user_error, "error: type declaration ~w is not supported~n", [Name]),
  fail.
load_statement(annotated(_, Name, Role, Formula, Source)) :-
  conclusion(Formula, Conclusion),
  how(Role, Source, Conclusion, How),
  record_introduced(Source),
  assertz(step(Name, Conclusion, How)).

% clause-shaped formulas become clauses; variables are kept as Prolog variables
conclusion(F, C) :- formula_clause(F, C), !.
conclusion(F, formula(F)).

how(Role, file(_, Input), _, input(Role, Input)) :- !.
how(_, introduced(definition, _, [avatar_definition]), formula(Symbol <=> Component), split_def(Symbol, C)) :-
  formula_clause(Component, C), !.
how(_, inference(Rule, _, Parents), _, How) :-
  tactic(Rule, Tactic), !,
  How = tactic(Tactic, Parents).
how(_, inference(Rule, _, Parents), _, todo(Rule, Parents)) :- !.
how(_, Source, _, todo(Source, [])).

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

record_introduced(Source) :-
  forall(introduced_symbol(Source, Kind, Symbol), assertz(introduced(Symbol, Kind))).

introduced_symbol(new_symbols(Kind, Symbols), Kind, Symbol) :- member(Symbol, Symbols).
introduced_symbol(inference(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
introduced_symbol(introduced(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
