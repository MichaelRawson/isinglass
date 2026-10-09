% Vampire front end: interpret TSTP statements as step/3 facts
:- module(vampire, [load_vampire/1]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).

load_vampire(Statements) :-
  maplist(load_statement, Statements),
  default_signature.

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

record_introduced(Source) :-
  forall(introduced_symbol(Source, Kind, Symbol), assertz(introduced(Symbol, Kind))).

introduced_symbol(new_symbols(Kind, Symbols), Kind, Symbol) :- member(Symbol, Symbols).
introduced_symbol(inference(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
introduced_symbol(introduced(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).

% untyped symbols get the default sorts
default_signature :-
  findall(P-S, (step(_, C, _), conclusion_symbol(C, P, S)), Ss),
  sort(Ss, Symbols),
  maplist(default_symbol, Symbols).

conclusion_symbol(clause(_, Ls), P, S) :- member(L, Ls), formula_symbol(L, P, S).
conclusion_symbol(formula(F), P, S) :- formula_symbol(F, P, S).

default_sort(function, '$i').
default_sort(predicate, '$o').

% functions sort before predicates, so a name used as both is a function
default_symbol(_-(F/N)) :- length(As, N), symbol(F, As, _), !.
default_symbol(P-(F/N)) :-
  default_sort(P, Sort),
  length(Args, N),
  maplist(=('$i'), Args),
  assertz(symbol(F, Args, Sort)).
