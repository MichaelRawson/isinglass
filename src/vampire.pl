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

% clause-shaped formulas become clauses, variables numbered in binder order
conclusion(F, C) :-
  clause_form(F, clause(Xs, Ls)), !,
  number_vars(Xs, 0, _),
  C = clause(Xs, Ls).
conclusion(F, formula(F)) :-
  term_variables(F, Vs),
  number_vars(Vs, 0, _).

how(Role, file(_, Input), _, input(Role, Input)) :- !.
how(_, introduced(definition, _, [avatar_definition]), formula(Symbol <=> Component), split_def(Symbol, C)) :-
  clause_form(Component, C), !.
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
  \+ ( introduced_symbol(Source, Kind, Symbol),
       \+ assertz(introduced(Symbol, Kind)) ).

introduced_symbol(new_symbols(Kind, Symbols), Kind, Symbol) :- member(Symbol, Symbols).
introduced_symbol(inference(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).
introduced_symbol(introduced(_, Info, _), Kind, Symbol) :- member(I, Info), introduced_symbol(I, Kind, Symbol).

% untyped symbols get the default sorts
default_signature :-
  findall(F-N, (step(_, C, _), conclusion_symbols(C, Fs, _), member(F/N, Fs)), Functions),
  findall(P-N, (step(_, C, _), conclusion_symbols(C, _, Ps), member(P/N, Ps)), Predicates),
  sort(Functions, Fs),
  sort(Predicates, Ps),
  maplist(default_symbol('$i'), Fs),
  maplist(default_symbol('$o'), Ps).

conclusion_symbols(clause(Xs, Ls), Fs, Ps) :- clause_formula(clause(Xs, Ls), F), symbols(F, Fs, Ps).
conclusion_symbols(formula(F), Fs, Ps) :- symbols(F, Fs, Ps).

default_symbol(_, F-_) :- symbol(F, _, _), !.
default_symbol(Sort, F-N) :-
  length(Args, N),
  maplist(=('$i'), Args),
  assertz(symbol(F, Args, Sort)).
