% the shared database: written by the front end and reconstruction, read by back ends
% The facts are private to this module: other modules read them through the exported predicates, and
% add them with record/1. Updating or calling a dynamic predicate imported from another module is
% not portable: Trealla refuses to update it, and Scryer gives each module its own copy.
:- module(db, [step/3, symbol/4, introduced/2, ir_step/3, split/2, skolem_hint/2, option/1, record/1]).

:- dynamic(step_/3).
:- dynamic(symbol_/4).
:- dynamic(introduced_/2).
:- dynamic(ir_step_/3).
:- dynamic(split_/2).
:- dynamic(skolem_hint_/2).
:- dynamic(option_/1).

% step(Name, Conclusion, How): a proof step, as understood by a front end
% Conclusion is clause(Binders, Literals) or formula(F), with Prolog variables:
% each retrieval is a fresh instance
% How is input(Role, Source), conjecture(Source), negated_conjecture(Conjecture),
% split_def(Symbol, Clause), define(Symbol), tactic(Procedure, Parents) or todo(Record, Parents); reconstruction adds
% the choice axioms of Skolem symbols, skolem_def(Symbol, Binders, F) (see ir.pl), so that proofs cite them
step(Name, Conclusion, How) :- step_(Name, Conclusion, How).

% symbol(Name, Params, ArgumentSorts, Sort): signature (see signature.pl), with Params the type
% variables of a polymorphic symbol; untyped symbols get sorts '$i' and '$o'
symbol(Name, Params, Args, Sort) :- symbol_(Name, Params, Args, Sort).

% introduced(Name, Kind): symbol introduced by the prover (e.g. naming, skolem)
introduced(Name, Kind) :- introduced_(Name, Kind).

% ir_step(Name, Conclusion, Justification): reconstructed steps, in dependency order
% ground: variables are numbered as '$VAR'(N), in binder order
% see ir.pl for the language of justifications and proof terms
ir_step(Name, Conclusion, Justification) :- ir_step_(Name, Conclusion, Justification).

% split(Symbol, Clause): AVATAR split definitions, indexed by symbol, with Prolog variables
split(Symbol, Clause) :- split_(Symbol, Clause).

% skolem_hint(Symbol, F): the prover says that a term of the Skolem symbol Symbol is the choice of
% the δ formula F, with Prolog variables; only a hint (see transform.pl)
skolem_hint(Symbol, F) :- skolem_hint_(Symbol, F).

% option(O): a run-time option given to main/3, e.g. trace
option(O) :- option_(O).

% add a fact, after those already there
record(step(Name, Conclusion, How)) :- assertz(step_(Name, Conclusion, How)).
record(symbol(Name, Params, Args, Sort)) :- assertz(symbol_(Name, Params, Args, Sort)).
record(introduced(Name, Kind)) :- assertz(introduced_(Name, Kind)).
record(ir_step(Name, Conclusion, Justification)) :- assertz(ir_step_(Name, Conclusion, Justification)).
record(split(Symbol, Clause)) :- assertz(split_(Symbol, Clause)).
record(skolem_hint(Symbol, F)) :- assertz(skolem_hint_(Symbol, F)).
record(option(O)) :- assertz(option_(O)).
