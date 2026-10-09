% the shared database: written by the front end and reconstruction, read by back ends
:- module(db, [step/3, symbol/3, introduced/2, ir_step/3, split/2]).

% step(Name, Conclusion, How): a proof step, as understood by a front end
% Conclusion is clause(Binders, Literals) or formula(F), with Prolog variables:
% each retrieval is a fresh instance
% How is input(Role, Source), split_def(Symbol, Clause), tactic(Procedure, Parents) or todo(Record, Parents)
:- dynamic(step/3).

% symbol(Name, ArgumentSorts, Sort): signature, with sorts '$i' and '$o' by default
:- dynamic(symbol/3).

% introduced(Name, Kind): symbol introduced by the prover (e.g. naming, skolem)
:- dynamic(introduced/2).

% ir_step(Name, Conclusion, Justification): reconstructed steps, in dependency order
% ground: variables are numbered as '$VAR'(N), in binder order
% see ir.pl for the language of justifications and proof terms
:- dynamic(ir_step/3).

% split(Symbol, Clause): AVATAR split definitions, indexed by symbol, with Prolog variables
:- dynamic(split/2).
