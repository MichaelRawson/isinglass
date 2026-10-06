% the shared database: written by the front end and reconstruction, read by back ends
:- module(db, [step/3, symbol/3, introduced/2, ir_step/3, split/2]).

% step(Name, Conclusion, How): a proof step, as understood by a front end
% Conclusion is clause(Xs, Literals) or formula(F), with variables numbered as '$VAR'(N)
% How is input(Role, Source), split_def(Symbol, Clause), tactic(Tactic, Parents) or todo(Record, Parents)
:- dynamic(step/3).

% symbol(Name, ArgumentSorts, Sort): signature, with sorts '$i' and '$o' by default
:- dynamic(symbol/3).

% introduced(Name, Kind): symbol introduced by the prover (e.g. naming, skolem)
:- dynamic(introduced/2).

% ir_step(Name, Conclusion, Justification): reconstructed steps, in dependency order
% see ir.pl for the language of justifications
:- dynamic(ir_step/3).

% split(Symbol, Clause): AVATAR split definitions among ir_step/3, indexed by symbol
:- dynamic(split/2).
