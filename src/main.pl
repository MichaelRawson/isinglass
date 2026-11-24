/*
Translate a TSTP proof on standard input, given the front end for its prover and a back end, e.g.

  swipl -g 'main(vampire, lambdapi)' src/main.pl < proof.p
  scryer-prolog -f -g 'main(vampire, smtlib)' src/main.pl < proof.p
  tpl -f -g 'main(vampire, checker)' src/main.pl < proof.p

The script `ising` does this with SWI, and traces the steps given --trace, or optimises the IR given
--optimise, by

  swipl -g 'main(vampire, checker, [trace, optimise])' src/main.pl < proof.p

Every module is loaded here, in dependency order: Trealla resolves the file of a nested use_module
against the working directory, but finds a module that is already loaded.
*/
:- use_module(ops).
:- use_module(utils).
:- use_module(db).
:- use_module(logic).
:- use_module(printing).
:- use_module(signature).
:- use_module(ir).
:- use_module(load).
:- use_module(vampire).
:- use_module(rup).
:- use_module(close).
:- use_module(optimise).
:- use_module(matching).
:- use_module(normal).
:- use_module(transform).
:- use_module(reconstruct).
:- use_module(lambdapi).
:- use_module(smtlib).
:- use_module(checker).
:- use_module(agda).

% exit with status 1 on failure or error: the top levels of the systems differ
main(Frontend, Backend) :- main(Frontend, Backend, []).

% Options: trace prints the name and tactic of each step to stderr as its search starts,
% optimise inlines and simplifies the IR before it is emitted (optimise.pl), implicits(Kinds)
% gives Agda type arguments of these kinds, and complete fails rather than print an Agda proof
% with holes (agda.pl)
main(Frontend, Backend, Options) :-
  recorded_options(Options),
  (   catch(run(Frontend, Backend), Error, ( error_message(Error, Message), warn(['error: '|Message]), fail ))
  ->  halt(0)
  ;   halt(1)
  ).

% errors that malformed input may raise, explained: Vampire, for one, prints TSTP only given -p tptp
error_message(not_tstp(Term), Message) :- !,
  Message = ['input is not TSTP: read ', Term, ' for an annotated formula such as fof(Name, Role, Formula, Source)', Hint],
  tstp_hint(Hint).
error_message(error(syntax_error(Error), _), ['syntax error in input (', Error, '): is it TSTP?', Hint]) :- !,
  tstp_hint(Hint).
error_message(no_refutation, ['the input has no refutation ($false): is it a proof?', Hint]) :- !,
  tstp_hint(Hint).
error_message(Error, [Error]).

tstp_hint(' (Vampire prints its proofs in TSTP given -p tptp)').

% both names are looked up before anything is read, so a typo is reported at once
run(Frontend, Backend) :-
  frontend(Frontend, Load),
  backend(Backend, Emit),
  read_tstp(Statements),
  call(Load, Statements),
  default_signature,
  reconstruct,
  ( option(optimise) -> optimise ; true ),
  call(Emit).

recorded_options([]).
recorded_options([Option|Options]) :- record(option(Option)), recorded_options(Options).

frontend(vampire, load_vampire) :- !.
frontend(Frontend, _) :- warn(['error: unknown frontend ', Frontend]), halt(1).

backend(lambdapi, emit_lambdapi) :- !.
backend(smtlib, emit_smtlib) :- !.
backend(checker, emit_checker) :- !.
backend(agda, emit_agda) :- !.
backend(agda_file, emit_agda_file) :- !.
backend(Backend, _) :- warn(['error: unknown backend ', Backend]), halt(1).
