/*
Translate a Vampire TSTP proof on standard input, e.g.

  swipl -g 'main(lambdapi)' src/main.pl < proof.p
  scryer-prolog -f -g 'main(smtlib)' src/main.pl < proof.p
  tpl -f -g 'main(checker)' src/main.pl < proof.p

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
:- use_module(matching).
:- use_module(descent).
:- use_module(reconstruct).
:- use_module(lambdapi).
:- use_module(smtlib).
:- use_module(checker).
:- use_module(agda).

% exit with status 1 on failure or error: the top levels of the systems differ
main(Backend) :-
  (   catch(run(Backend), Error, ( warn(['error: ', Error]), fail ))
  ->  halt(0)
  ;   halt(1)
  ).

run(Backend) :-
  read_tstp(Statements),
  load_vampire(Statements),
  default_signature,
  reconstruct,
  emit(Backend).

emit(lambdapi) :- emit_lambdapi.
emit(smtlib) :- emit_smtlib.
emit(checker) :- emit_checker.
emit(agda) :- emit_agda.
emit(agda_file) :- emit_agda_file.
