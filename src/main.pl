/*
Translate a Vampire TSTP proof on standard input, e.g.

  swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p
  swipl -g 'run(smtlib)' -t halt src/main.pl < proof.p
  swipl -g 'run(checker)' -t halt src/main.pl < proof.p
*/
:- use_module(load).
:- use_module(vampire).
:- use_module(signature).
:- use_module(reconstruct).
:- use_module(lambdapi, []).
:- use_module(smtlib, []).
:- use_module(checker, []).

run(Backend) :-
  read_tstp(Statements),
  load_vampire(Statements),
  default_signature,
  reconstruct,
  Backend:emit.
