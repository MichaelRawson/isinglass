/*
Translate a Vampire TSTP proof on standard input, e.g.

  swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p
  swipl -g 'run(smtlib)' -t halt src/main.pl < proof.p
  swipl -g 'run(check)' -t halt src/main.pl < proof.p
*/
:- use_module(load).
:- use_module(vampire).
:- use_module(reconstruct).
:- use_module(lambdapi, []).
:- use_module(smtlib, []).

run(Backend) :-
  read_tstp(Statements),
  load_vampire(Statements),
  reconstruct,
  emit(Backend).

% reconstruction alone elaborates (checks) every step
emit(check) :- !.
emit(Backend) :- Backend:emit.
