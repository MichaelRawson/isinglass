/*
Translate a Vampire TSTP proof on standard input, e.g.

  swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p
  swipl -g 'run(smtlib)' -t halt src/main.pl < proof.p
  swipl -g 'run(check)' -t halt src/main.pl < proof.p
*/
:- use_module(load).
:- use_module(vampire).
:- use_module(reconstruct).
:- use_module(ir).
:- use_module(db).
:- use_module(lambdapi, []).
:- use_module(smtlib, []).

run(Backend) :-
  read_tstp(Statements),
  load_vampire(Statements),
  reconstruct,
  emit(Backend).

% re-check the stored IR, and summarise the kinds of justification
emit(check) :- !,
  check_all,
  findall(Kind, (ir_step(_, _, J), functor(J, Kind, _)), Kinds),
  msort(Kinds, Sorted),
  clumped_pairs(Sorted, Counts),
  format("~w~n", [Counts]).
emit(Backend) :- Backend:emit.

clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Counts]) :- clump(X, Xs, 1, N, Rest), clumped_pairs(Rest, Counts).

clump(X, [Y|Ys], N0, N, Rest) :- X == Y, !, N1 is N0 + 1, clump(X, Ys, N1, N, Rest).
clump(_, Rest, N, N, Rest).
