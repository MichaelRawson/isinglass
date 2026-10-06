/*
Translate a Vampire TSTP proof on standard input, e.g.

  swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p
  swipl -g 'run(smtlib)' -t halt src/main.pl < proof.p
  swipl -g 'run(check)' -t halt src/main.pl < proof.p

run(Backend, Options) passes options to the back end, e.g. run(lambdapi, [gdv]).
*/
:- use_module(load).
:- use_module(vampire).
:- use_module(reconstruct).
:- use_module(ir).
:- use_module(db).
:- use_module(lambdapi, []).
:- use_module(smtlib, []).

run(Backend) :- run(Backend, []).

run(Backend, Options) :-
  read_tstp(Statements),
  load_vampire(Statements),
  reconstruct,
  check_all,
  emit(Backend, Options).

emit(check, _) :- !,
  findall(Kind, (ir_step(_, _, J), functor(J, Kind, _)), Kinds),
  msort(Kinds, Sorted),
  clumped_pairs(Sorted, Counts),
  format("~w~n", [Counts]).
emit(Backend, Options) :- Backend:emit(Options).

clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Counts]) :- clump(X, Xs, 1, N, Rest), clumped_pairs(Rest, Counts).

clump(X, [Y|Ys], N0, N, Rest) :- X == Y, !, N1 is N0 + 1, clump(X, Ys, N1, N, Rest).
clump(_, Rest, N, N, Rest).
