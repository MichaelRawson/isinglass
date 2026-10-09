/*
Read TPTP/TSTP from standard input with read/1, producing

  annotated(Language, Name, Role, Formula, Source)

with formulas normalised into the internal syntax (ops.pl):
  '$true', '$false', ~F, F | G, F & G, F => G, F <=> G, '!'(Bs, F), '?'(Bs, F), S = T
where the binders Bs of a quantifier are X : Sort, with sort '$i' if TPTP gives none, and
S != T becomes ~(S = T), F <= G becomes G => F, F <~> G becomes ~(F <=> G),
F ~| G becomes ~(F | G), F ~& G becomes ~(F & G).
*/
:- module(load, [read_tstp/1]).
:- use_module(library(apply)).
:- use_module(ops).

% operators needed to read TPTP (as in tptp.pl)
% declared only when reading, so as not to affect the parsing of code
tptp_op(80, fx, '$').
tptp_op(100, xf, '!').
tptp_op(400, fy, '!').
tptp_op(400, fx, '?').
tptp_op(403, yfx, *).
tptp_op(405, xfx, '=').
tptp_op(440, xfy, >).
tptp_op(450, fy, ~).
tptp_op(450, xfy, :).
tptp_op(1102, xfy, '|').
tptp_op(1102, xfx, '~|').
tptp_op(1103, xfy, &).
tptp_op(1103, xfx, ~&).
tptp_op(1104, xfx, =>).
tptp_op(1104, xfx, <=).
tptp_op(1105, xfx, <=>).
tptp_op(1105, xfx, <~>).

read_tstp(Statements) :-
  forall(tptp_op(P, T, N), op(P, T, N)),
  read_statements(Statements).

read_statements(Statements) :-
  read(Term),
  read_statement(Term, Statements).

read_statement(end_of_file, []) :- !.
read_statement(Term, [Statement|Rest]) :-
  statement(Term, Statement),
  read_statements(Rest).

statement(Term, annotated(Language, Name, Role, Formula, Source)) :-
  Term =.. [Language, Name, Role, Formula0|Annotations],
  source(Annotations, Source),
  normalise(Formula0, Formula).

% the source annotation is optional, and may be followed by useful info
source([], none).
source([Source|_], Source).

normalise(V, F) :- var(V), !, F = V.
normalise('$'(false), F) :- !, F = '$false'.
normalise('$'(true), F) :- !, F = '$true'.
normalise('!'(S) = T, F) :- !, F = ~(S = T).
normalise(S = T, F) :- !, F = (S = T).
normalise(~G, F) :- !, F = ~H, normalise(G, H).
normalise('!'(Xs) : G, F) :- !, F = '!'(Bs, H), maplist(binder, Xs, Bs), normalise(G, H).
normalise('?'(Xs) : G, F) :- !, F = '?'(Bs, H), maplist(binder, Xs, Bs), normalise(G, H).
normalise((G | H), F) :- !, F = (G1 | H1), normalise(G, G1), normalise(H, H1).
normalise((G & H), F) :- !, F = (G1 & H1), normalise(G, G1), normalise(H, H1).
normalise((G => H), F) :- !, F = (G1 => H1), normalise(G, G1), normalise(H, H1).
normalise('<='(G, H), F) :- !, F = (H1 => G1), normalise(G, G1), normalise(H, H1).
normalise((G <=> H), F) :- !, F = (G1 <=> H1), normalise(G, G1), normalise(H, H1).
normalise('<~>'(G, H), F) :- !, F = ~(G1 <=> H1), normalise(G, G1), normalise(H, H1).
normalise('~|'(G, H), F) :- !, F = ~(G1 | H1), normalise(G, G1), normalise(H, H1).
normalise('~&'(G, H), F) :- !, F = ~(G1 & H1), normalise(G, G1), normalise(H, H1).
normalise(A, A).

% a quantified variable X or X : Sort, as X : Sort
binder(B, X:S) :- nonvar(B), B = (X : T), !, sort_name(T, S).
binder(X, X:'$i').

sort_name('$'(A), S) :- !, atom_concat('$', A, S).
sort_name(S, S).
