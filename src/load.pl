/*
Read TPTP/TSTP from standard input with read/1, producing

  annotated(Language, Name, Role, Formula, Source)

with formulas normalised into the internal syntax (ops.pl):
  '$true', '$false', ~F, F | G, F & G, F => G, F <=> G, '!'(Bs, F), '?'(Bs, F), S = T
where the binders Bs of a quantifier are X : Sort, with sort '$i' if TPTP gives none, and
S != T becomes ~(S = T), F <= G becomes G => F, F <~> G becomes ~(F <=> G),
F ~| G becomes ~(F | G), F ~& G becomes ~(F & G). Equations are untyped here: the front end
gives them their sort, as '$='(Sort, S, T).

A type declaration (role type) Name : Type becomes type(Name, Params, Args, Sort), where Params are
the variables of TF1's !>[Params : $tType] (Prolog variables), Args the sorts of the arguments and
Sort that of the result: list : $tType > $tType is type(list, [], ['$tType'], '$tType').

Sorts are terms: '$i', '$o', '$tType', type variables, and declared types such as list('$i').
$-words are read as the prefix operator $ applied to a term, and become symbols named with a $.
*/
:- module(load, [read_tstp/1]).
:- use_module(library(lists)).
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

% Prolog's own prefix operators named by words (such as table and dynamic) are removed, as they may
% be TPTP symbols
read_tstp(Statements) :-
  findall(T-N, word_prefix_op(T, N), Words),
  forall(member(T-N, Words), op(0, T, N)),
  forall(tptp_op(P, T, N), op(P, T, N)),
  read_statements(Statements).

word_prefix_op(T, N) :-
  current_op(_, T, N),
  ( T == fx ; T == fy ),
  atom_codes(N, [C|_]),
  C >= 0'a,
  C =< 0'z.

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
  (   Role == type
  ->  declaration(Formula0, Formula)
  ;   normalise(Formula0, Formula)
  ).

% the source annotation is optional, and may be followed by useful info
source([], none).
source([Source|_], Source).

normalise(V, F) :- var(V), !, F = V.
% S != T is read as '!'(S) = T, but a variable S must not be unified with '!'(_)
normalise(S0 = T0, F) :- nonvar(S0), S0 = '!'(S1), !, F = ~(S = T), term(S1, S), term(T0, T).
normalise(S0 = T0, F) :- !, F = (S = T), term(S0, S), term(T0, T).
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
normalise(A0, A) :- term(A0, A).

% a quantified variable X or X : Sort, as X : Sort
binder(B, X:S) :- nonvar(B), B = (X : T), !, term(T, S).
binder(X, X:'$i').

% a term (or sort), with $-words as symbols: '$'(f(X)) is '$f'(X)
term(V, T) :- var(V), !, T = V.
term('$'(T0), T) :- !, T0 =.. [F0|As0], atom_concat('$', F0, F), terms(As0, As), T =.. [F|As].
term(T0, T) :- T0 =.. [F|As0], terms(As0, As), T =.. [F|As].

terms([], []).
terms([T0|Ts0], [T|Ts]) :- term(T0, T), terms(Ts0, Ts).

% Name : Type, with Type [!>[Params] :] [Args >] Sort, where Args are a product A * B * ...
declaration(Name0 : Type, type(Name, Params, Args, Sort)) :-
  term(Name0, Name),
  polymorphic(Type, Bs, Type1),
  maplist(binder, Bs, Params0),
  binder_variables(Params0, Params),
  arrow(Type1, Args0, Sort0),
  terms(Args0, Args),
  term(Sort0, Sort).

% !>[Bs] : Type, read as ((!) > Bs) : Type (canonical, as the operators of the code differ)
polymorphic(T, Bs, Type) :- nonvar(T), T = :(>('!', Bs), Type), !.
polymorphic(Type, [], Type).

% types may be type variables, which must not be unified with the patterns
arrow(T, As, Sort) :- nonvar(T), T = (Args > Sort), !, product(Args, As, []).
arrow(Sort, [], Sort).

product(T, As0, As) :- nonvar(T), T = A * B, !, product(A, As0, As1), product(B, As1, As).
product(A, [A|As], As).

binder_variables([], []).
binder_variables([X:_|Bs], [X|Xs]) :- binder_variables(Bs, Xs).
