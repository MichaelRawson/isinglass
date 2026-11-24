/*
Read TPTP/TSTP from standard input with read/1, producing

  annotated(Language, Name, Role, Formula, Source)

with formulas normalised into the internal syntax (ops.pl):
  '$true', '$false', ~F, F | G, F & G, F => G, F <=> G, '!'(B, F), '?'(B, F), S = T
where each quantifier has one binder B, X : Sort, with sort '$i' if TPTP gives none (a group of
binders is a quantifier for each, as ! [X] : ! [Y] : F), and
S != T becomes ~(S = T), F <= G becomes G => F, F <~> G becomes ~(F <=> G),
F ~| G becomes ~(F | G), F ~& G becomes ~(F & G). Equations are untyped here: the front end
gives them their sort, as '$='(Sort, S, T).

A type declaration (role type) Name : Type becomes type(Name, Params, Args, Sort), where Params are
the variables of TF1's !>[Params : $tType] (Prolog variables), Args the sorts of the arguments and
Sort that of the result: list : $tType > $tType is type(list, [], ['$tType'], '$tType').

Sorts are terms: '$i', '$o', '$tType', type variables, and declared types such as list('$i').
$-words are read as the prefix operator $ applied to a term, and become symbols named with a $.

TPTP names statements apart from symbols, so the name of each statement, of each parent of an
inference, and of the input of a file are renamed with reserved prefixes, '$step:f12' and
'$input:ax1' (utils:named/3), so that they cannot clash with symbols or built-ins.
*/
:- module(load, [read_tstp/1]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(utils).

% operators needed to read TPTP (as in tptp.pl), declared only when reading, so as not to affect the
% parsing of code. ! is a solo character, so != and !> are two tokens each, and are read with the
% help of prefix operators = and >: S != T as '!'(S, =(T)), with ! infix, and !>[Bs] as '!'(>(Bs)).
% (tptp.pl has a postfix ! instead, for (S!) = T, but Trealla does not read an atom that is both a
% prefix and a postfix operator; and ISO does not allow the operator ! as an operand of an infix >.)
% One fact to a line: checkread takes the table from here.
tptp_op(80, fx, '$').
tptp_op(400, fy, '!').
tptp_op(400, fx, '?').
tptp_op(400, fx, >).
tptp_op(400, fx, '=').
tptp_op(403, yfx, *).
tptp_op(405, xfx, '=').
tptp_op(405, xfx, '!').
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
% A distinct object "Apple" is read as the atom 'Apple': the default reading of double quotes differs
% between systems (a string, characters or codes)
read_tstp(Statements) :-
  findall(op(0, T, N), word_prefix_op(T, N), Words),
  findall(op(P, T, N), tptp_op(P, T, N), Ops),
  declare_ops(Words),
  declare_ops(Ops),
  set_prolog_flag(double_quotes, atom),
  read_statements(Statements).

% op/3 is called here, in the module that reads: Trealla's operators are local to a module, and
% those declared through a meta-predicate of another module would be local to that one
declare_ops([]).
declare_ops([op(P, T, N)|Ops]) :- op(P, T, N), declare_ops(Ops).

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
  Term =.. [Language, Name0, Role, Formula0|Annotations],
  step_name(Name0, Name),
  source(Annotations, Source0),
  renamed_source(Source0, Source),
  (   Role == type
  ->  declaration(Formula0, Formula)
  ;   normalise(Formula0, Formula)
  ).

% the source annotation is optional, and may be followed by useful info
source([], none).
source([Source|_], Source).

% the names of statements and inputs are renamed apart from symbols (utils:named/3): the parents of an
% inference, a name, Name:Info, or an inference itself, and the input name of a file
renamed_source(inference(Rule, Info, Parents0), inference(Rule, Info, Parents)) :- !,
  maplist(renamed_parent, Parents0, Parents).
renamed_source(file(File, Input0), file(File, Input)) :- !, named(input, Input0, Input).
renamed_source(Source, Source).

renamed_parent(P0, P) :- ( atom(P0) ; integer(P0) ), !, step_name(P0, P).
renamed_parent(P0:Info, P:Info) :- !, renamed_parent(P0, P).
renamed_parent(P0, P) :- renamed_source(P0, P).

normalise(V, F) :- var(V), !, F = V.
normalise('!'(S0, '='(T0)), F) :- !, F = ~(S = T), term(S0, S), term(T0, T).
normalise(S0 = T0, F) :- !, F = (S = T), term(S0, S), term(T0, T).
normalise(~G, F) :- !, F = ~H, normalise(G, H).
normalise('!'(Xs) : G, F) :- !, quantified(Xs, G, Bs, H), quantify('!', Bs, H, F).
normalise('?'(Xs) : G, F) :- !, quantified(Xs, G, Bs, H), quantify('?', Bs, H, F).
normalise((G | H), F) :- !, F = (G1 | H1), normalise(G, G1), normalise(H, H1).
normalise((G & H), F) :- !, F = (G1 & H1), normalise(G, G1), normalise(H, H1).
normalise((G => H), F) :- !, F = (G1 => H1), normalise(G, G1), normalise(H, H1).
normalise('<='(G, H), F) :- !, F = (H1 => G1), normalise(G, G1), normalise(H, H1).
normalise((G <=> H), F) :- !, F = (G1 <=> H1), normalise(G, G1), normalise(H, H1).
normalise('<~>'(G, H), F) :- !, F = ~((G1 <=> H1)), normalise(G, G1), normalise(H, H1).
normalise('~|'(G, H), F) :- !, F = ~((G1 | H1)), normalise(G, G1), normalise(H, H1).
normalise('~&'(G, H), F) :- !, F = ~((G1 & H1)), normalise(G, G1), normalise(H, H1).
normalise(A0, A) :- term(A0, A).

% a quantifier's binders Xs and body G, renamed apart: read/1 gives binders of the same name in one
% statement the same variable, but instantiation is unification
quantified(Xs, G, Bs, H) :-
  term_variables(Xs-G, Vs),
  copy_term(Vs-Xs-G, Ws-Ys-G1),
  maplist(binder, Xs, Bound),
  maplist(kept(Bound), Vs, Ws),
  maplist(binder, Ys, Bs),
  normalise(G1, H).

% a variable that the binders Bound do not bind is not renamed
kept(Bound, V, _) :- member(X:_, Bound), X == V, !.
kept(_, V, V).

% a quantified variable X or X : Sort, as X : Sort
binder(B, X:S) :- nonvar(B), B = (X : T), !, term(T, S).
binder(X, X:'$i').

% a term (or sort), with $-words as symbols: '$'(f(X)) is '$f'(X); a symbol '@'/2 would be read as
% the application of a proof (ops.pl), so it is refused
term(V, T) :- var(V), !, T = V.
term(_ @ _, _) :- !, throw(reserved_symbol('@'/2)).
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

% !>[Bs] : Type, read as '!'(>(Bs)) : Type
polymorphic(T, Bs, Type) :- nonvar(T), T = :('!'(>(Bs)), Type), !.
polymorphic(Type, [], Type).

% types may be type variables, which must not be unified with the patterns
arrow(T, As, Sort) :- nonvar(T), T = (Args > Sort), !, product(Args, As, []).
arrow(Sort, [], Sort).

product(T, As0, As) :- nonvar(T), T = A * B, !, product(A, As0, As1), product(B, As1, As).
product(A, [A|As], As).

