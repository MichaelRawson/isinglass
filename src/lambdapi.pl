/*
lambdapi back end, using the encoding of first-order logic in lambdapi's Stdlib.

A clause ∀xs. L_0 ∨ ... ∨ L_n-1 is stated as Π xs, π H_0 → ... → π H_n-1 → π ⊥,
where the hypothesis H for a positive literal A is ¬ A, and for a negative literal ~A is A.

The IR only provides ¬ ¬ A for some negative literals (see ir.pl): such values are "indirect",
and are used in continuation-passing style, n (λ a, ...), which is constructive as the goal is ⊥.
Every step takes the negated global conjecture ng and negated local conjecture nc.

Options:
  gdv: refer to the original problem's symbols and inputs as S.name and F.name
*/
:- module(lambdapi, [emit/1]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- use_module(ir).
:- set_prolog_flag(double_quotes, codes).
:- dynamic(gdv/0).
:- dynamic(lifted/4).
:- dynamic(indirect/1).

emit(Options) :-
  retractall(gdv),
  ( memberchk(gdv, Options) -> assertz(gdv) ; true ),
  findall(Name, ir_step(Name, _, _), Names),
  last(Names, Refutation),
  out(prelude),
  out(signature),
  out(conjectures),
  \+ ( member(Name, Names), \+ out(proof_step(Name)) ),
  out(qed(Refutation)).

out(G) :- phrase(G, Cs), atom_codes(A, Cs), write(A).

prelude -->
  "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Classic;\n\n",
  "opaque symbol neq_sym [a] [x y : τ a] : π (x ≠ y) → π (y ≠ x) ≔ λ neqxy eqyx, neqxy (eq_sym eqyx);\n",
  "opaque symbol nneq_sym [a] [x y : τ a] : π (¬ (¬ (x = y))) → π (¬ (¬ (y = x))) ≔ λ nn k, nn (λ e, k (eq_sym e));\n",
  "opaque symbol infer_el [a] : τ a ≔ el a;\n\n".

/********************************************************************************
 * signature and conjecture
 ********************************************************************************/

signature -->
  { findall(S-T, (symbol(S, Args, Sort), \+ introduced(S, _), \+ gdv, T = Args-Sort), Original),
    findall(S-T, (symbol(S, Args, Sort), introduced(S, _), T = Args-Sort), Introduced) },
  declarations("constant symbol ", Original),
  declarations("symbol ", Introduced),
  "\n".

declarations(_, []) --> [].
declarations(Keyword, [S-(Args-Sort)|Ss]) -->
  Keyword, sym(S), " : ", arrows(Args, Sort), ";\n",
  declarations(Keyword, Ss).

arrows([], Sort) --> sort(Sort).
arrows([A|As], Sort) --> sort(A), " → ", arrows(As, Sort).

sort('$i') --> "τ ι".
sort('$o') --> "Prop".

conjectures -->
  "symbol conj ≔ ⊥;\n",
  ( { gdv } -> "symbol gconj ≔ F.lambdapi__conjecture;\n" ; "symbol gconj ≔ ⊥;\n" ),
  "\n".

qed(Refutation) -->
  "\nopaque symbol qed (ng : π (¬ gconj)) : π conj ≔ ¬¬ₑ conj (", atom(Refutation), " ng);\n".

/********************************************************************************
 * steps
 ********************************************************************************/

proof_step(Name) -->
  { ir_step(Name, Conclusion, _), elaborate(Name, E), retractall(lifted(_, _, _, _)), retractall(indirect(_)) },
  proof_step(E, Name, Conclusion).

proof_step(input(_, Input), Name, clause(Xs, Ls)) -->
  { clause_formula(clause(Xs, Ls), F) },
  ( { gdv } -> [] ; "constant symbol ", input(Input), " (ng : π (¬ gconj)) : π ", formula(F), ";\n" ),
  header(Name), statement(clause(Xs, Ls), bottom), " ≔ ",
  { length(Ls, N), numlist_(0, N, Is) },
  lambdas(Xs, Is),
  cases(Is, Ls, input_instance(Input, Xs)), ";\n".
proof_step(split_def(Split, Clause), _, _) -->
  "rule ", sym(Split), " ↪ ", clause(Clause), ";\n".
proof_step(refute(Hs, E), Name, Clause) -->
  { Clause = clause(Xs, _), findall(I, member(h(I)-_, Hs), Is) },
  lemmas(E, Body, Name, Clause, Is),
  header(Name), statement(Clause, bottom), " ≔ ", lambdas(Xs, Is), refutation(Body), ";\n".

proof_step(todo(Record, _), Name, Conclusion) -->
  { functor(Record, Rule, _) },
  header(Name), conclusion(Conclusion), " ≔ begin admit end; // TODO ", atom(Rule), "\n".

/*
A chain of lemmas at the start of a refutation (e.g. from RUP) would be deeply nested,
which lambdapi checks slowly: lift each to a top-level symbol taking the step's variables and hypotheses.
*/
lemmas(let(H, L, arg(_, A), E), Body, Name, clause(Xs, Ls), Is) --> !,
  { value(L, A, Indirect, Cs), name_value(H, Indirect) },
  header(lemma(Name, H)), statement(clause(Xs, Ls), hypothesis_type(L, H)), " ≔ ",
  lambdas(Xs, Is), codes(Cs), ";\n",
  { assertz(lifted(H, Name, Xs, Is)) },
  lemmas(E, Body, Name, clause(Xs, Ls), Is).
lemmas(Body, Body, _, _, _) --> [].

header(lemma(Name, H)) --> !, "opaque symbol ", atom(Name), "_", local(H), " (ng : π (¬ gconj)) (nc : π (¬ conj)) : ".
header(Name) --> "opaque symbol ", atom(Name), " (ng : π (¬ gconj)) (nc : π (¬ conj)) : ".

conclusion(clause(Xs, Ls)) --> statement(clause(Xs, Ls), bottom).
conclusion(formula(F)) --> "π ", formula(F).

% step statements use framework-level Π and →, rather than `∀ and ⇒ which must be rewritten
statement(clause(Xs, Ls), Target) --> pis(Xs), arrows_to(Ls, Target).

pis([]) --> [].
pis([X|Xs]) --> "Π (", term(X), " : τ ι), ", pis(Xs).

arrows_to([], Target) --> "π ", call(Target).
arrows_to([L|Ls], Target) --> "π ", hypothesis_type(L), " → ", arrows_to(Ls, Target).

lambdas([], []) --> !.
lambdas(Xs, Is) --> "λ", variables(Xs), hypotheses(Is), ", ".

variables([]) --> [].
variables([X|Xs]) --> " ", term(X), variables(Xs).

hypotheses([]) --> [].
hypotheses([I|Is]) --> " ", local(h(I)), hypotheses(Is).

% from a proof of the input disjunction, refute each literal by case analysis
% binders are typed: inferring them is very expensive for wide clauses
cases([], [], D) --> call(D).
cases([I], [L], D) --> mate(L, h(I), D).
cases([I, J|Is], [L|Ls], D) -->
  { disjunction(Ls, F) },
  "(∨ₑ ", call(D), " (λ (l : π ", formula(L), "), ", mate(L, h(I), l), ") (λ (r", number(I), " : π ", formula(F), "), ",
  cases([J|Is], Ls, r(I)), "))".

% a proof D of literal L contradicts hypothesis H for L
mate(~_, H, D) --> !, "(", call(D), " ", hypothesis(H), ")".
mate(_, H, D) --> "(", hypothesis(H), " ", call(D), ")".

l --> "l".
r(I) --> "r", number(I).

input_instance(Input, Xs) --> "(", input(Input), ( { gdv } -> [] ; " ng" ), variables(Xs), ")".

input(Input) --> { gdv }, !, "F.", atom(Input).
input(Input) --> "{|", atom(Input), "²|}".

/********************************************************************************
 * proof terms
 ********************************************************************************/

% indirect arguments are bound by continuations around the use of the premise
refutation(use(P, Ts, Args)) -->
  { arguments(Args, 0, Direct, Continuations) },
  continuations(Continuations),
  "(", premise(P), variables(Ts), direct(Direct), ")",
  closing(Continuations).
% lemmas are β-redexes rather than let, which lambdapi may unfold during type checking
% (lemmas at the start of a step are lifted to top-level symbols instead, see lemmas//4)
refutation(let(H, L, arg(_, A), E)) -->
  { value(L, A, Indirect, Cs), name_value(H, Indirect) },
  "((λ (", hypothesis(H), " : π ", hypothesis_type(L, H), "), ", refutation(E), ") ", codes(Cs), ")".
% H refutes K, Pos proves K
refutation(contra(H, ~B, arg(_, A))) -->
  { value(B, A, _, Cs) },
  ( { indirect(H) } -> "(", hypothesis(H), " ", codes(Cs), ")" ; "(", codes(Cs), " ", hypothesis(H), ")" ).
refutation(contra(H, _, intro(Xs, HLs, E))) -->
  "(", hypothesis(H), " (λ", binders(Xs), typed_hypotheses(HLs), ", ", refutation(E), "))".

premise(h(I)) --> !, hypothesis(h(I)).
premise(Name) --> atom(Name), " ng nc".

% arguments(Args, N, Direct, Continuations): indirect arguments are replaced by variables cN
arguments([], _, [], []).
arguments([arg(L, A)|Args], N, [Cs|Direct], Continuations) :-
  value(L, A, Indirect, Value),
  M is N + 1,
  (   Indirect == true
  ->  L = ~B,
      phrase(("c", number(N)), Cs),
      Continuations = [c(N, B, Value)|Rest]
  ;   Cs = Value,
      Continuations = Rest
  ),
  arguments(Args, M, Direct, Rest).

direct([]) --> [].
direct([Cs|Css]) --> " ", codes(Cs), direct(Css).

continuations([]) --> [].
continuations([c(N, B, Value)|Cs]) --> "(", codes(Value), " (λ (c", number(N), " : π ", formula(B), "), ", continuations(Cs).

closing([]) --> [].
closing([_|Cs]) --> "))", closing(Cs).

% value(L, A, Indirect, Codes): the term refuting L by argument A, and whether it is indirect
value(L, A, Indirect, Cs) :- phrase(argument(L, A, Indirect), Cs).

% hypothesis H names a value
name_value(H, true) :- assertz(indirect(H)).
name_value(_, false).

argument(L, hyp(H), Indirect) --> { L = ~_, indirect(H) -> Indirect = true ; Indirect = false }, hypothesis(H).
argument(_, sym(L0, A), Indirect) -->
  { phrase(argument(L0, A, Indirect), Cs) },
  ( { L0 \= ~_ } -> "(neq_sym " ; { Indirect == true } -> "(nneq_sym " ; "(eq_sym " ),
  codes(Cs), ")".
argument(~A, assume(H, E), true) --> !,
  "(λ (", hypothesis(H), " : π (¬ ", formula(A), ")), ", refutation(E), ")".
argument(A, assume(H, E), false) -->
  "(λ (", hypothesis(H), " : π ", formula(A), "), ", refutation(E), ")".
argument(_, unfold(D, Clause, E), false) -->
  "(λ (", hypothesis(D), " : π ", clause(Clause), "), ", refutation(E), ")".

binders([]) --> [].
binders([X|Xs]) --> " (", term(X), " : τ ι)", binders(Xs).

typed_hypotheses([]) --> [].
typed_hypotheses([H-L|HLs]) --> " (", hypothesis(H), " : π ", hypothesis_type(L), ")", typed_hypotheses(HLs).

hypothesis(H) --> { lifted(H, Name, Xs, Is) }, !, "(", atom(Name), "_", local(H), " ng nc", variables(Xs), hypotheses(Is), ")".
hypothesis(H) --> local(H).

local(h(I)) --> "h", number(I).

/********************************************************************************
 * formulas and terms
 ********************************************************************************/

clause(clause(Xs, Ls)) --> foralls(Xs), implications(Ls, bottom).

foralls([]) --> [].
foralls([X|Xs]) --> "`∀ (", term(X), " : τ ι), ", foralls(Xs).

implications([], Target) --> call(Target).
implications([L|Ls], Target) --> "(", hypothesis_type(L), " ⇒ ", implications(Ls, Target), ")".

bottom --> "⊥".

% the type of hypothesis refuting literal L (and of an indirect value H)
hypothesis_type(~A) --> !, formula(A).
hypothesis_type(A) --> "(¬ ", formula(A), ")".

hypothesis_type(~A, H) --> { indirect(H) }, !, "(¬ (¬ ", formula(A), "))".
hypothesis_type(L, _) --> hypothesis_type(L).

formula('$false') --> !, "⊥".
formula('$true') --> !, "⊤".
formula(~F) --> !, "(¬ ", formula(F), ")".
formula((F | G)) --> !, "(", formula(F), " ∨ ", formula(G), ")".
formula((F & G)) --> !, "(", formula(F), " ∧ ", formula(G), ")".
formula((F => G)) --> !, "(", formula(F), " ⇒ ", formula(G), ")".
formula((F <=> G)) --> !, "(", formula(F), " ⇔ ", formula(G), ")".
formula((F <~> G)) --> !, "(¬ (", formula(F), " ⇔ ", formula(G), "))".
formula('!'(Xs, F)) --> !, "(", foralls(Xs), formula(F), ")".
formula('?'(Xs, F)) --> !, "(", exists(Xs), formula(F), ")".
formula(S = T) --> !, "(", term(S), " = ", term(T), ")".
formula(A) --> term(A).

exists([]) --> [].
exists([X|Xs]) --> "`∃ (", term(X), " : τ ι), ", exists(Xs).

term('$VAR'(N)) --> !, "x", number(N).
term('$any') --> !, "infer_el".
term(T) --> { T =.. [F|Ts] }, ( { Ts == [] } -> sym(F) ; "(", sym(F), variables(Ts), ")" ).

sym(S) --> { introduced(S, _) }, !, atom(S).
sym(S) --> { gdv }, !, "S.", atom(S).
sym(S) --> "{|", atom(S), "¹|}".

atom(A) --> { atom_codes(A, Cs) }, codes(Cs).
number(N) --> { number_codes(N, Cs) }, codes(Cs).

codes([]) --> [].
codes([C|Cs]) --> [C], codes(Cs).

numlist_(N, N, []) :- !.
numlist_(I, N, [I|Is]) :- J is I + 1, numlist_(J, N, Is).
