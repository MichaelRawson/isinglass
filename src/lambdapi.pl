/*
lambdapi back end, using the encoding of first-order logic in lambdapi's Stdlib.

A clause ∀xs. L_0 ∨ ... ∨ L_n-1 is stated as Π xs, π H_0 → ... → π H_n-1 → π ⊥,
where the hypothesis H for a positive literal A is ¬ A, and for a negative literal ~A is A.

The IR only provides ¬ ¬ A for some negative literals (see ir.pl): such values are "indirect",
and are used in continuation-passing style, n (λ a, ...), which is constructive as the goal is ⊥.

*/
:- module(lambdapi, [emit/0]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- set_prolog_flag(double_quotes, codes).
:- dynamic(indirect/1).

emit :-
  findall(Name, ir_step(Name, _, _), Names),
  out(prelude),
  out(signature),
  \+ ( member(Name, Names), \+ out(proof_step(Name)) ).

out(G) :- phrase(G, Cs), atom_codes(A, Cs), write(A).

prelude -->
  "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq;\n\n",
  "opaque symbol neq_sym [a] [x y : τ a] : π (x ≠ y) → π (y ≠ x) ≔ λ neqxy eqyx, neqxy (eq_sym eqyx);\n",
  "opaque symbol nneq_sym [a] [x y : τ a] : π (¬ (¬ (x = y))) → π (¬ (¬ (y = x))) ≔ λ nn k, nn (λ e, k (eq_sym e));\n",
  "opaque symbol infer_el [a] : τ a ≔ el a;\n\n".

/********************************************************************************
 * signature
 ********************************************************************************/

signature -->
  { findall(S-T, (symbol(S, Args, Sort), \+ introduced(S, _), T = Args-Sort), Original),
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

/********************************************************************************
 * steps
 ********************************************************************************/

proof_step(Name) -->
  { ir_step(Name, Conclusion, Justification), retractall(indirect(_)) },
  proof_step(Justification, Name, Conclusion).

proof_step(input(_, Input), Name, clause(Xs, Ls)) -->
  { clause_formula(clause(Xs, Ls), F) },
  "constant symbol ", input(Input), " : π ", formula(F), ";\n",
  header(Name), statement(clause(Xs, Ls)), " ≔ ",
  { length(Ls, N), numlist_(0, N, Is) },
  lambdas(Xs, Is),
  cases(Is, Ls, input_instance(Input, Xs)), ";\n".
proof_step(split_def(Split, Clause), _, _) -->
  "rule ", sym(Split), " ↪ ", clause(Clause), ";\n".
proof_step(refute(R), Name, clause(Xs, Ls)) -->
  { length(Ls, N), numlist_(0, N, Is) },
  header(Name), statement(clause(Xs, Ls)), " ≔ ", lambdas(Xs, Is), refutation(R), ";\n".

proof_step(todo(Record, _), Name, Conclusion) -->
  { functor(Record, Rule, _) },
  header(Name), conclusion(Conclusion), " ≔ begin admit end; // TODO ", atom(Rule), "\n".

header(Name) --> "opaque symbol ", atom(Name), " : ".

conclusion(clause(Xs, Ls)) --> statement(clause(Xs, Ls)).
conclusion(formula(F)) --> "π ", formula(F).

% step statements use framework-level Π and →, rather than `∀ and ⇒ which must be rewritten
statement(clause(Xs, Ls)) --> pis(Xs), arrows_to(Ls).

pis([]) --> [].
pis([X|Xs]) --> "Π (", term(X), " : τ ι), ", pis(Xs).

arrows_to([]) --> "π ⊥".
arrows_to([L|Ls]) --> "π ", hypothesis_type(L), " → ", arrows_to(Ls).

lambdas([], []) --> !.
lambdas(Xs, Is) --> "λ", variables(Xs), hypotheses(Is), ", ".

variables([]) --> [].
variables([X|Xs]) --> " ", term(X), variables(Xs).

hypotheses([]) --> [].
hypotheses([I|Is]) --> " ", hypothesis(h(I)), hypotheses(Is).

% from a proof of the input disjunction, refute each literal by case analysis
cases([], [], D) --> call(D).
cases([I], [L], D) --> mate(L, h(I), D).
cases([I, J|Is], [L|Ls], D) -->
  "(∨ₑ ", call(D), " (λ l, ", mate(L, h(I), l), ") (λ r", number(I), ", ", cases([J|Is], Ls, r(I)), "))".

% a proof D of literal L contradicts hypothesis H for L
mate(~_, H, D) --> !, "(", call(D), " ", hypothesis(H), ")".
mate(_, H, D) --> "(", hypothesis(H), " ", call(D), ")".

l --> "l".
r(I) --> "r", number(I).

input_instance(Input, Xs) --> { phrase(variables(Xs), As) }, application(input(Input), As).

input(Input) --> "{|", atom(Input), "²|}".

/********************************************************************************
 * proof terms
 ********************************************************************************/

% indirect arguments are bound by continuations around the use of the premise
refutation(use(P, Ts, Args)) -->
  { arguments(Args, 0, Direct, Continuations) },
  { phrase((variables(Ts), direct(Direct)), As) },
  continuations(Continuations),
  application(premise(P), As),
  closing(Continuations).
% lemmas are β-redexes rather than let, which lambdapi may unfold during type checking
refutation(let(H, L, arg(_, A), E)) -->
  { value(L, A, Indirect, Cs), name_value(H, Indirect) },
  "((λ ", hypothesis(H), ", ", refutation(E), ") ", codes(Cs), ")".
% H refutes K, Pos proves K
refutation(contra(H, ~B, arg(_, A))) -->
  { value(B, A, _, Cs) },
  ( { indirect(H) } -> "(", hypothesis(H), " ", codes(Cs), ")" ; "(", codes(Cs), " ", hypothesis(H), ")" ).
refutation(contra(H, _, intro(Xs, Gs, E))) -->
  "(", hypothesis(H), " (λ", variables(Xs), binders(Gs), ", ", refutation(E), "))".

premise(h(I)) --> !, hypothesis(h(I)).
premise(Name) --> atom(Name).

% arguments(Args, N, Direct, Continuations): indirect arguments are replaced by variables cN
arguments([], _, [], []).
arguments([arg(L, A)|Args], N, [Cs|Direct], Continuations) :-
  value(L, A, Indirect, Value),
  M is N + 1,
  (   Indirect == true
  ->  phrase(("c", number(N)), Cs),
      Continuations = [c(N, Value)|Rest]
  ;   Cs = Value,
      Continuations = Rest
  ),
  arguments(Args, M, Direct, Rest).

direct([]) --> [].
direct([Cs|Css]) --> " ", codes(Cs), direct(Css).

continuations([]) --> [].
continuations([c(N, Value)|Cs]) --> "(", codes(Value), " (λ c", number(N), ", ", continuations(Cs).

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
argument(L, assume(H, E), Indirect) -->
  { L = ~_ -> Indirect = true ; Indirect = false },
  "(λ ", hypothesis(H), ", ", refutation(E), ")".
argument(_, unfold(D, _, E), false) -->
  "(λ ", hypothesis(D), ", ", refutation(E), ")".

binders([]) --> [].
binders([H|Hs]) --> " ", hypothesis(H), binders(Hs).

hypothesis(h(I)) --> "h", number(I).

% Head applied to the (space-separated) arguments As, parenthesised only if there are any
application(Head, []) --> !, call(Head).
application(Head, As) --> "(", call(Head), codes(As), ")".

/********************************************************************************
 * formulas and terms
 ********************************************************************************/

/*
Formulas are parenthesised only where needed, by the priorities of the Stdlib notations
(= 10, ∧ 7, ∨ 6, ⇒ and ⇔ 5, all infix right; ¬ prefix 35; quantifiers lowest),
with 100 for application and 101 for atomic terms. formula(P, F) prints F where priority P is
required; formula//1 and term//1 print an argument, e.g. of π.
*/
formula(F) --> formula(101, F).

formula(P, F) --> { priority(F, Q) }, lparen(P, Q), formula_(F), rparen(P, Q).

lparen(P, Q) --> { Q < P }, !, "(".
lparen(_, _) --> [].

rparen(P, Q) --> { Q < P }, !, ")".
rparen(_, _) --> [].

priority('$false', 101) :- !.
priority('$true', 101) :- !.
priority(~_, 35) :- !.
priority(_ | _, 6) :- !.
priority(_ & _, 7) :- !.
priority(_ => _, 5) :- !.
priority(_ <=> _, 5) :- !.
priority('!'(_, _), 0) :- !.
priority('?'(_, _), 0) :- !.
priority(_ = _, 10) :- !.
priority(T, Q) :- term_priority(T, Q).

formula_('$false') --> !, "⊥".
formula_('$true') --> !, "⊤".
formula_(~F) --> !, "¬ ", formula(35, F).
formula_((F | G)) --> !, formula(7, F), " ∨ ", formula(6, G).
formula_((F & G)) --> !, formula(8, F), " ∧ ", formula(7, G).
formula_((F => G)) --> !, formula(6, F), " ⇒ ", formula(5, G).
formula_((F <=> G)) --> !, formula(6, F), " ⇔ ", formula(6, G).
formula_('!'(Xs, F)) --> !, foralls(Xs), formula(0, F).
formula_('?'(Xs, F)) --> !, exists(Xs), formula(0, F).
formula_(S = T) --> !, term(11, S), " = ", term(11, T).
formula_(A) --> term_(A).

foralls([]) --> [].
foralls([X|Xs]) --> "`∀ (", term(X), " : τ ι), ", foralls(Xs).

exists([]) --> [].
exists([X|Xs]) --> "`∃ (", term(X), " : τ ι), ", exists(Xs).

% a clause as a top-level formula: `∀ xs, H_0 ⇒ ... ⇒ ⊥
clause(clause(Xs, Ls)) -->
  { implications(Ls, F0), ( Xs == [] -> F = F0 ; F = '!'(Xs, F0) ) },
  formula(0, F).

implications([], '$false').
implications([L|Ls], (H => F)) :- hypothesis_formula(L, H), implications(Ls, F).


% the type of hypothesis refuting literal L, as an argument of π
hypothesis_type(L) --> { hypothesis_formula(L, F) }, formula(F).

hypothesis_formula(~A, A) :- !.
hypothesis_formula(A, ~A).

term(T) --> term(101, T).

term(P, T) --> { term_priority(T, Q) }, lparen(P, Q), term_(T), rparen(P, Q).

term_priority(T, 100) :- compound(T), T \= '$VAR'(_), !.
term_priority(_, 101).

term_('$VAR'(N)) --> !, "x", number(N).
term_('$any') --> !, "infer_el".
term_(T) --> { T =.. [F|Ts] }, sym(F), variables(Ts).

sym(S) --> { introduced(S, _) }, !, atom(S).
sym(S) --> "{|", atom(S), "¹|}".

atom(A) --> { atom_codes(A, Cs) }, codes(Cs).
number(N) --> { number_codes(N, Cs) }, codes(Cs).

codes([]) --> [].
codes([C|Cs]) --> [C], codes(Cs).

numlist_(N, N, []) :- !.
numlist_(I, N, [I|Is]) :- J is I + 1, numlist_(J, N, Is).
