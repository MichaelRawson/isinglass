/*
lambdapi back end, using the encoding of first-order logic in lambdapi's Stdlib.

A clause ∀xs. L_0 ∨ ... ∨ L_n-1 is stated as Π xs, π (¬ L_0) → ... → π (¬ L_n-1) → π ⊥,
the type of its proof terms in the IR (see ir.pl), which are printed directly.
*/
:- module(lambdapi, [emit/0]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(db).
:- set_prolog_flag(double_quotes, codes).

emit :-
  findall(Name, ir_step(Name, _, _), Names),
  out(prelude),
  out(signature),
  forall(member(Name, Names), out(proof_step(Name))).

out(G) :- phrase(G, Cs), atom_codes(A, Cs), write(A).

prelude -->
  "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq;\n\n",
  "opaque symbol sym (x y : τ ι) : π (x = y) → π (y = x) ≔ λ e, eq_sym e;\n",
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
  { ir_step(Name, Conclusion, Justification) },
  proof_step(Justification, Name, Conclusion).

proof_step(input(_, Input), Name, clause(Xs, Ls)) -->
  { clause_formula(clause(Xs, Ls), F) },
  "constant symbol ", input(Input), " : π ", formula(F), ";\n",
  header(Name), statement(clause(Xs, Ls)), " ≔ ",
  { length(Ls, N), numlist_(0, N, Is) },
  lambdas(Xs, Is),
  cases(Is, input_instance(Input, Xs)), ";\n".
proof_step(split_def(Split, Clause), _, _) -->
  "rule ", sym(Split), " ↪ ", clause(Clause), ";\n".
proof_step(proof(M), Name, Conclusion) -->
  header(Name), conclusion(Conclusion), " ≔ ", proof(M), ";\n".

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
cases([], D) --> call(D).
cases([I], D) --> "(", hypothesis(h(I)), " ", call(D), ")".
cases([I, J|Is], D) -->
  "(∨ₑ ", call(D), " (λ l, ", hypothesis(h(I)), " l) (λ r", number(I), ", ", cases([J|Is], r(I)), "))".

r(I) --> "r", number(I).

input_instance(Input, Xs) --> { phrase(variables(Xs), As) }, application(input(Input), As).

input(Input) --> "{|", atom(Input), "²|}".

/********************************************************************************
 * proof terms
 ********************************************************************************/

% proof terms are printed bare: they occur as binder bodies, which extend rightwards,
% and are parenthesised by operand//1 where they are arguments
proof(lam(X, _, M)) --> !, "λ ", variable(X), binders(M).
proof(let(X, F, M, N)) --> !, "let ", variable(X), " : π ", formula(F), " ≔ ", value(M), " in ", proof(N).
proof(app(F, Ts, Ms)) --> !, head(F), variables(Ts), operands(Ms).
proof(X) --> head(X).

% consecutive λs are merged
binders(lam(X, _, M)) --> !, " ", variable(X), binders(M).
binders(M) --> ", ", proof(M).

% lambdapi does not use the type of a let to elaborate its value, so a λ value's binder is annotated
% (without, inference can be very slow, e.g. PUZ017-1)
value(lam(X, T, M)) --> !, "λ (", variable(X), " : ", annotation(T), ")", binders(M).
value(M) --> proof(M).

annotation('$i') --> !, "τ ι".
annotation(F) --> "π ", formula(F).

head('$sym') --> !, "sym".
head(Name) --> { atom(Name) }, !, atom(Name).
head(X) --> variable(X).

variable(h(N)) --> !, hypothesis(h(N)).
variable(X) --> term(X).

operands([]) --> [].
operands([M|Ms]) --> " ", operand(M), operands(Ms).

operand(app(F, [], [])) --> !, head(F).
operand(M) --> { M = app(_, _, _) ; M = lam(_, _, _) ; M = let(_, _, _, _) }, !, "(", proof(M), ")".
operand(X) --> head(X).

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
implications([L|Ls], (~L => F)) :- implications(Ls, F).

% the type of hypothesis refuting literal L, as an argument of π
hypothesis_type(L) --> formula(~L).

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
