/*
lambdapi back end, using the encoding of first-order logic in lambdapi's Stdlib.

A clause ∀xs. L_0 ∨ ... ∨ L_n-1 is stated as Π xs, π (¬ L_0) → ... → π (¬ L_n-1) → π ⊥,
the type of its proof terms in the IR (see ir.pl), which are printed directly.
*/
:- module(lambdapi, [emit/0]).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(printing).
:- use_module(signature).
:- use_module(utils).
:- set_prolog_flag(double_quotes, codes).

emit :-
  out(prelude),
  out(signature),
  forall(ir_step(Name, Conclusion, Justification), out(proof_step(Justification, Name, Conclusion))).

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
  { length(Args, N) },
  Keyword, sym(S/N), " : ", arrows(Args, Sort), ";\n",
  declarations(Keyword, Ss).

arrows([], Sort) --> sort(Sort).
arrows([A|As], Sort) --> sort(A), " → ", arrows(As, Sort).

sort('$i') --> "τ ι".
sort('$o') --> "Prop".

/********************************************************************************
 * steps
 ********************************************************************************/

proof_step(input(_, Input), Name, clause(Bs, Ls)) -->
  { clause_formula(clause(Bs, Ls), F) },
  "constant symbol ", input(Input), " : π ", formula(F), ";\n",
  header(Name), statement(clause(Bs, Ls)), " ≔ ",
  { binder_variables(Bs, Xs), length(Ls, N), range(0, N, Is) },
  lambdas(Xs, Is),
  cases(Is, input_instance(Input, Xs)), ";\n".
proof_step(split_def(Split, Clause), _, _) -->
  "rule ", sym(Split/0), " ↪ ", clause(Clause), ";\n".
proof_step(proof(M), Name, Conclusion) -->
  header(Name), conclusion(Conclusion), " ≔ ", proof(M), ";\n".

proof_step(todo(Record, _), Name, Conclusion) -->
  { functor(Record, Rule, _) },
  header(Name), conclusion(Conclusion), " ≔ begin admit end; // TODO ", atom(Rule), "\n".

header(Name) --> "opaque symbol ", atom(Name), " : ".

conclusion(clause(Bs, Ls)) --> statement(clause(Bs, Ls)).
conclusion(formula(F)) --> "π ", formula(F).

% step statements use framework-level Π and →, rather than `∀ and ⇒ which must be rewritten
statement(clause(Bs, Ls)) --> pis(Bs), arrows_to(Ls).

pis([]) --> [].
pis([X:S|Bs]) --> "Π (", term(X), " : ", sort(S), "), ", pis(Bs).

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

input_instance(Input, []) --> !, input(Input).
input_instance(Input, Xs) --> "(", input(Input), variables(Xs), ")".

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
value(lam(X, T, M)) --> !, "λ (", variable(X), " : ", annotation(X, T), ")", binders(M).
value(M) --> proof(M).

% an eigenvariable has a sort, and a hypothesis a formula
annotation('$VAR'(_), S) --> !, sort(S).
annotation(_, F) --> "π ", formula(F).

% a head is a built-in, a hypothesis or a step
head('$sym') --> !, "sym".
head(h(N)) --> !, hypothesis(h(N)).
head(Name) --> { atom(Name) }, atom(Name).

variable(h(N)) --> !, hypothesis(h(N)).
variable(X) --> term(X).

operands([]) --> [].
operands([M|Ms]) --> " ", operand(M), operands(Ms).

operand(app(F, [], [])) --> !, head(F).
operand(M) --> { M = app(_, _, _) ; M = lam(_, _, _) ; M = let(_, _, _, _) }, !, "(", proof(M), ")".
operand(X) --> head(X).

hypothesis(h(I)) --> "h", number(I).

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
foralls([X:S|Bs]) --> "`∀ (", term(X), " : ", sort(S), "), ", foralls(Bs).

exists([]) --> [].
exists([X:S|Bs]) --> "`∃ (", term(X), " : ", sort(S), "), ", exists(Bs).

% a clause as a top-level formula: `∀ xs, H_0 ⇒ ... ⇒ ⊥
clause(C) --> { clause_type(C, F) }, formula(0, F).

% the type of hypothesis refuting literal L, as an argument of π
hypothesis_type(L) --> formula(~L).

term(T) --> term(101, T).

term(P, T) --> { term_priority(T, Q) }, lparen(P, Q), term_(T), rparen(P, Q).

term_priority(T, 100) :- compound(T), T \= '$VAR'(_), !.
term_priority(_, 101).

term_('$VAR'(N)) --> !, "x", number(N).
term_('$inhabited') --> !, "infer_el".
term_(T) --> { T =.. [F|Ts], length(Ts, N) }, sym(F/N), variables(Ts).

sym(F/_) --> { introduced(F, _) }, !, atom(F).
sym(F/N) --> "{|", atom(F), arity(F, N), "¹|}".

% a name overloaded by arity is told apart by its arity
arity(F, N) --> { overloaded(F/N) }, !, "/", number(N).
arity(_, _) --> [].
