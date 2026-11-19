/*
lambdapi back end, using the encoding of first-order logic in lambdapi's Stdlib.

A clause ∀xs. L_0 ∨ ... ∨ L_n-1 is stated as Π xs, π (¬ L_0) → ... → π (¬ L_n-1) → π ⊥,
the type of its proof terms in the IR (see ir.pl), which are printed directly.

The negated conjecture ~G is a hypothesis, not an axiom: each step that depends on it (its cone)
takes it as a parameter, named after it, and the conjecture is proved by ¬¬-elimination, the only
use of Stdlib.Classic.
*/
:- module(lambdapi, [emit_lambdapi/0]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(printing).
:- use_module(signature).
:- use_module(utils).
:- set_prolog_flag(double_quotes, codes).

% negated(Name, G): Name is the negated conjecture ~G
% cone(Name): step Name depends on the negated conjecture
:- dynamic(negated/2).
:- dynamic(cone/1).

emit_lambdapi :-
  retractall(negated(_, _)),
  retractall(cone(_)),
  each(ir_step(Name, _, Justification), mark(Name, Justification)),
  out(prelude),
  out(signature),
  each(ir_step(Name, Conclusion, Justification), out(proof_step(Justification, Name, Conclusion))).

% steps are in dependency order, so the cone is found in one pass
mark(Name, negated_conjecture(_)) :- !, ir_step(Name, formula(~G), _), assertz(negated(Name, G)).
mark(_, conjecture(_, _, _)) :- !.
mark(Name, Justification) :-
  reference(Justification, N),
  ( negated(N, _) ; cone(N) ), !,
  assertz(cone(Name)).
mark(_, _).

% ∀ₜ and ∃ₜ quantify over types, so that the type variables of TF1 can be bound within a formula
prelude -->
  "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq", classic, epsilon, ";\n\n",
  "constant symbol ∀ₜ : (Set → Prop) → Prop;\nnotation ∀ₜ quantifier;\n",
  "rule π (∀ₜ $p) ↪ Π a : Set, π ($p a);\n",
  "constant symbol ∃ₜ : (Set → Prop) → Prop;\nnotation ∃ₜ quantifier;\n",
  "opaque symbol sym (a : Set) (x y : τ a) : π (x = y) → π (y = x) ≔ λ e, eq_sym e;\n",
  "opaque symbol refl (a : Set) (x : τ a) : π (x = x) ≔ eq_refl x;\n",
  "opaque symbol rw [a] [x y : τ a] (p : τ a → Prop) : π (x = y) → π (p x) → π (p y) ≔ λ e h, ind_eq (eq_sym e) p h;\n",
  rules, type_choice, "\n".

% the expansion rules (see ir.pl), proved once; those for ¬⇔ and ¬∀ are classical,
% and those for quantifiers over types are apart (_t), with the rules of ∃ₜ
rules --> { formula_step(_) }, !,
  "opaque symbol and_e [p q] : π (p ∧ q) → (π p → π q → π ⊥) → π ⊥ ≔ λ h k, k (∧ₑ₁ h) (∧ₑ₂ h);\n",
  "opaque symbol or_e [p q] : π (p ∨ q) → (π p → π ⊥) → (π q → π ⊥) → π ⊥ ≔ λ h k l, ∨ₑ h k l;\n",
  "opaque symbol imp_e [p q] : π (p ⇒ q) → (π (¬ p) → π ⊥) → (π q → π ⊥) → π ⊥ ≔ λ h k l, k (λ x, l (h x));\n",
  "opaque symbol iff_e [p q] : π (p ⇔ q) → (π p → π q → π ⊥) → (π (¬ p) → π (¬ q) → π ⊥) → π ⊥ ≔\n",
  "  λ h k l, l (λ x, k x (∧ₑ₁ h x)) (λ y, k (∧ₑ₂ h y) y);\n",
  "opaque symbol nand_e [p q] : π (¬ (p ∧ q)) → (π (¬ p) → π ⊥) → (π (¬ q) → π ⊥) → π ⊥ ≔ λ h k l, k (λ x, l (λ y, h (∧ᵢ x y)));\n",
  "opaque symbol nor_e [p q] : π (¬ (p ∨ q)) → (π (¬ p) → π (¬ q) → π ⊥) → π ⊥ ≔ λ h k, k (λ x, h (∨ᵢ₁ x)) (λ y, h (∨ᵢ₂ y));\n",
  "opaque symbol nimp_e [p q] : π (¬ (p ⇒ q)) → (π p → π (¬ q) → π ⊥) → π ⊥ ≔ λ h k, h (λ x, ⊥ₑ (k x (λ y, h (λ _, y))));\n",
  "opaque symbol niff_e [p q] : π (¬ (p ⇔ q)) → (π p → π (¬ q) → π ⊥) → (π (¬ p) → π q → π ⊥) → π ⊥ ≔\n",
  "  λ h k l, ∨ₑ (em p) (λ x, k x (λ y, h (∧ᵢ (λ _, y) (λ _, x))))\n",
  "    (λ nx, ∨ₑ (em q) (λ y, l nx y) (λ ny, h (∧ᵢ (λ x, ⊥ₑ (nx x)) (λ y, ⊥ₑ (ny y)))));\n",
  "opaque symbol ex_e [a] [p : τ a → Prop] : π (`∃ x, p x) → (Π x, π (p x) → π ⊥) → π ⊥ ≔ λ h k, ∃ₑ h k;\n",
  "opaque symbol nall_e [a] [p : τ a → Prop] : π (¬ (`∀ x, p x)) → (Π x, π (¬ (p x)) → π ⊥) → π ⊥ ≔\n",
  "  λ h k, h (λ x, ¬¬ₑ (p x) (λ n, k x n));\n",
  "opaque symbol nex_e [a] [p : τ a → Prop] : π (¬ (`∃ x, p x)) → Π x, π (¬ (p x)) ≔ λ h x y, h (∃ᵢ x y);\n",
  "constant symbol ∃ₜᵢ [p] (a : Set) : π (p a) → π (∃ₜ p);\n",
  "symbol ∃ₜₑ [p] : π (∃ₜ p) → Π [q], (Π a, π (p a) → π q) → π q;\n",
  "opaque symbol ex_t [p : Set → Prop] : π (`∃ₜ a, p a) → (Π a, π (p a) → π ⊥) → π ⊥ ≔ λ h k, ∃ₜₑ h k;\n",
  "opaque symbol nall_t [p : Set → Prop] : π (¬ (`∀ₜ a, p a)) → (Π a, π (¬ (p a)) → π ⊥) → π ⊥ ≔\n",
  "  λ h k, h (λ a, ¬¬ₑ (p a) (λ n, k a n));\n",
  "opaque symbol nex_t [p : Set → Prop] : π (¬ (`∃ₜ a, p a)) → Π a, π (¬ (p a)) ≔ λ h a y, h (∃ₜᵢ a y);\n".
rules --> [].

/********************************************************************************
 * signature
 ********************************************************************************/

% a polymorphic symbol takes its type arguments first, as Π (x0 : Set), ...
signature -->
  { findall(S-T, (symbol(S, Ps, Args, Sort), \+ introduced(S, _), T = Ps-Args-Sort), Original),
    findall(S-T, (symbol(S, Ps, Args, Sort), introduced(S, _), T = Ps-Args-Sort), Introduced) },
  declarations("constant symbol ", Original),
  declarations("symbol ", Introduced),
  "\n".

declarations(_, []) --> [].
declarations(Keyword, [S-(Ps-Args-Sort)|Ss]) -->
  { length(Ps, K), length(Args, M), N is K + M, number_vars(Ps, 0, _) },
  codes(Keyword), sym(S/N), " : ", params(Ps), arrows(Args, Sort), ";\n",
  declarations(Keyword, Ss).

params([]) --> [].
params([P|Ps]) --> "Π (", term(P), " : Set), ", params(Ps).

arrows([], Sort) --> sort(Sort).
arrows([A|As], Sort) --> sort(A), " → ", arrows(As, Sort).

classic --> { negated(_, _) ; formula_step(_) }, !, " Stdlib.Classic".
classic --> [].

epsilon --> { ir_step(_, _, skolem_def(_, _, _)) }, !, " Stdlib.Epsilon".
epsilon --> [].

% a Skolem symbol defined by the δ formula F, whose variable is of sort S
skolem_delta(F, S) :- ir_step(_, _, skolem_def(_, _, F)), delta_body(F, _:S, _).

% Stdlib's ε chooses an element of a Set: a type is chosen by εₜ, as ∃ₜ quantifies over types
type_choice --> { skolem_delta(_, S), S == '$tType' }, !,
  "constant symbol εₜ : (Set → Prop) → Set;\n",
  "symbol εₜᵢ (p : Set → Prop) : π (∃ₜ p) → π (p (εₜ p));\n".
type_choice --> [].

% sorts are terms of sort Set
sort('$tType') --> !, "Set".
sort('$o') --> !, "Prop".
sort(S) --> "τ ", term(S).

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
proof_step(input(_, Input), Name, formula(F)) -->
  "constant symbol ", input(Input), " : π ", formula(F), ";\n",
  header(Name), "π ", formula(F), " ≔ ", input(Input), ";\n".
proof_step(negated_conjecture(_), Name, formula(F)) -->
  "// ", atom(Name), " : π ", formula(F), " is a parameter of the steps that depend on it\n".
proof_step(conjecture(_, Negated, Refutation), Name, formula(G)) -->
  header(Name), "π ", formula(G), " ≔ ¬¬ₑ ", formula(G), " (λ ", atom(Negated), ", ", head(Refutation), ");\n".
% a Skolem symbol unfolds to its choice, ε Y. T, and its choice axiom is εᵢ; a type is chosen by εₜ
proof_step(skolem_def(Sk, Bs, F), Name, formula(_)) -->
  { length(Bs, N), binder_variables(Bs, Xs), choice_axiom(Sk, Bs, F, A), consequent(A, T1), delta_body(F, Y:S, T) },
  "rule ", sym(Sk/N), " ↪ ", abstraction(Xs), epsilon(S), " (λ (", term(Y), " : ", sort(S), "), ", formula(0, T), ");\n",
  header(Name), pis(Bs), "π ", formula(F), " → π ", formula(T1), " ≔ λ", variables(Xs), " h, ",
  epsilon(S), "ᵢ (λ (", term(Y), " : ", sort(S), "), ", formula(0, T), ") h;\n".
% a function symbol unfolds to its definition, so that its equation holds by reflexivity
proof_step(definition(Symbol, Bs, Body), Name, clause(Cs, [Eq])) -->
  { length(Bs, N), binder_variables(Bs, Xs), binder_variables(Cs, Ys), Eq = '$='(S, A, _) },
  "rule ", sym(Symbol/N), " ↪ ", abstraction(Xs), term(0, Body), ";\n",
  header(Name), statement(clause(Cs, [Eq])), " ≔ λ", variables(Ys), " h0, h0 (refl ", term(S), " ", term(A), ");\n".
% ...and a predicate unfolds to its body, so that each side of its definition implies the other
proof_step(definition(Symbol, Bs, Body), Name, formula(F)) -->
  { length(Bs, N), binder_variables(Bs, Xs) },
  "rule ", sym(Symbol/N), " ↪ ", abstraction(Xs), formula(0, Body), ";\n",
  header(Name), "π ", formula(F), " ≔ ", abstraction(Xs), "∧ᵢ (λ h, h) (λ h, h);\n".
proof_step(proof(M), Name, Conclusion) -->
  header(Name), assumption(Name), conclusion(Conclusion), " ≔ ", discharge(Name), proof(M), ";\n".

proof_step(todo(Record, _), Name, Conclusion) -->
  header(Name), assumption(Name), conclusion(Conclusion), " ≔ begin admit end; // TODO ", rule(Record), "\n".

rule(esa(Rule, _)) --> !, atom(Rule).
rule(Record) --> { functor(Record, Rule, _) }, atom(Rule).

header(Name) --> "opaque symbol ", atom(Name), " : ".

% a step in the cone of the negated conjecture takes it as a parameter
assumption(Name) --> { cone(Name), negated(N, G) }, !, "Π (", atom(N), " : π ", formula(~G), "), ".
assumption(_) --> [].

discharge(Name) --> { cone(Name), negated(N, _) }, !, "λ ", atom(N), ", ".
discharge(_) --> [].

conclusion(clause(Bs, Ls)) --> statement(clause(Bs, Ls)).
conclusion(formula(F)) --> "π ", formula(F).

% step statements use framework-level Π and →, rather than `∀ and ⇒ which must be rewritten
statement(clause(Bs, Ls)) --> pis(Bs), arrows_to(Ls).

pis([]) --> [].
pis([X:S|Bs]) --> "Π (", term(X), " : ", sort(S), "), ", pis(Bs).

arrows_to([]) --> "π ⊥".
arrows_to([L|Ls]) --> "π ", hypothesis_type(L), " → ", arrows_to(Ls).

abstraction([]) --> [].
abstraction([X|Xs]) --> "λ", variables([X|Xs]), ", ".

consequent(A, T) :- quantifier_prefix('!', A, _, (_ => T)).

% the δ formula F, ?[Y:S|Ys] : G, is opened with Y for the body T
delta_body(F, B, T) :- rule_type('$ex', F, ('!'([B], (T => '$false')) => '$false')).

epsilon(S) --> { S == '$tType' }, !, "εₜ".
epsilon(_) --> "ε".

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
proof(let(X, '!'([B:S], F), app('$nex', [], [M]), N)) --> !,
  "let ", variable(X), " : π ", formula('!'([B:S], F)), " ≔ ", not_exists(S), " ", operand(M), " in ", proof(N).
proof(let(X, F, M, N)) --> !, "let ", variable(X), " : π ", formula(F), " ≔ ", value(M), " in ", proof(N).
% rw, as rewrite is a lambdapi keyword
proof(rewrite(X:S, A, E, M)) --> !,
  "rw (λ (", term(X), " : ", sort(S), "), ", formula(0, A), ") ", operand(E), " ", operand(M).
proof(app('$dne', [F], [M])) --> !, "¬¬ₑ ", formula(F), " ", operand(M).
% the eigenvariable of a δ rule may be a type
proof(app(Rule, [], [M, lam(X, S, K)])) --> { S == '$tType', type_rule(Rule, Codes) }, !,
  codes(Codes), " ", operand(M), " ", operand(lam(X, S, K)).
proof(app(F, Ts, Ms)) --> !, head(F), variables(Ts), operands(Ms).
proof(X) --> head(X).

not_exists('$tType') --> !, "nex_t".
not_exists(_) --> "nex_e".

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
head('$refl') --> !, "refl".
head('$trivial') --> !, "⊤ᵢ".
head(Rule) --> { rule_symbol(Rule, Codes) }, !, codes(Codes).
head(h(N)) --> !, hypothesis(h(N)).
head(Name) --> { atom(Name), cone(Name), negated(N, _) }, !, "(", atom(Name), " ", atom(N), ")".
head(Name) --> { atom(Name) }, atom(Name).

rule_symbol('$and', "and_e").
rule_symbol('$or', "or_e").
rule_symbol('$imp', "imp_e").
rule_symbol('$iff', "iff_e").
rule_symbol('$nand', "nand_e").
rule_symbol('$nor', "nor_e").
rule_symbol('$nimp', "nimp_e").
rule_symbol('$niff', "niff_e").
rule_symbol('$ex', "ex_e").
rule_symbol('$nall', "nall_e").

type_rule('$ex', "ex_t").
type_rule('$nall', "nall_t").

variable(h(N)) --> !, hypothesis(h(N)).
variable(X) --> term(X).

operands([]) --> [].
operands([M|Ms]) --> " ", operand(M), operands(Ms).

operand(app(F, [], [])) --> !, head(F).
operand(M) --> { M = app(_, _, _) ; M = lam(_, _, _) ; M = let(_, _, _, _) ; M = rewrite(_, _, _, _) }, !, "(", proof(M), ")".
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
priority((_ | _), 6) :- !.
priority((_ & _), 7) :- !.
priority((_ => _), 5) :- !.
priority((_ <=> _), 5) :- !.
priority('!'(_, _), 0) :- !.
priority('?'(_, _), 0) :- !.
priority('$='(_, _, _), 10) :- !.
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
formula_('$='(_, S, T)) --> !, term(11, S), " = ", term(11, T).
formula_(A) --> term_(A).

% type variables are bound by ∀ₜ and ∃ₜ
foralls([]) --> [].
foralls([X:S|Bs]) --> "`", quantifier("∀", S), " (", term(X), " : ", sort(S), "), ", foralls(Bs).

exists([]) --> [].
exists([X:S|Bs]) --> "`", quantifier("∃", S), " (", term(X), " : ", sort(S), "), ", exists(Bs).

quantifier(Q, '$tType') --> !, codes(Q), "ₜ".
quantifier(Q, _) --> codes(Q).

% a clause as a top-level formula: `∀ xs, H_0 ⇒ ... ⇒ ⊥

% the type of hypothesis refuting literal L, as an argument of π
hypothesis_type(L) --> formula(~L).

term(T) --> term(101, T).

term(P, T) --> { term_priority(T, Q) }, lparen(P, Q), term_(T), rparen(P, Q).

term_priority(T, 100) :- compound(T), T \= '$VAR'(_), T \= '$BOUND'(_), !.
term_priority(_, 101).

term_('$VAR'(N)) --> !, "x", number(N).
term_('$BOUND'(N)) --> !, "y", number(N).
term_('$inhabited'(S)) --> !, "el ", term(S).
term_('$i') --> !, "ι".
term_(T) --> { T =.. [F|Ts], length(Ts, N) }, sym(F/N), variables(Ts).

sym(F/_) --> { introduced(F, _) }, !, atom(F).
sym(F/N) --> "{|", atom(F), arity(F, N), "¹|}".

% a name overloaded by arity is told apart by its arity
arity(F, N) --> { overloaded(F/N) }, !, "/", number(N).
arity(_, _) --> [].
