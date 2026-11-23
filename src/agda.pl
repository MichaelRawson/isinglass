/*
Agda back end, for a hammer: a term to fill a hole, constructive by the A-translation.

  Proof.refutation bridge ... bridge
    where
    module Proof {R : Set} (leaf : type) ... where
      step : type
      step = proof term
      ...

R is the ⊥ of the IR (see ir.pl), which Agda infers to be the goal, so the goal is never printed, and
~F is F → R. The leaves are the input clauses and the negated conjecture ~G, parameters of the module:
the negated conjecture is the identity, as R is G, and an input clause is bridged from its Agda term,
assumed to be of the sequent type

  ∀ xs → A_1 → ... → A_n → B_1 ⊎ ... ⊎ B_m      (⊥ if m = 0)

for the negative literals ~A_i and the positive literals B_j of the clause, in order.

Names are printed as they are: the hammer names symbols, sorts and inputs after their Agda terms.
Only the prover's own names, of symbols, steps and definitions, are escaped (see escaped//1).
In scope are assumed _≡_, refl, sym, trans, cong and subst, and for the bridges ⊥-elim and [_,_]′, as in
the standard library.

emit_agda_term prints the same proof as one expression, for a caller that can check an expression
but not declare a module (Agda's reflection: checkFromStringTC), the parameters bound by λ and the
steps by let:

  (λ {R : Set}
        (leaf : type)
        ... →
    let
      step : type
      step = proof term
      ...
    in refutation)
      bridge
      ...

emit_agda_file wraps the term in a module that postulates the signature and the inputs, for testing
on proofs whose names were not chosen for Agda: there, every name is mangled.
*/
:- module(agda, [emit_agda/0, emit_agda_term/0, emit_agda_file/0]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(printing).
:- use_module(utils).
:- set_prolog_flag(double_quotes, codes).

% mangled: names are made Agda identifiers, apart from each other and from ours, for testing
:- dynamic(mangled/0).

emit_agda :- retractall(mangled), decorate, out(fragment).

emit_agda_term :- retractall(mangled), decorate, out(expression).

emit_agda_file :- retractall(mangled), assertz(mangled), decorate, out(file).

/*
Our own names (variables, R, the module Proof, steps and definitions) are in the scope of the names
that are printed as they are (the hammer's symbols and inputs, or mangled ones), so they must not
shadow them: a symbol x0 would be captured by λ x0. So each of our names is decorated, the same
for the whole proof, by as few primes as make it apart from every name printed as it is: usually
none.
*/
:- dynamic(decoration/1).

decorate :-
  retractall(decoration(_)),
  assertz(decoration([])),
  findall(Cs, ( symbol(S, _, _, _), symbol(S, Cs, []) ), Symbols),
  findall(Cs, ( ir_step(_, _, input(_, S)), source(S, Cs, []) ), Sources),
  findall(Cs, ( ir_step(Name, _, _), name(Name, Cs, []) ), Steps),
  append(Symbols, Sources, Theirs),
  decoration(Theirs, Steps, [], D),
  retractall(decoration(_)),
  assertz(decoration(D)).

% the fewest primes D such that none of Theirs is one of our names decorated by D
decoration(Theirs, Steps, D0, D) :-
  (   member(Cs, Theirs), append(Ours, D0, Cs), ours(Ours, Steps)
  ->  append(D0, "′", D1), decoration(Theirs, Steps, D1, D)
  ;   D = D0
  ).

ours(Cs, _) :- memberchk(Cs, ["R", "Proof", "e", "g"]), !.
ours([C|Ds], _) :- memberchk(C, "ahxy"), Ds \== [], each(member(D, Ds), ( D >= 0'0, D =< 0'9 )), !.
ours(Cs, Steps) :- memberchk(Cs, Steps).

% our names are decorated
decorated --> { decoration(D) }, codes(D).

proof_module --> "Proof", decorated.
result --> "R", decorated.

fragment -->
  { proof_parts(Leaves, Refutation, Steps) },
  proof_module, ".", name(Refutation), foldl(bridge, Leaves), "\n",
  "  where\n",
  "  module ", proof_module, " {", result, " : Set}", foldl(parameter, Leaves), "\n",
  "    where\n",
  proof_steps(Steps).

% the steps are printed with the indentation of the module's, which is also that of a let block
expression -->
  { proof_parts(Leaves, Refutation, Steps) },
  "(λ {", result, " : Set}", foldl(parameter, Leaves), " →\n",
  "  let\n",
  proof_steps(Steps),
  "  in ", name(Refutation), ")", foldl(bridge, Leaves), "\n".

proof_parts(Leaves, Refutation, Steps) :-
  leaves(Leaves),
  findall(Name, ir_step(Name, clause([], []), _), Refutations),
  final(Refutations, Refutation),
  findall(step(Name, Conclusion, Justification), ir_step(Name, Conclusion, Justification), Steps).

proof_steps(Steps) --> { cited_steps(Cited) }, foldl(emitted(Cited), Steps).

/********************************************************************************
 * leaves
 ********************************************************************************/

% the input clauses and the negated conjecture, of an atom: other formulas are only cited by todo steps
leaves(Leaves) :-
  findall(leaf(Name, Conclusion, Justification),
          ( ir_step(Name, Conclusion, Justification), leaf(Justification, Conclusion) ),
          Leaves).

leaf(input(_, _), clause(_, _)).
leaf(negated_conjecture(_), formula(~G)) :- \+ connective(G, _).

parameter(leaf(Name, Conclusion, _)) --> "\n      (", name(Name), " : ", conclusion(Conclusion), ")".

bridge(leaf(Name, Conclusion, Justification)) -->
  "\n    (", bridge(Justification, Conclusion), ")  -- ", name(Name).

% the negated conjecture G → R is the identity; an input of sequent type is given its negative
% literals, in continuation-passing style, and its positive literals are refuted by cases
bridge(negated_conjecture(_), _) --> "λ g", decorated, " → g", decorated.
bridge(input(_, Source), clause(Bs, Ls)) -->
  { binder_variables(Bs, Xs),
    length(Ls, N),
    range(0, N, Is),
    signs(Ls, Is, Negatives, Positives) },
  lambdas(Xs, Is),
  foldl(continuation, Negatives),
  cases(Positives), " (", source(Source), arguments(Xs), foldl(antecedent, Negatives), ")",
  foldl(close, Negatives).

% the indices of the negative and of the positive literals
signs([], [], [], []).
signs([~_|Ls], [I|Is], [I|Ns], Ps) :- !, signs(Ls, Is, Ns, Ps).
signs([_|Ls], [I|Is], Ns, [I|Ps]) :- signs(Ls, Is, Ns, Ps).

lambdas([], []) --> !.
lambdas(Xs, Is) --> "λ", arguments(Xs), foldl(hypothesis_binder, Is), " → ".

hypothesis_binder(I) --> " ", hypothesis(I).

% h_i : ¬¬A_i gives a_i : A_i
continuation(I) --> hypothesis(I), " (λ ", antecedent_variable(I), " → ".

antecedent(I) --> " ", antecedent_variable(I).

antecedent_variable(I) --> "a", number(I), decorated.

close(_) --> ")".

cases([]) --> !, "⊥-elim".
cases([I]) --> !, hypothesis(I).
cases([I|Is]) --> "[ ", hypothesis(I), " , ", cases(Is), " ]′".

/********************************************************************************
 * steps
 ********************************************************************************/

% a function symbol is defined by its term, so that its equation holds by reflexivity, stated only if
% a step cites it (Cited)
emitted(Cited, step(Name, clause(Cs, Ls), definition(Symbol, Bs, Body))) --> !,
  { binder_variables(Bs, Xs), binder_variables(Cs, Ys), length(Ys, K), append(Ys, ['$VAR'(K)], Zs) },
  definition(symbol(Symbol), symbol_type(Symbol), defined(Xs, Body)),
  (   { get_assoc(Name, Cited, _) }
  ->  definition(name(Name), conclusion(clause(Cs, Ls)), defined(Zs, '$app'('$VAR'(K), '$refl')))
  ;   []
  ).
% ...and a predicate by its body, where Agda can state it (formulas of clauses), else a hole
emitted(_, step(_, formula(_), definition(Symbol, Bs, Body))) --> !,
  { binder_variables(Bs, Xs) },
  definition(symbol(Symbol), symbol_type(Symbol), defined_predicate(Xs, Body)).
% a step between formulas is classical, so it is left as a hole
emitted(_, step(Name, clause(Bs, Ls), proof(_))) --> { formula_step(Name) }, !,
  definition(name(Name), conclusion(clause(Bs, Ls)), todo(formula_step)).
emitted(_, step(Name, clause(Bs, Ls), proof(M))) --> !,
  definition(name(Name), conclusion(clause(Bs, Ls)), proof(M)).
emitted(_, step(Name, clause(Bs, Ls), todo(Record, _))) --> !,
  definition(name(Name), conclusion(clause(Bs, Ls)), todo(Record)).
emitted(_, _) --> [].

definition(Name, Type, Body) -->
  "    ", call(Name), " : ", call(Type), "\n",
  "    ", call(Name), " = ", call(Body), "\n".

defined([], Body) --> !, body(Body).
defined(Xs, Body) --> "λ", foldl(spaced_variable, Xs), " → ", body(Body).

spaced_variable(X) --> " ", variable(X).

defined_predicate(Xs, Body) --> { stated(Body) }, !, defined(Xs, formula(Body)).
defined_predicate(_, _) --> "{! !}".

stated('!'(_, F)) :- !, stated(F).
stated((F => G)) :- !, stated(F), stated(G).
stated(~F) :- !, stated(F).
stated('$false') :- !.
stated(F) :- \+ connective(F, _).

body(M) --> { M = '$app'(_, _) }, !, proof(M).
body(formula(F)) --> !, type(F).
body(T) --> term(T).

% a polymorphic symbol takes its type arguments first
symbol_type(S) -->
  { symbol(S, Ps, Args, Sort), number_vars(Ps, 0, _) },
  foldl(type_parameter, Ps), foldl(argument_sort, Args), sort(Sort).

todo(esa(Rule, _)) --> !, "{! ", atom(Rule), " !}".
todo(Record) --> { functor(Record, Rule, _) }, "{! ", atom(Rule), " !}".

conclusion(clause(Bs, Ls)) --> { clause_type(clause(Bs, Ls), T) }, type(T).
conclusion(formula(F)) --> type(F).

/********************************************************************************
 * proof terms
 ********************************************************************************/

% proof terms are printed bare, and parenthesised by operand//1 where they are arguments
proof('$lam'(X, _, M)) --> !, "λ ", variable(X), binders(M).
% a redex of one hypothesis is a let
proof('$app'('$lam'(X, '$proof'(F), N), M)) --> !,
  "let ", variable(X), " : ", type(F), " ; ", variable(X), " = ", proof(M), " in ", proof(N).
proof('$rewrite'(X:_, A, E, M)) --> !, rewritten(A, X, E, M).
% an argument is a proof or a first-order term
proof(M) --> { M = '$app'(_, _), spine(M, F, As) }, !, head(F), foldl(spaced_argument, As).
proof(X) --> head(X).

% consecutive λs are merged
binders('$lam'(X, _, M)) --> !, " ", variable(X), binders(M).
binders(M) --> " → ", proof(M).

head('$sym') --> !, "sym".
head('$refl') --> !, "refl".
head('$VAR'(N)) --> !, variable('$VAR'(N)).
head(Name) --> { atom(Name) }, !, name(Name).
head(M) --> "(", proof(M), ")".

spaced_operand(M) --> " ", operand(M).

spaced_argument(M) --> { proof_argument(M) }, !, spaced_operand(M).
spaced_argument(T) --> argument(T).

operand(M) --> { compound(M), M \= '$VAR'(_) }, !, "(", proof(M), ")".
operand(X) --> head(X).

% the hypotheses of an input's bridge, by the index of their literals
hypothesis(I) --> "h", number(I), decorated.

variable('$VAR'(N)) --> "x", number(N), decorated.
variable('$BOUND'(N)) --> "y", number(N), decorated.

/********************************************************************************
 * rewriting
 ********************************************************************************/

/*
E : l ≡ r rewrites M : A[l] to A[r], where X marks l in the motive A. An equation s[l] ≡ t[l] is
rewritten by a path, a chain of trans: back along s, then M, then along t, flattened where M or
a step is itself such a rewrite. A negated equation is
applied to the path the other way, from e : s[r] ≡ t[r]. Any other literal is rewritten by subst.

The steps of a path are e, proof(M), eq(E) and cong(X, S, P), for P along the side S[X];
none is no step, where X does not occur in the side.
*/
rewritten('$='(A, S, T), X, E, M) --> !, path([proof('$rewrite'(X:_, '$='(A, S, T), E, M))]).
rewritten(~'$='(A, S, T), X, E, M) --> !,
  "λ e", decorated, " → ", refutation('$rewrite'(X:_, ~'$='(A, S, T), E, M), [e]).
rewritten(A, X, E, M) -->
  "subst (λ ", variable(X), " → ", type(A), ") ", operand(E), " ", operand(M).

% M refutes the equation of the path Ps; a rewrite of M lengthens the path instead
refutation('$rewrite'(X:_, ~'$='(_, S, T), E, M), Ps) --> !,
  { side(X, S, E, P), side(X, T, E, Q), inverse(Q, Q1), append([P|Ps], [Q1], Ps1) },
  refutation(M, Ps1).
refutation(M, Ps) --> operand(M), " ", { present(Ps, Qs) }, path_operand(Qs).

% the step along the side S: E itself at the top, and cong below it
side(X, S, E, eq(E)) :- S == X, !.
side(X, S, E, cong(X, S, eq(E))) :- \+ substitute(X, [], S, S), !.
side(_, _, _, none).

inverse(none, none).
inverse(eq(E), eq(E1)) :- inverted(E, E1).
inverse(cong(X, S, P), cong(X, S, Q)) :- inverse(P, Q).

% sym E, with sym pushed down to the hypotheses: through a rewrite of an equation L = R, which is a
% rewrite of sym of its proof by R = L, to cancel against sym
inverted('$app'('$sym', E), E) :- !.
inverted('$rewrite'(X, '$='(A, L, R), E, M0), '$rewrite'(X, '$='(A, R, L), E, M)) :- !, inverted(M0, M).
inverted(E, '$app'('$sym', E)).

% the steps of a path, flat: a step whose proof is a rewrite of an equation is its own path
present([], []).
present([none|Ps], Qs) :- !, present(Ps, Qs).
present([P|Ps], Qs) :- step_path(P, Ps1), !, append(Ps1, Ps, Ps2), present(Ps2, Qs).
present([P|Ps], [P|Qs]) :- present(Ps, Qs).

step_path(proof(M), Ps) :- equation_path(M, Ps).
step_path(eq(E), Ps) :- equation_path(E, Ps).

equation_path('$rewrite'(X:_, '$='(_, S, T), E, M), [P1, proof(M), Q]) :-
  side(X, S, E, P), side(X, T, E, Q), inverse(P, P1).
equation_path('$app'('$sym', E), Ps) :-
  E = '$rewrite'(_, '$='(_, _, _), _, _),
  inverted(E, E1),
  equation_path(E1, Ps).

path(Ps) --> { present(Ps, Qs) }, steps(Qs).

steps([P]) --> !, path_step(P).
steps([P|Ps]) --> "trans ", path_operand([P]), " ", path_operand(Ps).

path_operand([e]) --> !, "e", decorated.
path_operand([proof(M)]) --> !, operand(M).
path_operand([eq(E)]) --> !, operand(E).
path_operand(Ps) --> "(", steps(Ps), ")".

path_step(e) --> "e", decorated.
path_step(proof(M)) --> proof(M).
path_step(eq(E)) --> proof(E).
path_step(cong(X, S, P)) --> "cong (λ ", variable(X), " → ", term(S), ") ", path_operand([P]).

/********************************************************************************
 * types and terms
 ********************************************************************************/

% the types of the IR: ~F is F → R, and '$false' is R
type('!'(B, F)) --> !, pi(B), type(F).
type((F => G)) --> !, domain(F), " → ", type(G).
type(~F) --> !, domain(F), " → ", result.
type('$false') --> !, result.
type('$='(_, S, T)) --> !, term(S), " ≡ ", term(T).
type(A) --> term(A).

pi(X:S) --> "(", variable(X), " : ", sort(S), ") → ".

domain(F) --> { F = '!'(_, _) ; F = (_ => _) ; F = ~_ }, !, "(", type(F), ")".
domain(F) --> type(F).

% types and propositions are both in Set
sort('$tType') --> !, "Set".
sort('$o') --> !, "Set".
sort(S) --> term(S).

% an arbitrary individual, or type, is left as a hole
term('$VAR'(N)) --> !, variable('$VAR'(N)).
term('$BOUND'(N)) --> !, variable('$BOUND'(N)).
term('$inhabited'(_)) --> !, "{! !}".
term('$i') --> !, "ι".
term(T) --> { T =.. [F|Ts] }, symbol(F), arguments(Ts).

% the prover's own symbols are renamed, as _ marks an argument place in an Agda name: spl0_1 is spl0-1
symbol(F) --> { mangled }, !, escaped(F), "′".
symbol(F) --> { introduced(F, _) }, !, escaped(F).
symbol(F) --> atom(F).

% the Agda term of an input
source(S) --> { named(input, Bare, S) }, ( { mangled } -> escaped(Bare), "″" ; atom(Bare) ).

% steps and definitions are the prover's and ours, so they are escaped, apart from each other by the
% mark of a definition, and from the Agda names of symbols and inputs (the hammer's, or mangled)
name(Name) --> { named(step, Bare, Name) }, !, escaped(Bare), decorated.
name(Name) --> { named(definition, Symbol, Name) }, escaped(Symbol), "ᵈᵉᶠ", decorated.

% a name as an Agda identifier, one to one: ASCII letters and digits are kept (but for a leading
% digit), _ between them is -, as _ marks an argument place, and any other character is ·HH·, its
% code in hex, so that names from SMT-LIB (with ., @, - or spaces) are Agda identifiers too
escaped(F) --> { atom_codes(F, Cs) }, escaped_codes(Cs, start).

escaped_codes([], _) --> [].
escaped_codes([C|Cs], Previous) --> escaped_code(C, Previous, Cs), escaped_codes(Cs, C).

escaped_code(C, Previous, _) --> { alphanumeric(C), \+ ( Previous == start, C >= 0'0, C =< 0'9 ) }, !, [C].
escaped_code(0'_, Previous, [Next|_]) --> { alphanumeric(Previous), alphanumeric(Next) }, !, "-".
escaped_code(C, _, _) --> "·", hex(C), "·".

alphanumeric(C) :- integer(C), ( C >= 0'a, C =< 0'z ; C >= 0'A, C =< 0'Z ; C >= 0'0, C =< 0'9 ), !.

hex(N) --> { N < 16 }, !, hex_digit(N).
hex(N) --> { H is N // 16, L is N mod 16 }, hex(H), hex_digit(L).

hex_digit(D) --> { D < 10 -> C is 0'0 + D ; C is 0'a + D - 10 }, [C].

arguments(Ts) --> foldl(argument, Ts).

argument(T) --> { compound(T), T \= '$VAR'(_), T \= '$inhabited'(_) }, !, " (", term(T), ")".
argument(T) --> " ", term(T).

/********************************************************************************
 * a module to check, with the signature and the inputs postulated
 ********************************************************************************/

file -->
  { findall(S, ( symbol(S, _, _, _), \+ ir_step(_, _, definition(S, _, _)) ), Symbols),
    leaves(Leaves) },
  "{-# OPTIONS --allow-unsolved-metas #-}\n",
  "open import Agda.Builtin.Equality\n",
  "open import Data.Empty\n",
  "open import Data.Sum.Base\n",
  "open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; subst)\n\n",
  "postulate\n",
  "  ι : Set\n",
  foldl(declaration, Symbols),
  foldl(postulated, Leaves),
  "\ngoal : ", goal(Leaves), "\n",
  "goal = ", fragment.

% split symbols and defined function symbols are defined in the proof
declaration(S) --> "  ", symbol(S), " : ", symbol_type(S), "\n".

type_parameter(P) --> pi(P:'$tType').

argument_sort(S) --> sort(S), " → ".

postulated(leaf(_, clause(Bs, Ls), input(_, Source))) --> !,
  { length(Ls, N), range(0, N, Is), signs(Ls, Is, _, Positives) },
  "  ", source(Source), " : ", foldl(pi, Bs), foldl(negative, Ls), positives(Positives, Ls), "\n".
postulated(_) --> [].

negative(~A) --> !, type(A), " → ".
negative(_) --> [].

positives([], _) --> !, "⊥".
positives([I], Ls) --> !, { nth0(I, Ls, B) }, type(B).
positives([I|Is], Ls) --> { nth0(I, Ls, B) }, type(B), " ⊎ ", positives(Is, Ls).

% the conjecture, or anything at all if the proof is a refutation of the inputs
goal(Leaves) --> { member(leaf(_, formula(~G), _), Leaves) }, !, type(G).
goal(_) --> "{", result, " : Set} → ", result.
