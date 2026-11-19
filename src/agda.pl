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
Only the prover's own symbols are renamed.
In scope are assumed _≡_, refl, sym, trans, cong and subst, and for the bridges ⊥-elim and [_,_]′, as in
the standard library.

emit_agda_file wraps the term in a module that postulates the signature and the inputs, for testing
on proofs whose names were not chosen for Agda: there, every name is mangled.
*/
:- module(agda, [emit_agda/0, emit_agda_file/0]).
:- use_module(library(lists)).
:- use_module(ops).
:- use_module(logic).
:- use_module(ir).
:- use_module(db).
:- use_module(printing).
:- use_module(utils).
:- set_prolog_flag(double_quotes, codes).

% mangled: names are made Agda identifiers, apart from each other and from ours, for testing
:- dynamic(mangled/0).

emit_agda :- retractall(mangled), out(fragment).

emit_agda_file :- retractall(mangled), assertz(mangled), out(file).

fragment -->
  { leaves(Leaves),
    findall(Name, ir_step(Name, clause([], []), _), Refutations),
    final(Refutations, Refutation),
    findall(step(Name, Conclusion, Justification), ir_step(Name, Conclusion, Justification), Steps) },
  "Proof.", atom(Refutation), foldl(bridge, Leaves), "\n",
  "  where\n",
  "  module Proof {R : Set}", foldl(parameter, Leaves), "\n",
  "    where\n",
  foldl(emitted, Steps).

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

parameter(leaf(Name, Conclusion, _)) --> "\n      (", atom(Name), " : ", conclusion(Conclusion), ")".

bridge(leaf(Name, Conclusion, Justification)) -->
  "\n    (", bridge(Justification, Conclusion), ")  -- ", atom(Name).

% the negated conjecture G → R is the identity; an input of sequent type is given its negative
% literals, in continuation-passing style, and its positive literals are refuted by cases
bridge(negated_conjecture(_), _) --> "λ g → g".
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

hypothesis_binder(I) --> " ", variable(h(I)).

% h_i : ¬¬A_i gives a_i : A_i
continuation(I) --> variable(h(I)), " (λ a", number(I), " → ".

antecedent(I) --> " a", number(I).

close(_) --> ")".

cases([]) --> !, "⊥-elim".
cases([I]) --> !, variable(h(I)).
cases([I|Is]) --> "[ ", variable(h(I)), " , ", cases(Is), " ]′".

/********************************************************************************
 * steps
 ********************************************************************************/

% a function symbol is defined by its term, so that its equation holds by reflexivity
emitted(step(Name, clause(Cs, Ls), definition(Symbol, Bs, Body))) --> !,
  { binder_variables(Bs, Xs), binder_variables(Cs, Ys), append(Ys, [h(0)], Zs) },
  definition(symbol(Symbol), symbol_type(Symbol), defined(Xs, Body)),
  definition(atom(Name), conclusion(clause(Cs, Ls)), defined(Zs, app(h(0), [], ['$refl']))).
% ...and a predicate by its body, where Agda can state it (formulas of clauses), else a hole
emitted(step(_, formula(_), definition(Symbol, Bs, Body))) --> !,
  { binder_variables(Bs, Xs) },
  definition(symbol(Symbol), symbol_type(Symbol), defined_predicate(Xs, Body)).
% a step between formulas is classical, so it is left as a hole
emitted(step(Name, clause(Bs, Ls), proof(_))) --> { formula_step(Name) }, !,
  definition(atom(Name), conclusion(clause(Bs, Ls)), todo(formula_step)).
emitted(step(Name, clause(Bs, Ls), proof(M))) --> !,
  definition(atom(Name), conclusion(clause(Bs, Ls)), proof(M)).
emitted(step(Name, clause(Bs, Ls), todo(Record, _))) --> !,
  definition(atom(Name), conclusion(clause(Bs, Ls)), todo(Record)).
emitted(_) --> [].

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

body(app(F, Ts, Ms)) --> !, proof(app(F, Ts, Ms)).
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
proof(lam(X, _, M)) --> !, "λ ", variable(X), binders(M).
proof(let(X, F, M, N)) --> !,
  "let ", variable(X), " : ", type(F), " ; ", variable(X), " = ", proof(M), " in ", proof(N).
proof(rewrite(X:_, A, E, M)) --> !, rewritten(A, X, E, M).
% Agda infers the terms of sym and refl
proof(app(F, _, Ms)) --> { builtin(F) }, !, head(F), foldl(spaced_operand, Ms).
proof(app(F, Ts, Ms)) --> !, head(F), arguments(Ts), foldl(spaced_operand, Ms).
proof(X) --> head(X).

% consecutive λs are merged
binders(lam(X, _, M)) --> !, " ", variable(X), binders(M).
binders(M) --> " → ", proof(M).

head('$sym') --> !, "sym".
head('$refl') --> !, "refl".
head(h(N)) --> !, variable(h(N)).
head(Name) --> atom(Name).

spaced_operand(M) --> " ", operand(M).

operand(app('$refl', _, [])) --> !, "refl".
operand(app(F, [], [])) --> !, head(F).
operand(M) --> { compound(M), M \= h(_) }, !, "(", proof(M), ")".
operand(X) --> head(X).

variable(h(N)) --> !, "h", number(N).
variable('$VAR'(N)) --> "x", number(N).
variable('$BOUND'(N)) --> "y", number(N).

/********************************************************************************
 * rewriting
 ********************************************************************************/

/*
E : l ≡ r rewrites M : A[l] to A[r], where X marks l in the motive A. An equation s[l] ≡ t[l] is
rewritten by a path, a chain of trans: back along s, then M, then along t. A negated equation is
applied to the path the other way, from e : s[r] ≡ t[r]. Any other literal is rewritten by subst.

The steps of a path are e, proof(M), eq(E), sym(E) and cong(X, S, P), for P along the side S[X];
none is no step, where X does not occur in the side.
*/
rewritten('$='(_, S, T), X, E, M) --> !,
  { side(X, S, E, P), side(X, T, E, Q), inverse(P, P1) },
  path([P1, proof(M), Q]).
rewritten(~'$='(A, S, T), X, E, M) --> !,
  "λ e → ", refutation(rewrite(X:_, ~'$='(A, S, T), E, M), [e]).
rewritten(A, X, E, M) -->
  "subst (λ ", variable(X), " → ", type(A), ") ", operand(E), " ", operand(M).

% M refutes the equation of the path Ps; a rewrite of M lengthens the path instead
refutation(rewrite(X:_, ~'$='(_, S, T), E, M), Ps) --> !,
  { side(X, S, E, P), side(X, T, E, Q), inverse(Q, Q1), append([P|Ps], [Q1], Ps1) },
  refutation(M, Ps1).
refutation(M, Ps) --> operand(M), " ", { present(Ps, Qs) }, path_operand(Qs).

% the step along the side S: E itself at the top, and cong below it
side(X, S, E, eq(E)) :- S == X, !.
side(X, S, E, cong(X, S, eq(E))) :- \+ substitute(X, [], S, S), !.
side(_, _, _, none).

inverse(none, none).
inverse(eq(app('$sym', _, [E])), eq(E)) :- !.
inverse(eq(E), sym(E)).
inverse(sym(E), eq(E)).
inverse(cong(X, S, P), cong(X, S, Q)) :- inverse(P, Q).

present([], []).
present([none|Ps], Qs) :- !, present(Ps, Qs).
present([P|Ps], [P|Qs]) :- present(Ps, Qs).

path(Ps) --> { present(Ps, Qs) }, steps(Qs).

steps([P]) --> !, path_step(P).
steps([P|Ps]) --> "trans ", path_operand([P]), " ", path_operand(Ps).

path_operand([e]) --> !, "e".
path_operand([proof(M)]) --> !, operand(M).
path_operand([eq(E)]) --> !, operand(E).
path_operand(Ps) --> "(", steps(Ps), ")".

path_step(e) --> "e".
path_step(proof(M)) --> proof(M).
path_step(eq(E)) --> proof(E).
path_step(sym(E)) --> "sym ", operand(E).
path_step(cong(X, S, P)) --> "cong (λ ", variable(X), " → ", term(S), ") ", path_operand([P]).

/********************************************************************************
 * types and terms
 ********************************************************************************/

% the types of the IR: ~F is F → R, and '$false' is R
type('!'(B, F)) --> !, pi(B), type(F).
type((F => G)) --> !, domain(F), " → ", type(G).
type(~F) --> !, domain(F), " → R".
type('$false') --> !, "R".
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
symbol(F) --> { mangled }, !, dashed(F), "′".
symbol(F) --> { introduced(F, _) }, !, dashed(F).
symbol(F) --> atom(F).

% the Agda term of an input
source(S) --> { mangled }, !, dashed(S), "″".
source(S) --> atom(S).

dashed(F) --> { atom_codes(F, Cs) }, foldl(dash, Cs).

dash(0'_) --> !, "-".
dash(C) --> [C].

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
goal(_) --> "{R : Set} → R".
