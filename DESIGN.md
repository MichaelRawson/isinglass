# atp2itp: reconstruct once, emit many

atp2itp reads Vampire TSTP proofs (CNF, FOF, and TFF with rank-1 polymorphism, TF1), reconstructs each inference as a λ-term by backtracking search, and emits the result through one of several back ends. (`lp.pl` is the older single-pass version: it reconstructs and prints lambdapi at the same time.) Front ends, search and back ends are kept separate, so that each prover and each output format only needs its own small module:

**TSTP → front end → proof search → λ-term IR → back ends (one of which is a type checker)**

Usage: `swipl -g 'run(Backend)' -t halt src/main.pl < proof.p`, where `Backend` is `lambdapi`, `smtlib` or `checker`.

## Constraints
- **Concise, maintainable Prolog.**
- **Reasonably portable Prolog; only SWI must run.**
  - No SWI-only features: no SSU `=>`, no `format ~@`, no `sub_term/2`, no `string_*`, no `:- if`.
  - A few common non-ISO library predicates are used: `forall/2`, `msort/2`, `last/2`, `same_length/2`, `foldl/4`, `library(assoc)`. Other helpers go in `utils.pl`, under names that clash with no built-in or library predicate.
  - Output is built by DCGs over code lists, and written with `phrase/2` and `write/1`.
- **Scryer has not been tried yet.** Its reader rejected Vampire's old SAT lines (`cnf(s1, plain, spl0_1 | spl0_2, ...)`): an unparenthesised priority-1102 term in argument position is valid TPTP but invalid ISO. Vampire now parenthesises them (from commit 7c404dbd8), but most of the corpus predates that. Other Scryer differences to keep in mind:
  - A prefix `!` operator breaks cuts, so quantifiers are written `'!'(Bs, F)`.
  - It has no `:- if` and no `consult/1` directive.
  - `phrase/3`, and a variable DCG body, need `library(dcgs)`. `forall/2` is in `library(iso_ext)`.
  - Operator atoms must be parenthesised as operands: `C == (/)`.
  - A dynamic predicate imported into a second module is not visible there.
- **TSTP is read with `read/1`.** TPTP operators are declared only while reading (`load.pl`), so they don't affect how the code is parsed. Prolog's own word prefix operators (`table`, `dynamic`, …) are removed then, as they may be TPTP symbols (PUZ159_1 declares `table : $tType`).
- **The IR is logic-agnostic and constructive.** Back ends make every encoding decision.
- **`test/` is not committed.** It holds a large generated corpus. **Tests cap memory** with `ulimit -v` and Vampire's `-m`: lambdapi can exhaust the machine on big proofs.

## Internal syntax (`ops.pl`, `load.pl`, `signature.pl`)
- Connectives `~F`, `F | G`, `F & G`, `F => G`, `F <=> G`, `'$true'`, `'$false'`. Atoms are Prolog terms. `$`-words, read as the prefix operator `$` applied to a term, become symbols named with a `$`.
- **Equality is typed**: `'$='(A, S, T)`, where `A` is the sort of `S` and `T`. TPTP's `=` is implicitly polymorphic, so the front end gives each equation its sort once, at load time (`signature:typed/3`). Search instantiates by unification, so the sort comes along wherever a literal is matched: `'$sym'` and `'$refl'` get their type argument from it, and so does the motive of a rewrite. It also binds premise type variables that occur only under an equality.
- Quantifiers `'!'(Bs, F)` and `'?'(Bs, F)`, with binders `X : Sort` as in TPTP (`:` has SWI's priority). The sort is `'$i'` when TPTP gives none.
- **Types are terms of the pseudo-sort `'$tType'`, as in TF1**, and sorts are terms: `'$i'`, `'$o'`, type variables, and declared types such as `list('$i')`. A type variable is a binder `X : '$tType'`, in quantifiers and clauses alike; Vampire lists them first, and the sorts of later binders may depend on them. A polymorphic symbol takes its type arguments explicitly, first: `f(Types…, Terms…)`.
- The signature is `symbol(Name, Params, Args, Sort)` (`db.pl`), with `Params` the Prolog variables that the type arguments instantiate, so every lookup is a fresh instance: `list : $tType > $tType` is `symbol(list, [], ['$tType'], '$tType')`, and a Skolem type `sK9 : $tType` is `symbol(sK9, [], [], '$tType')`. Built-in symbols (`'$='`, `'$i'`, `'$o'`, `'$inhabited'`) are not in the database; `signature:instance/5` covers both. Type declarations are loaded first, and untyped symbols get the default sorts.
- Reading normalises `S != T` to `~(S = T)`, `F <= G` to `G => F`, `F <~> G` to `~(F <=> G)`, and `~|`, `~&` to a negated `|` or `&`.
- Clauses are `clause(Bs, Literals)`: binders as in quantifiers, and a list of literals `A` or `~A` over their variables. Vampire's AVATAR shape `(! [X] : C) | ~spl` is a clause too.
- Vampire prints clauses as `fof` too, so shape alone cannot tell a clause from a formula. `$false` is the empty clause. Otherwise a statement is a clause if it is clause-shaped and is either `cnf`, an input, or derived by clausal reasoning: `cnf_transformation`, a rule in the table below, or an unknown rule from clauses only. The conjecture, its negation, preprocessing and definitions are formulas.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so every lookup is a fresh instance and instantiation is unification. When a step is reconstructed, its conclusion is made rigid by numbering its variables `'$VAR'(N)` in binder order, so the IR is ground.
- In search contexts, `X-T` is an entry (`X : T`); `X : Sort` is always a quantifier or clause binder.

## The IR (`ir.pl`, `db.pl`)
```
ir_step(Name, Conclusion, Justification)     % dependency order, reachable from the last $false
Conclusion    ::= clause(Bs, Lits) | formula(F)
Justification ::= input(Role, Source)      % never the conjecture
                | split_def(Symbol, Clause) | proof(M)
                | negated_conjecture(Conjecture)
                                           % the hypothesis ~G, discharged by Conjecture
                | conjecture(Source, Negated, Refutation)
                                           % G by contradiction: the last step, if there is a conjecture
                | todo(Record, Parents)    % Record is a Rule (an entailment), or esa(Rule, Symbols):
                                           % satisfiability only, introducing Symbols
M ::= h(N)                 % a hypothesis
    | app(F, Ts, Ms)       % F applied to first-order terms Ts, then to proofs Ms
    | lam(X, T, M)         % X : T is h(N) : formula, or an eigenvariable '$VAR'(N) : Sort
    | let(X, F, M, M')     % lemma X : F
    | rewrite(X:S, A, E, M) % E : S = T, M : A[X:=S] give A[X:=T]
F ::= h(N) | Name | '$sym' | '$refl'
                           % '$sym' : ∀a:$tType. ∀x y:a. x = y → y = x, '$refl' : ∀a:$tType. ∀x:a. x = x
```
**Proofs are λ-terms**, Curry–Howard style, in minimal logic with an abstract `⊥`.
- `clause(Bs, [L₀…Lₙ₋₁])` has type `Π Bs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`), where `¬F` is `F → ⊥`.
- The hypothesis for a negative literal `~A` is `¬¬A`, so `¬¬`-elimination is never needed. The IR is therefore sound under any reading of `⊥`: classical falsity, or the conjecture of the A-translation.
- Heads are variables or constants, so terms are β-normal apart from `let`.
- **Rewriting:** in `rewrite(X:S, A, E, M)` the motive `A` is any formula, so a literal of either polarity can be rewritten. `X` is an eigenvariable `'$VAR'(N)` of sort `S`, the sort of `E`'s equation, bound only in `A`; `E`'s type must be inferable (a hypothesis or an application), so `rewrite` is only ever checked against a type, never a head.
- First-order arguments `Ts` are terms, kept apart from proof arguments, so back ends can read premise instances directly. They are built from the signature, eigenvariables, and `'$inhabited'(S)` (below). Type arguments are among them, as in TF1.
- **Split definitions:** a split symbol is a defined proposition that unfolds to the type of its clause. A hypothesis `H : ¬¬Split` is used as `H (λ d, d ts …)`; `H : ¬Split` is refuted by proving the definition, `H (λ xs hs, …)`, with eigenvariables `xs`.

## Formulas and the conjecture
FOF proofs are clausified by Vampire: preprocessing (`ennf`/`nnf_transformation`, `flattening`, `rectify`, `skolemize`, `pure_predicate_removal`, `definition_folding`, …), then `cnf_transformation`. These intra-formula steps are left as `todo` for now. The clausal part is reconstructed as before. The design keeps a later **A-translation** (a constructive Agda back end, with ⊥ := G) open:
1. **Proof terms stay in minimal logic with an abstract ⊥.** No DNE or excluded middle ever appears in the IR.
2. **Classical reasoning is confined to two places:** the `conjecture` step, and unreconstructed clausification (`todo`).
3. **The negated conjecture is a hypothesis, never an axiom.** Its type is `G → ⊥`, where ⊥ is the refutation's answer type, and only the `conjecture` step discharges it. A classical back end proves `G` by `¬¬ₑ G (λ nc, refutation nc)`. An A-translation takes ⊥ := G and nc := `id`, so the theorem is `refutation id`. In Agda that falls out of a module parameterised by `(⊥ : Set) (nc : G → ⊥)`.
4. **Which ⊥ is which follows from structure, so formulas carry no tags.** In clause types every `¬` is the answer ⊥, including the one in a literal `~A`. In `formula(F)` conclusions `¬` is object falsity, except the outermost `¬` of the negated conjecture. Steps that depend on it mix the two. Getting from object falsity to the answer ⊥ (ex falso) is clausification's job, and back ends can compute that cone with `ir:references/2`.
5. **Clause-shaped inputs are clauses**, as for CNF problems. Their clause type follows from the input formula by case analysis, for any ⊥.

Steps that only preserve satisfiability are `todo(esa(Rule, Symbols), Parents)`: Vampire's `status(esa)` (Skolemisation), and predicate definitions. `definition_folding` is `esa` too. Vampire's predicate definitions are one-sided (Plaisted–Greenbaum): `body | ~sP` gives only `sP → body`. Folding `body | rest` into `sP | rest` needs `body → sP`, so the conclusion does not follow from the printed premises (z3 finds models). It is satisfiable, though, because `sP` is fresh. A better treatment, for later: make `sP := body` a real definition, as split symbols are. Folding then holds by unfolding, constructively, with nothing postulated. That needs the body recovered from the one-sided formula, possibly under `! [X..]`. A proof with more than one conjecture is an error. If the conjecture is unused, Vampire does not print it, and the IR ends at `$false`.

## Reconstruction (`reconstruct.pl`, `rup.pl`, `close.pl`)
- **Search** builds terms directly from the conclusion's binders and a hypothesis `X-(~L)` for each literal, annotating every λ as it is built. A tactic's term has type `⊥` and is abstracted over the conclusion.
- **Rigidity:** conclusion variables and eigenvariables are numbered `'$VAR'(N)` *before* search, so unification cannot instantiate them. `Fresh`, the next index, is threaded to `intro`.
- **Closing** (`close.pl`) runs after search: binders are named `h(N)`, and term variables left unconstrained become `'$inhabited'(S)`, an arbitrary individual of their sort `S`. Every variable comes from the binders of some instance `app(F, Ts, _)` (a step, a split definition or a built-in), so its sort is that of its binder. Unconstrained type variables are closed first, as `'$inhabited'('$tType')`, an arbitrary type, so that the other sorts are then ground. This assumes every sort is inhabited, as TF1 does.
- **RUP** (`rup.pl`): propagation from the hypotheses over ground premises, as in a SAT solver without decisions. A queue holds the literals made false but not yet propagated; propagating one checks the clauses that contain it against the assignment. A unit gives a lemma `let G : ~C ≔ λ X : C. P …`, and a conflict ends the chain. Clauses are not chopped: updating them in an assoc cost about 25% of the run on SWV424-1.200.
- **Resolution** lets the minor premise refute only positive literals of the major. Both premises are tried as major, so this is complete, and it avoids an exponential search on wide, mostly negative clauses (SYO656-1 did not finish otherwise).
- **Refl** is the last way to match a premise literal: `~(S = T)` with `S`, `T` unifiable is refuted by `λk. k (refl S)`. So `variant` also covers equality resolution, trivial inequality removal and (by symmetry) reorienting equations. This might blow up on wide clauses with many disequations; on the corpus it did not.
- **Paramodulation** is like resolution: each literal `K` of the `Into` premise is matched, or rewritten as `λy : K. From …`, where one positive equation `A = B` of (an instance of) `From` is refuted by `λe : A = B. Body`, and the other literals of `From` are matched. **Equality factoring** is the same, but the equation comes from a hypothesis for a conclusion literal `A ≠ B`. In `Body`, `y` is rewritten by `e` (or `sym e`) to a hypothesis's literal or its flip, by a parallel walk of the two literals that chooses rewrite sites by unification: any set of occurrences, as Vampire rewrites all of them, even inside instantiated variables. A flipped hypothesis refutes by a λ, whose β-redex is written as a `let`, so that heads stay variables or constants. All rewrites in a step share the motive variable `'$VAR'(Fresh)`. **Rewrites respect sorts:** the walk knows the sort of each argument position from the signature, and rewrites only where it unifies with the equation's sort. Literal matching is sort-safe by itself, as type arguments are explicit, but a rewrite site is any subterm: with a variable side, as in SCT239_5's `! [X0, X1 : t] : X0 = X1`, an equation would otherwise unify with a subterm of another sort (there, a list). Type arguments are never rewritten, nor unfolded.
- **Definition unfolding** replaces every occurrence of each defined symbol: the first parent is the clause, and the others are unit definitions `f(X₁…Xₙ) = body`, either way round, listed once per occurrence. Each definition is oriented by a side `f(distinct variables)`, by backtracking if both sides are. Each literal is then unfolded deterministically, innermost first, so an instance's arguments are already unfolded, and each occurrence is one `rewrite`. Its motive is the literal around the occurrence, rebuilt from a zipper of frames rather than by `copy_term`, which would rename the clause's variables. The unfolded literal is refuted by a hypothesis, as in paramodulation. Each distinct definition instance is opened once, outside the clause application, so that every literal can use it.
- A failed tactic leaves the step as `todo`, with a warning.

Vampire rule → search procedure (`vampire.pl`):
| Vampire rules | Procedure |
|---|---|
| resolution, forward/backward_subsumption_resolution | `resolve` |
| factoring, duplicate_literal_removal, sat_conversion, avatar_contradiction_clause, avatar_sat_refutation, reorient_equations, trivial_inequality_removal, equality_resolution | `variant` |
| superposition, forward/backward_demodulation | `paramodulate` |
| equality_factoring | `equality_factor` |
| definition_unfolding | `unfold` |
| avatar_split_clause | `avatar_split` |
| avatar_component_clause | `avatar_component` |
| rat | `rup` |

The conjecture becomes `conjecture`, `negated_conjecture` becomes `negated_conjecture`, `status(esa)` and `definition_folding` become `todo(esa(…))`, and any other rule becomes `todo`.

## Back ends
**checker** (`checker.pl`): an independent type checker of each ground, annotated term against the ground type of its conclusion, step by step.
- It only binds the quantifier binders of fresh instances of steps, split definitions and `'$sym'`: to ground terms `Ts`, or to eigenvariables under the λs of an unfolded split definition.
- **First-order terms are checked against the signature**: each instance term is of its binder's sort (binder by binder, as sorts depend on earlier type arguments), and in scope; the sort of each eigenvariable is well formed, and each rewrite motive is well sorted, with `X : S`. The types of steps are taken to be well sorted, as the prover gives them. A step can only cite steps checked before it.
- The `conjecture` step `G` must cite a checked refutation of `$false`, and a checked `negated_conjecture` step `~G`.
- Types are compared syntactically, not up to unfolding. Instantiation is by unification, so it needs fresh instances: a hypothesis of quantified type would need substitution.
- A term that fails to check is a search bug: the step is reported and the run fails. Other back ends do not run the checker.

**lambdapi** (`lambdapi.pl`), using the Stdlib encoding of first-order logic:
- A clause is stated as its IR type with framework-level `Π`/`→`; for `~A` that is `π (¬ ¬ A)`. Proof terms are printed directly, with `'$sym'` and `'$refl'` as prelude symbols `sym` and `refl` (whose type argument is explicit, `sym a x y e`), and `rewrite(X:S, A, E, M)` as `rw (λ (x : τ S), A) E M` (`rewrite` is a lambdapi keyword), where `rw` is defined by `ind_eq`.
- **Sorts** are terms of `Set` (`Stdlib.Set`): `'$i'` is `ι`, a type constructor is declared `Set → Set`, a polymorphic symbol `Π (x0 : Set), τ x0 → …`, and a term of sort `S` has type `τ S`. `'$inhabited'(S)` is `el S`.
- **Type quantifiers:** the Stdlib's `` `∀ `` ranges over the elements of a `Set`, not over `Set`, so the prelude adds a binder `∀ₜ : (Set → Prop) → Prop`, with `π (∀ₜ p) ↪ Π a : Set, π (p a)`: the usual Dedukti encoding of prenex polymorphism, sound when `Set` is read as a family of non-empty sets and `∀ₜ` as their meet (`Stdlib.Impred`, where `∀ₜ` would range over `Prop` too, is not imported). A type-quantified formula is then an ordinary `Prop`, so inputs, the negated conjecture and split definitions need nothing special. `∃ₜ` has no rule: it only occurs in unreconstructed steps (the NNF of a type-quantified conjecture's negation). For an Agda back end, quantifying over `Set` lands in `Set₁`, so the A-translation's ⊥ := G must be large there.
- A `let` carries its type, and so does the binder of a λ value: lambdapi does not use a let's type to elaborate its value, and without the annotation PUZ017-1 went from 2 s to over 60 s.
- Inputs are declared as `{|name²|}` with their original formula, and their clause is obtained by an `∨ₑ` chain (a formula input is just the constant). A split symbol is a `Prop` with `rule spl ↪ clause`.
- **The negated conjecture** `nc` is not declared. Each step in its cone takes it as a parameter, `Π (nc : π (¬ G))`, and refers to a cone step as `(f nc)`. The conjecture is `¬¬ₑ G (λ nc, refutation nc)`, the only use of `Stdlib.Classic`, which is required only when there is a conjecture.
- Symbols are `{|f¹|}`, or `{|f/2¹|}` for a name overloaded by arity (TPTP allows it, and Vampire prints both as `f`). Formulas are parenthesised only where the Stdlib priorities need it.

**SMT-LIB** (`smtlib.pl`), in the manner of "Ground Truth": one `push`/`check-sat`/`pop` per step, expecting `unsat`.
- Each `check-sat` is preceded by `(set-info :status unsat)`, so any other result fails loudly: z3 reports an error and exits 1 after the remaining steps, and cvc5 aborts at once.
- A step asserts the ground premise instances `app(Name, Ts, _)` of its proof term and its negated conclusion. Rewrites need no facts: equality reasoning is left to the solver.
- Variables are Skolem constants, read from the λ binders with their sorts: the conclusion's variables, and the eigenvariables of split definitions proved in the term. Type variables are Skolem sorts, `(declare-sort x0 0)`, declared first.
- **Types are sorts**, declared with their arity (`(declare-sort |t.list| 1)`), but **polymorphic symbols are monomorphised**: each instance used in a check is declared in its scope, as `|t.f[int,list(int)]|`, and so is each `'$inhabited'(S)`. Checks are ground, so this is easy. SMT-LIB 2.7's `declare-sort-parameter` would map the signature directly, but z3 4.13.3 rejects it and cvc5 1.4.2 says "Sort parameters not supported in this version".
- AVATAR definitions are ground implications: `spl ⇒ Cσ` where a definition is used, and `C[eigen] ⇒ spl` where one is proved. The latter is sound by Skolemisation only because eigenvariables are fresh, which this back end does not check.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted. `todo` steps are not checked: the solver echoes `warning: name (rule) is not checked` instead. Checking them with quantified premises often timed out on preprocessing. The negated conjecture and the conjecture are not checked either.

## Files (`src/`)
| File | Role |
|---|---|
| `main.pl` | `run(Backend)` |
| `ops.pl` | Operators of the internal syntax |
| `load.pl` | `read_tstp/1`: `read/1` with TPTP operators, then normalisation |
| `db.pl` | Shared dynamic facts: `step/3`, `symbol/3`, `introduced/2`, `ir_step/3`, `split/2` |
| `logic.pl` | Formulas and clauses: `formula_clause`, `clause_formula`, `binder_variables`, `complement`, `flip`, `number_vars`, `substitute`, `formula_symbol` |
| `vampire.pl` | Vampire front end: clause or formula, rule table, inputs, the conjecture and AVATAR definitions; unknown rules become `todo` |
| `signature.pl` | The signature: symbol instances and term sorts, typing equations, default sorts for undeclared symbols (any front end); `overloaded/1` |
| `reconstruct.pl` | Proof search and the tactics |
| `rup.pl` | Reverse unit propagation |
| `close.pl` | Closing terms after search |
| `ir.pl` | IR documentation; `clause_type/2`, `references/2` |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl`, `smtlib.pl` | Back ends |
| `printing.pl` | Shared printing: `out/1` and the `atom`, `number`, `codes` DCGs |
| `utils.pl` | Portable helpers (`range/3`) |

## Testing and known issues
- `'$sym'` was first tested on hand-made proofs of both polarities, through lambdapi and z3. Mutating proof terms (dropped or swapped arguments, wrong `'$sym'` order, wrong lemma type or binder annotation) was always caught by the checker: over 23000 mutants for SYN488-1.
- The CNF corpus (3740 proofs) has equality throughout: about 59000 rewrites, of which 17000 are into a flipped hypothesis (a `let`). Every step is reconstructed and checks, with no `todo` left; definition unfolding adds another 29000 rewrites. Mutants of rewrites (wrong direction, no hole, wrong motive variable, rewrite dropped) and of `refl`/`sym` arguments were all caught.
- **lambdapi scaling:** checking cost grows roughly as n⁴ in the number of hypotheses of one declaration, even with every binder typed: n = 150 takes 30–50 s. The largest proofs (lambdapi output 4–245 MB, such as HWV057 and SWV424-1.200 and up) time out or run out of memory. lambdapi's `let` was much worse than β-redexes, and a `cut` lemma worse still.
- The FOF corpus (3486 proofs): every clausal step reconstructs and checks, with no warnings. One fails in `read/1`: SYN986+1.004 exceeds the default C stack with its deep `succ` terms, and checks with `ulimit -s unlimited`. Vampire used to print `~$true`, which tokenises as the symbol `~$`; it now prints `~ $true`, and the four such proofs (the conjecture `$true`) were regenerated. Mutants of the negated conjecture, of a cone argument and of its type were caught.
- The TFF corpus (388 proofs, 204 of them TF1): every clausal step reconstructs and checks, with sorts, and no warnings. Their lambdapi checks within 10 s, and so does SMT-LIB with cvc5, but for PUZ135_1, whose self-superposition of a 7-literal equational clause takes 13 s to reconstruct (about 20% of it sort bookkeeping in the rewriting walk). Four proofs (ITP006/010/015/018_3) have type-quantified conjectures. Of 40 TF1 proofs, all checked unmutated, and 14782 mutants of 36 (a type or term argument of the wrong sort or out of scope, another type, a wrong rewrite sort) were all caught.
- cvc5 exits 0 on `unknown` (`:status unsat` only catches `sat`), so `checksmt` would not notice one. `distinctness_axiom` and `introduced(theory, …)` steps are not entailments, and are not yet marked `esa`.
- Literal matching is naive, in a fixed literal order.

To test: produce a corpus of TSTP proofs in `solutions/` if not already.
Then use `gen*` scripts to produce transformed proofs (or just check the corpus with `check`).
Finally, use `check*` to check the resulting proofs.
All should produce noisy output on failure and play well with GNU parallel.
