# atp2itp: reconstruct once, emit many

atp2itp reads Vampire TSTP proofs, reconstructs each inference as a λ-term by backtracking search, and emits the result through one of several back ends. (`lp.pl` is the older single-pass version: it reconstructs and prints lambdapi at the same time.) Front ends, search and back ends are kept separate, so that each prover and each output format only needs its own small module:

**TSTP → front end → proof search → λ-term IR → back ends (one of which is a type checker)**

Usage: `swipl -g 'run(Backend)' -t halt src/main.pl < proof.p`, where `Backend` is `lambdapi`, `smtlib` or `checker`.

## Constraints
- **Concise, maintainable Prolog.**
- **Reasonably portable Prolog; only SWI must run.**
  - No SWI-only features: no SSU `=>`, no `format ~@`, no `sub_term/2`, no `string_*`, no `:- if`.
  - A few common non-ISO library predicates are used: `forall/2`, `msort/2`, `last/2`, `same_length/2`, `foldl/4`, `library(assoc)`. Other helpers go in `utils.pl`, under names that clash with no built-in or library predicate.
  - Output is built by DCGs over code lists, and written with `phrase/2` and `write/1`.
- **Scryer does not run yet.** Its reader rejects Vampire's SAT lines (`cnf(s1, plain, spl0_1 | spl0_2, ...)`): an unparenthesised priority-1102 term in argument position is valid TPTP but invalid ISO. That needs fixing in Vampire. Other Scryer differences to keep in mind:
  - A prefix `!` operator breaks cuts, so quantifiers are written `'!'(Bs, F)`.
  - It has no `:- if` and no `consult/1` directive.
  - `phrase/3`, and a variable DCG body, need `library(dcgs)`. `forall/2` is in `library(iso_ext)`.
  - Operator atoms must be parenthesised as operands: `C == (/)`.
  - A dynamic predicate imported into a second module is not visible there.
- **TSTP is read with `read/1`.** TPTP operators are declared only while reading (`load.pl`), so they don't affect how the code is parsed.
- **The IR is logic-agnostic and constructive.** Back ends make every encoding decision.
- **`test/` is not committed.** It holds a large generated corpus. **Tests cap memory** with `ulimit -v` and Vampire's `-m`: lambdapi can exhaust the machine on big proofs.

## Internal syntax (`ops.pl`, `load.pl`)
- Connectives `~F`, `F | G`, `F & G`, `F => G`, `F <=> G`, `'$true'`, `'$false'`. Atoms are Prolog terms, and `S = T` is equality.
- Quantifiers `'!'(Bs, F)` and `'?'(Bs, F)`, with binders `X : Sort` as in TPTP (`:` has SWI's priority). The sort is `'$i'` when TPTP gives none.
- Reading normalises `S != T` to `~(S = T)`, `F <= G` to `G => F`, `F <~> G` to `~(F <=> G)`, and `~|`, `~&` to a negated `|` or `&`.
- Clauses are `clause(Bs, Literals)`: binders as in quantifiers, and a list of literals `A` or `~A` over their variables. Vampire's AVATAR shape `(! [X] : C) | ~spl` is a clause too.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so every lookup is a fresh instance and instantiation is unification. When a step is reconstructed, its conclusion is made rigid by numbering its variables `'$VAR'(N)` in binder order, so the IR is ground.
- In search contexts, `X-T` is an entry (`X : T`); `X : Sort` is always a quantifier or clause binder.

## The IR (`ir.pl`, `db.pl`)
```
ir_step(Name, Conclusion, Justification)     % dependency order, reachable from the last $false
Conclusion    ::= clause(Bs, Lits) | formula(F)
Justification ::= input(Role, Source) | split_def(Symbol, Clause) | proof(M) | todo(Record, Parents)
M ::= h(N)                 % a hypothesis
    | app(F, Ts, Ms)       % F applied to first-order terms Ts, then to proofs Ms
    | lam(X, T, M)         % X : T is h(N) : formula, or an eigenvariable '$VAR'(N) : Sort
    | let(X, F, M, M')     % lemma X : F
    | rewrite(X, A, E, M)  % E : S = T, M : A[X:=S] give A[X:=T]
F ::= h(N) | Name | '$sym' | '$refl'
                           % '$sym' : ∀x y. x = y → y = x, '$refl' : ∀x. x = x
```
**Proofs are λ-terms**, Curry–Howard style, in minimal logic with an abstract `⊥`.
- `clause(Bs, [L₀…Lₙ₋₁])` has type `Π Bs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`), where `¬F` is `F → ⊥`.
- The hypothesis for a negative literal `~A` is `¬¬A`, so `¬¬`-elimination is never needed. The IR is therefore sound under any reading of `⊥`: classical falsity, or the conjecture of the A-translation.
- Heads are variables or constants, so terms are β-normal apart from `let`.
- **Rewriting:** in `rewrite(X, A, E, M)` the motive `A` is any formula, so a literal of either polarity can be rewritten. `X` is an eigenvariable `'$VAR'(N)` of sort `'$i'`, bound only in `A`; `E`'s type must be inferable (a hypothesis or an application), so `rewrite` is only ever checked against a type, never a head.
- First-order arguments `Ts` are untyped terms, kept apart from proof arguments, so back ends can read premise instances directly. They are built from the signature, eigenvariables, and `'$inhabited'` (below).
- **Split definitions:** a split symbol is a defined proposition that unfolds to the type of its clause. A hypothesis `H : ¬¬Split` is used as `H (λ d, d ts …)`; `H : ¬Split` is refuted by proving the definition, `H (λ xs hs, …)`, with eigenvariables `xs`.

## Reconstruction (`reconstruct.pl`, `rup.pl`, `close.pl`)
- **Search** builds terms directly from the conclusion's binders and a hypothesis `X-(~L)` for each literal, annotating every λ as it is built. A tactic's term has type `⊥` and is abstracted over the conclusion.
- **Rigidity:** conclusion variables and eigenvariables are numbered `'$VAR'(N)` *before* search, so unification cannot instantiate them. `Fresh`, the next index, is threaded to `intro`.
- **Closing** (`close.pl`) runs after search: binders are named `h(N)`, and term variables left unconstrained become `'$inhabited'`, an arbitrary individual. This assumes the sort is inhabited.
- **RUP** (`rup.pl`): propagation from the hypotheses over ground premises, as in a SAT solver without decisions. A queue holds the literals made false but not yet propagated; propagating one checks the clauses that contain it against the assignment. A unit gives a lemma `let G : ~C ≔ λ X : C. P …`, and a conflict ends the chain. Clauses are not chopped: updating them in an assoc cost about 25% of the run on SWV424-1.200.
- **Resolution** lets the minor premise refute only positive literals of the major. Both premises are tried as major, so this is complete, and it avoids an exponential search on wide, mostly negative clauses (SYO656-1 did not finish otherwise).
- **Refl** is the last way to match a premise literal: `~(S = T)` with `S`, `T` unifiable is refuted by `λk. k (refl S)`. So `variant` also covers equality resolution, trivial inequality removal and (by symmetry) reorienting equations. This might blow up on wide clauses with many disequations; on the corpus it did not.
- **Paramodulation** is like resolution: each literal `K` of the `Into` premise is matched, or rewritten as `λy : K. From …`, where one positive equation `A = B` of (an instance of) `From` is refuted by `λe : A = B. Body`, and the other literals of `From` are matched. **Equality factoring** is the same, but the equation comes from a hypothesis for a conclusion literal `A ≠ B`. In `Body`, `y` is rewritten by `e` (or `sym e`) to a hypothesis's literal or its flip, by a parallel walk of the two literals that chooses rewrite sites by unification: any set of occurrences, as Vampire rewrites all of them, even inside instantiated variables. A flipped hypothesis refutes by a λ, whose β-redex is written as a `let`, so that heads stay variables or constants. All rewrites in a step share the motive variable `'$VAR'(Fresh)`.
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

## Back ends
**checker** (`checker.pl`): an independent type checker of each ground, annotated term against the ground type of its conclusion, step by step.
- It only binds the quantifier binders of fresh instances of steps, split definitions and `'$sym'`: to ground terms `Ts`, or to eigenvariables under the λs of an unfolded split definition.
- First-order terms must be in scope, and a step can only cite steps checked before it.
- Types are compared syntactically, not up to unfolding. Instantiation is by unification, so it needs fresh instances: a hypothesis of quantified type would need substitution.
- A term that fails to check is a search bug: the step is reported and the run fails. Other back ends do not run the checker.

**lambdapi** (`lambdapi.pl`), using the Stdlib encoding of first-order logic:
- A clause is stated as its IR type with framework-level `Π`/`→`; for `~A` that is `π (¬ ¬ A)`. Proof terms are printed directly, with `'$sym'` and `'$refl'` as prelude symbols `sym` and `refl`, and `rewrite(X, A, E, M)` as `rw (λ (x : τ ι), A) E M` (`rewrite` is a lambdapi keyword), where `rw` is defined by `ind_eq`.
- A `let` carries its type, and so does the binder of a λ value: lambdapi does not use a let's type to elaborate its value, and without the annotation PUZ017-1 went from 2 s to over 60 s.
- Inputs are declared as `{|name²|}` with their original formula, and their clause is obtained by an `∨ₑ` chain. A split symbol is a `Prop` with `rule spl ↪ clause`.
- Symbols are `{|f¹|}`, or `{|f/2¹|}` for a name overloaded by arity (TPTP allows it, and Vampire prints both as `f`). Formulas are parenthesised only where the Stdlib priorities need it.

**SMT-LIB** (`smtlib.pl`), in the manner of "Ground Truth": one `push`/`check-sat`/`pop` per step, expecting `unsat`.
- Each `check-sat` is preceded by `(set-info :status unsat)`, so any other result fails loudly: z3 reports an error and exits 1 after the remaining steps, and cvc5 aborts at once.
- A step asserts the ground premise instances `app(Name, Ts, _)` of its proof term and its negated conclusion. Rewrites need no facts: equality reasoning is left to the solver.
- Variables are Skolem constants, read from the λ binders with their sorts: the conclusion's variables, and the eigenvariables of split definitions proved in the term.
- AVATAR definitions are ground implications: `spl ⇒ Cσ` where a definition is used, and `C[eigen] ⇒ spl` where one is proved. The latter is sound by Skolemisation only because eigenvariables are fresh, which this back end does not check.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted. `todo` steps are checked with universally quantified premises.

## Files (`src/`)
| File | Role |
|---|---|
| `main.pl` | `run(Backend)` |
| `ops.pl` | Operators of the internal syntax |
| `load.pl` | `read_tstp/1`: `read/1` with TPTP operators, then normalisation |
| `db.pl` | Shared dynamic facts: `step/3`, `symbol/3`, `introduced/2`, `ir_step/3`, `split/2` |
| `logic.pl` | Formulas and clauses: `formula_clause`, `clause_formula`, `binder_variables`, `complement`, `flip`, `number_vars`, `substitute`, `formula_symbol` |
| `vampire.pl` | Vampire front end: rule table, inputs and AVATAR definitions; unknown rules become `todo` |
| `signature.pl` | Default sorts for undeclared symbols, for any front end; `overloaded/1` |
| `reconstruct.pl` | Proof search and the tactics |
| `rup.pl` | Reverse unit propagation |
| `close.pl` | Closing terms after search |
| `ir.pl` | IR documentation; `clause_type/2` |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl`, `smtlib.pl` | Back ends |
| `printing.pl` | Shared printing: `out/1` and the `atom`, `number`, `codes` DCGs |
| `utils.pl` | Portable helpers (`range/3`) |

## Testing and known issues
- `'$sym'` was first tested on hand-made proofs of both polarities, through lambdapi and z3. Mutating proof terms (dropped or swapped arguments, wrong `'$sym'` order, wrong lemma type or binder annotation) was always caught by the checker: over 23000 mutants for SYN488-1.
- The CNF corpus (3740 proofs) has equality throughout: about 59000 rewrites, of which 17000 are into a flipped hypothesis (a `let`). Every step is reconstructed and checks, with no `todo` left; definition unfolding adds another 29000 rewrites. Mutants of rewrites (wrong direction, no hole, wrong motive variable, rewrite dropped) and of `refl`/`sym` arguments were all caught.
- **lambdapi scaling:** checking cost grows roughly as n⁴ in the number of hypotheses of one declaration, even with every binder typed: n = 150 takes 30–50 s. The largest proofs (lambdapi output 4–245 MB, such as HWV057 and SWV424-1.200 and up) time out or run out of memory. lambdapi's `let` was much worse than β-redexes, and a `cut` lemma worse still.
- Literal matching is naive, in a fixed literal order.

To test: produce a corpus of TSTP proofs in `solutions/` if not already.
Then use `gen*` scripts to produce transformed proofs (or just check the corpus with `check`).
Finally, use `check*` to check the resulting proofs.
All should produce noisy output on failure and play well with GNU parallel.
