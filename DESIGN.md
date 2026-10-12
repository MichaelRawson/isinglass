# Design

`atp2itp` reads Vampire (and in future other ATPs') TSTP proofs (CNF, FOF, or TFF), reconstructs each inference as an intermediate representation, and emits the result through one of several back ends.
Frontends, reconstruction and backends are kept separate, so that each prover and each output format can be treated separately.
Reconstruction is done by backtracking _search_ over the space of possible instances of an inference like, say, "binary resolution".

Overall: TSTP → frontend (e.g. 'Vampire') → ATP-agnostic proof → reconstruction → IR → backend (e.g. 'lambdapi')

Usage: `swipl -g 'main(Backend)' src/main.pl < proof.p`, where `Backend` is `lambdapi`, `smtlib` or `checker`. Scryer or Trealla have also been tested at some point.

## Design Decisions
- Concise, reasonably-portable Prolog.
- TSTP is read with `read/1`. TPTP operators are declared only while reading (`load.pl`), so they don't affect how the code is parsed.
- Agnostic to ATP system, in principle
- IR attempts to be logic-agnostic and constructive. Backends make every encoding decision.

## Internal Language (`ops.pl`, `load.pl`, `signature.pl`)
- Rank-1 polymorphic first-order logic. Variables, terms and atoms are Prolog variables, terms.
- Connectives `~F`, `F | G`, `F & G`, `F => G`, `F <=> G`, `'$true'`, `'$false'`.
- Equality is typed: `'$='(A, S, T)`, where `A` is the sort of `S` and `T`. TPTP's `=` is implicitly polymorphic, so the front end gives each equation its sort once, at load time (`signature:typed/3`).
- Quantifiers `'!'(Bs, F)` and `'?'(Bs, F)`, with binders `X : Sort` as in TPTP.
- Sorts are terms: e.g. `'$i'`, `'$o'`, type variables, and declared type constructors such as `list(A)`. The sort of sorts is `$tType` as in TFF1.
- Sorts `A` are assumed inhabited with the polymorphic symbol `$inhabited(A)`. The implementation tries to avoid using this for the sake of constructive backends.
- The signature is `symbol(Name, Params, Args, Sort)` (`db.pl`), with `Params` the sort variables, `Args` the domain and `Sort` the range.
- Reading normalises `S != T` to `~ (S = T)`, `F <= G` to `G => F`, `F <~> G` to `~(F <=> G)`, and `~|`, `~&` to a negated `|` or `&`. At some point this should perhaps be reported verbatim and subsequently normalised.
- Clauses are `clause(Bs, Literals)`: binders as in quantifiers, and a list of literals `A` or `~A` over their variables. Vampire's AVATAR shape `(! [X] : C) | ~spl` is a clause too.
- Vampire prints clauses as `fof` too, so shape alone cannot tell a clause from a formula. `$false` is the empty clause. Otherwise a statement is a clause if it is clause-shaped and is either `cnf`, an input, or derived by clausal reasoning: `cnf_transformation`, a rule in the table below, or an unknown rule from clauses only. The conjecture, its negation, preprocessing and definitions are formulas.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so every lookup is a fresh instance and instantiation is unification. When a step is reconstructed, its conclusion is made rigid by numbering its variables `'$VAR'(N)` in binder order, so the IR is ground.
- In search contexts, `X-T` is an entry (`X : T`); `X : Sort` is always a quantifier or clause binder.

## IR (`ir.pl`, `db.pl`)
- Proofs are λ-terms, Curry–Howard style, in minimal logic with an abstract `⊥`.
- This does not necessarily exclude non-Curry-Howard systems, e.g. the SMT-LIB backend just looks for groundings in the proof term.
- First-order arguments `Ts` are terms, kept apart from proof arguments (so that back ends can read premise instances directly).
- `clause(Bs, [L₀…Lₙ₋₁])` has type `Π Bs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`), where `¬F` is `F → ⊥`.
- Clause-shaped `fof`/`tff` inputs are clauses, as for CNF problems.
- The hypothesis for a negative literal `~A` is `¬¬A`, so `¬¬`-elimination is never needed. The IR is therefore sound under any reading of `⊥`: classical falsity, or the conjecture of the A-translation.
- Heads are variables or constants, so terms are β-normal apart from `let`.
- Rewriting: in `rewrite(X:S, A, E, M)` the motive `A` is any formula context `A[X]` so that `E : S = T` rewrites `M : A[S]`, producing `A[T]`.
- Clause splits: a split symbol is a defined proposition that unfolds to the type of its clause.
- A hypothesis `H : ¬¬Split` is used as `H (λ d, d ts …)`; `H : ¬Split` is refuted by proving the definition, `H (λ xs hs, …)`, with eigenvariables `xs`.

## Classical Logic and Conjectures
The IR does not pre-suppose classical logic, and large chunks of ATP proofs are intuitionistically valid, which may be surprising.
Future constructive backends may use an A-translation to produce a constructive proof (!).

- Proof terms stay in minimal logic with an abstract ⊥. No DNE or excluded middle appears in the IR.
- Proof by refutation (negate conjecture, derive falsum) and clausification are the main exceptions.
- The negated conjecture is a parameter, not an axiom. Its type is `G → ⊥`, and only the `conjecture` step discharges it.
- A classical back end proves `G` by double-negation elimination.
- An A-translation takes `⊥ := G` and the negated conjecture `nc := id`, so the theorem is `refutation id`.
- If a conjecture does not appear in the proof (whether or not there one was given) the IR ends at `$false`.

## Reconstruction (`reconstruct.pl`, `rup.pl`, `close.pl`)
Reconstruction tries to build an IR term with the conclusion's type given that the step is e.g. "resolution".
each 

- Conclusion variables and eigenvariables are numbered `'$VAR'(N)` _before_ search, so unification cannot instantiate them.
- Closing (`close.pl`) runs after search: binders are named `h(N)`, and term variables left unconstrained become `'$inhabited'(S)`, an arbitrary individual of their sort `S`.
- RUP (`rup.pl`): ground reverse unit propagation as in a SAT solver, split out into a separate module.
- Many rules are simply variants of a parent, up to instantiation, factoring, reflexivity, literal re-ordering, and symmetry of equality.
- Resolution finds the pivot literal and then matches remaining literals in the same way.
- Paramodulation is similar: each literal is matched to a premise, or rewritten using one positive equation `A = B` from a premise.
- Equality factoring is the same, but the equation comes from a hypothesis for a conclusion literal `A != B`
- Rewrites respect sorts: the walk knows the sort of each argument position from the signature, and rewrites only where it unifies with the equation's sort.
- Definition unfolding replaces every occurrence of each defined symbol. Each definition is oriented which side is a pattern, backtracking if both are. Each literal is unfolded deterministically, innermost first. Its context is the literal around the occurrence, rebuilt from a zipper of frames.
- A failed tactic leaves the step as `todo`, with a warning.

## Frontends
The job of a frontend is to load the proof of a given system in its own idiom, then match its inference rules to the existing ATP-generic 'tactics' that we know how to reconstruct.

### Vampire (`vampire.pl`)
| Vampire rules | Tactic |
|---|---|
| resolution, forward/backward_subsumption_resolution | `resolve` |
| factoring, duplicate_literal_removal, sat_conversion, avatar_contradiction_clause, avatar_sat_refutation, reorient_equations, trivial_inequality_removal, equality_resolution | `variant` |
| superposition, forward/backward_demodulation | `paramodulate` |
| equality_factoring | `equality_factor` |
| definition_unfolding | `unfold` |
| avatar_split_clause | `avatar_split` |
| avatar_component_clause | `avatar_component` |
| rat | `rup` |

The conjecture becomes `conjecture`, `negated_conjecture` becomes `negated_conjecture`, and any other rule becomes `todo`.
Steps that preserve only satisfiability are not yet handled.

## Backends

### Checker (`checker.pl`)
An independent-ish type checker of each ground, annotated term against the type of its conclusion.
- First-order terms are checked against the signature.
- The sort of each eigenvariable is well formed.
- The `conjecture` step `G` must cite a refutation of `$false`, and a checked `negated_conjecture` step `~G`.
- A term that fails to check is a reconstruction bug: the step is reported and the run fails.
- Other back ends do not run the checker.

### Lambdapi (`lambdapi.pl`)
Uses the `Stdlib` encoding of first-order logic.:
- Input symbols are printed `{|f¹|}`, or `{|f/n¹|}` for a name overloaded by arity.
- Inputs are declared as `{|name²|}` with their original formula.
- A clause is stated as its IR type with framework-level `Π`/`→`; for `~A` that is `π (¬ ¬ A)`.
- Proof terms are printed directly, with `'$sym'` and `'$refl'` as our symbols `sym` and `refl`, and `rewrite(X:S, A, E, M)` as `rw (λ (x : τ S), A) E M` (`rewrite` is a lambdapi keyword), where `rw` is defined by `ind_eq`.
- Sorts are terms of `Set` (`Stdlib.Set`): `'$i'` is `ι`, a type constructor is declared `Set → Set`, and a polymorphic symbol `Π (x0 : Set), ...`. `'$inhabited'(S)` is `el S`.
- Type quantification: Stdlib's `` `∀ `` ranges over the elements of a `Set`, not over `Set`, so our prelude adds a binder `∀ₜ : (Set → Prop) → Prop` with `π (∀ₜ p) ↪ Π a : Set, π (p a)`.
- `∃ₜ` is declared but has no rewrite rule yet.
- Type annotations are used where this was shown to improve checking performance, although it should not really be necessary.

### SMT-LIB (`smtlib.pl`)
In the manner of "Ground Truth" (Voronkov et al), ground premises of each step in such a way that in combination with the negated conclusion it produces an unsatisfiable SMT instance.
Produces an SMT-LIB script with one `push`/`check-sat`/`pop` per step.
- Each `check-sat` is preceded by `(set-info :status unsat)`.
- Only the instantiations of premises are read from the proof term. Propositional/theory reasoning (including equality) is left to the SMT solver.
- Sorts are sorts, declared with their arity (`(declare-sort |t.list| 1)`), but polymorphic symbols are _monomorphised_: each instance used in a check is declared in its scope.
- SMT-LIB `declare-sort-parameter` could support polymorphism but is not yet supported by mainstream SMT solvers.
- Some inferences are not checkable by nature, e.g. definition introduction, conjecture negation, etc.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted.
- `todo` steps are not checked: the solver echoes `warning: name (rule) is not checked` instead.

## Files (`src/`)
| File | Role |
|---|---|
| `main.pl` | `main(Backend)`: loads every module, runs, and exits with a status |
| `ops.pl` | Operators of the internal syntax |
| `load.pl` | `read_tstp/1`: `read/1` with TPTP operators, then normalisation |
| `db.pl` | The shared database: `step/3`, `symbol/4`, `introduced/2`, `ir_step/3`, `split/2`, and `record/1` to add to them |
| `logic.pl` | Formulas and clauses: `formula_clause`, `clause_formula`, `binder_variables`, `complement`, `flip`, `number_vars`, `substitute`, `formula_symbol` |
| `vampire.pl` | Vampire front end: clause or formula, rule table, inputs, the conjecture and AVATAR definitions; unknown rules become `todo` |
| `signature.pl` | The signature: symbol instances and term sorts, typing equations, default sorts for undeclared symbols (any front end); `overloaded/1` |
| `reconstruct.pl` | Proof search and the tactics |
| `rup.pl` | Reverse unit propagation |
| `close.pl` | Closing terms after search |
| `ir.pl` | IR documentation; `clause_type/2`, `reference/2` |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl`, `smtlib.pl` | Back ends |
| `printing.pl` | Shared printing: `out/1` and the `atom`, `number`, `codes` DCGs |
| `utils.pl` | Portable helpers: `each/2`, `warn/1`, `final/2`, `range/3`, `list//1` |

## Known Issues
- Backend scaling: for some backends (lambdapi) the largest proofs (e.g. `HWV057`, `SWV424-1.200`) time out or run out of memory. Not our problem, will be reported upstream.
- One failure at `read/1`: SYN986+1.004 blows the stack with its deep `succ` terms, but checks with `ulimit -s unlimited`.
- Some slowness during reconstruction in places, under investigation - e.g. `PUZ135_1`'s self-superposition.
- cvc5 exits 0 on `unknown` (`:status unsat` only catches `sat`), so `checksmt` would not notice a timeout.

## Testing
To test: produce a corpus of TSTP proofs in `solutions/` if not already.
Then use `gen*` scripts to produce transformed proofs (or just check the corpus with `check`).
Finally, use `check*` to check the resulting proofs.
All should produce noisy output on failure and play well with GNU parallel.

Be careful with memory when testing: e.g. lambdapi can hang indefinitely on some inputs and consumes all available memory.
