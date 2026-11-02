# Design

Isinglass reads Vampire (and in future other ATPs') TSTP proofs (CNF, FOF, or TFF), reconstructs each inference as an intermediate representation, and emits the result through one of several back ends.
Frontends, reconstruction and backends are kept separate, so that each prover and each output format can be treated separately.
Reconstruction is done by backtracking _search_ over the space of possible instances of an inference like, say, "binary resolution".

Overall: TSTP → frontend (e.g. 'Vampire') → ATP-agnostic proof → reconstruction → IR → backend (e.g. 'lambdapi')

Usage: `./ising Frontend Backend < proof.p`, where `Frontend` is `vampire` and `Backend` is `lambdapi`, `smtlib`, `agda` or `checker`. The script runs `main(Frontend, Backend)` in `src/main.pl` with SWI.

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
- Each binder has its own variable: `read/1` gives binders of the same name in one statement the same variable, so they are renamed apart at load time.
- Where formulas are compared (reconstruction, checker), bound variables are named canonically: `'$BOUND'(H)`, with `H` the number of binders nested in its scope (`logic:canonical/2`).
- Sorts are terms: e.g. `'$i'`, `'$o'`, type variables, and declared type constructors such as `list(A)`. The sort of sorts is `$tType` as in TFF1.
- Sorts `A` are assumed inhabited with the polymorphic symbol `$inhabited(A)`. The implementation tries to avoid using this for the sake of constructive backends.
- The signature is `symbol(Name, Params, Args, Sort)` (`db.pl`), with `Params` the sort variables, `Args` the domain and `Sort` the range.
- Reading normalises `S != T` to `~ (S = T)`, `F <= G` to `G => F`, `F <~> G` to `~(F <=> G)`, and `~|`, `~&` to a negated `|` or `&`. At some point this should perhaps be reported verbatim and subsequently normalised.
- Clauses are `clause(Bs, Literals)`: binders as in quantifiers, and a list of literals `A` or `~A` over their variables. Vampire's AVATAR shape `(! [X] : C) | ~spl` is a clause too.
- Vampire prints clauses as `fof` too, so shape alone cannot tell a clause from a formula. `$false` is the empty clause. Otherwise a statement is a clause if it is clause-shaped and is either `cnf`, an input, or derived by clausal reasoning: `cnf_transformation`, a rule in the table below, or an unknown rule from clauses only. The conjecture, its negation, preprocessing and definitions are formulas.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so every lookup is a fresh instance and instantiation is unification.
- When a step is reconstructed, its conclusion is made rigid, so the IR is ground: a clause by numbering its variables `'$VAR'(N)` in binder order, a formula by naming its bound variables canonically.
- In search contexts, `X-T` is an entry (`X : T`); `X : Sort` is always a quantifier or clause binder.

## IR (`ir.pl`, `db.pl`)
- Proofs are λ-terms, Curry–Howard style, in minimal logic with an abstract `⊥`.
- This does not necessarily exclude non-Curry-Howard systems, e.g. the SMT-LIB backend just looks for groundings in the proof term.
- First-order arguments `Ts` are terms, kept apart from proof arguments (so that back ends can read premise instances directly).
- `clause(Bs, [L₀…Lₙ₋₁])` has type `Π Bs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`), where `¬F` is `F → ⊥`.
- `formula(F)` has type `F`.
- Formulas are taken apart by expansion rules, as in a tableau (`ir:rule_type/3`): a built-in head applied to a proof of the formula and a refutation of each branch, e.g. `'$or' : F | G → (F → ⊥) → (G → ⊥) → ⊥`.
- The hypotheses that an expansion rule binds are annotated `'$inferred'` rather than with their formulas, which follow from the rule's first argument: annotating the parts of a conjunction would make terms quadratic in its size. The checker and `close.pl` infer them; back ends that print binder types must too.
- The rules for `?` and `~!` bind an eigenvariable. `'$nex'` turns `~?` into `!~`.
- Clause-shaped `fof`/`tff` inputs are clauses, as for CNF problems.
- The hypothesis for a negative literal `~A` is `¬¬A`, so `¬¬`-elimination is never needed. The IR is therefore sound under any reading of `⊥`: classical falsity, or the conjecture of the A-translation.
- Heads are variables or constants, so terms are β-normal apart from `let`.
- Rewriting: in `rewrite(X:S, A, E, M)` the motive `A` is any formula context `A[X]` so that `E : S = T` rewrites `M : A[S]`, producing `A[T]`.
- Clause splits: a split symbol is a defined proposition that unfolds to the type of its clause.
- A hypothesis `H : ¬¬Split` is used as `H (λ d, d ts …)`; `H : ¬Split` is refuted by proving the definition, `H (λ xs hs, …)`, with eigenvariables `xs`.
- Function definitions: `definition(F, Bs, T)` defines `F(Xs)`, for binders `Bs = Xs : Sorts`, as the term `T`. It is the prover's own step, whose conclusion is the unit clause `F(Xs) = T`, either way round: a conservative extension, so the step is an axiom.
- Predicate definitions: `definition(P, Bs, F)` defines `P(Xs)` as the formula `F`, and its conclusion is `![Bs] : (P(Xs) <=> F)`. Like a split symbol, a defined predicate unfolds to its body: a formula is also of any type that differs from it by unfolding defined atoms (`ir:expanded/2`). Proofs use this only at a `let`, which states the unfolded type, so the back ends need only define the predicate. A body cites only definitions before it, so unfolding terminates.
- Skolem symbols: `skolem_def(Sk, Bs, F)` defines `Sk(Xs)`, for binders `Bs = Xs : Sorts`, as Hilbert's choice `ε Y. T` of a δ formula `F`: `?[Y:S|Ys] : G` (`T` is `?[Ys] : G`) or `~![Y:S|Ys] : G` (`T` is `~![Ys] : G`).
  It is a step named `Sk_def`, whose conclusion is its _choice axiom_ `![Bs] : (F => T[Sk(Xs)/Y])` (`ir:choice_axiom/4`), so a proof opens a δ formula by applying it, like any other step. It is recorded just before the step that first uses it.

## Classical Logic and Conjectures
The IR does not pre-suppose classical logic, and large chunks of ATP proofs are intuitionistically valid, which may be surprising.
Future constructive backends may use an A-translation to produce a constructive proof (!).

- Proof terms stay in minimal logic with an abstract ⊥. No DNE or excluded middle appears in the clausal IR, but may in steps between formulas.
- Of the formula expansion rules, those for `~(F => G)`, `~(F <=> G)` and `~!` are not valid in minimal logic.
- Neither is the choice axiom of a Skolem symbol for `~!` (a counterexample is chosen); that for `?` needs only choice.
- The other rules are valid for any `⊥`, so a step from a formula to a clause is often constructive.
- The negated conjecture is a parameter, not an axiom. Its type is `G → ⊥`, and only the `conjecture` step discharges it.
- A classical back end proves `G` by double-negation elimination.
- An A-translation takes `⊥ := G` and the negated conjecture `nc := id`, so the theorem is `refutation id`.
- If a conjecture does not appear in the proof (whether or not one was given) the IR ends at `$false`.

## Reconstruction (`reconstruct.pl`, `transform.pl`, `rup.pl`, `close.pl`)
Reconstruction tries to build an IR term with the conclusion's type given that the step is e.g. "resolution".

- Conclusion variables and eigenvariables are numbered `'$VAR'(N)` _before_ search, so unification cannot instantiate them.
- Closing (`close.pl`) runs after search: binders are named `h(N)`, and it tries to fill term-level variables left unconstrained with a suitable inhabitant (else `'$inhabited'(S)`)
- RUP (`rup.pl`): ground reverse unit propagation as in a SAT solver, split out into a separate module.
- Many rules are simply variants of a parent, up to instantiation, factoring, reflexivity, literal re-ordering, and symmetry of equality.
- Resolution finds the pivot literal and then matches remaining literals in the same way. Unit-resulting resolution is the same, with a unit minor premise for each pivot (unit but for AVATAR split literals, which are in the conclusion).
- Paramodulation is similar: each literal is matched to a premise, or rewritten using one positive equation `A = B` from a premise.
- Equality factoring is the same, but the equation comes from a hypothesis for a conclusion literal `A != B`
- Denial: derive `~A` from the negated conjecture `~A`, modulo symmetry.
- Rewrites respect sorts: the walk knows the sort of each argument position from the signature, and rewrites only where it unifies with the equation's sort.
- Definition unfolding replaces every occurrence of each defined symbol. Each definition is oriented which side is a pattern, backtracking if both are. Each literal is unfolded deterministically, innermost first. Its context is the literal around the occurrence, rebuilt from a zipper of frames.
- Definition folding replaces each instance of the body of a function definition by the defined term. It is proved the other way round, from the conclusion: each defined term in a conclusion literal is unfolded by one rewrite, at every occurrence at once, as folded terms can be large (in SWV545-1.010, 885k nodes, with 59049 occurrences of one instance). As each rewrite states the whole literal, a premise literal of more than 100k nodes is not attempted.
- Steps by definition (`defined(Tactic)`): the defined atoms of the hypotheses are unfolded, where their bodies are literals (a hypothesis `~~~C` becomes `~C`), and `Tactic` refutes the conclusion as if stated with the bodies: `variant` of the first parent, or `tautology`, of equality (reflexivity, symmetry, transitivity), with no premise.
- A failed tactic leaves the step as `todo`, with a warning.

### Preprocessing (`normal.pl`, `transform.pl`)
Transformation to normal form is an entailment from one parent, transformed structurally.
A general tableau search for these blows up, as it must guess which of many parts to take apart next.
Instead, each prover rule names the transformation it performs, and the tactic checks just that one, with no search.

- Each transformation has a _normal form_ (`normal:normal/3`), a ground key that forgets what the transformation may change: `base` (renaming, `~~`, `=>`, nesting of `&`/`|` and their units, operand order, equation orientation, vacuous and grouped quantifiers), `ennf` (and negation pushed to atoms, keeping `<=>`), `nnf` (and `<=>` expanded), `simplify` (and `$true`/`$false`), `pure(Ss)` (pure predicates replaced by `$true`/`$false`), `skolem(Ss)` (as `ennf`, with bound variables and terms of the Skolem symbols `Ss` all `'$skolem'`).
- The keys are approximate, so that small implementation differences (reordering, renaming, flipped equations, vacuous quantifiers) do not matter.
- `transform(Mode)` fails at once unless the parent and conclusion have the same key.
- The proof then takes the two apart in lockstep (`pair`), and the keys say which parts go together:
  - literals close modulo symmetry;
  - a δ formula's eigenvariables instantiate its γ counterpart, binder by binder, skipping vacuous ones;
  - otherwise the conjunctive side is expanded into a _pool_ of parts by key, and each branch of the other side is looked up in it, or split further.
- In nnf the negation of an expanded `<=>` is a disjunction of conjunctions, so there both formulas are also compared the other way round.
- Weakening steps:
  - `pure`: the pure predicates are those of the parent that are not in the conclusion.
  - `definition`: one `<=>` of the parent becomes the `=>` that makes the keys equal.
- Definition folding (`transform(fold)`): the parent and the conclusion are unfolded throughout (by `let`s that state the unfolded types), and are then the same, as in `base`.
- Skolemisation (`transform(skolem)`) is an entailment once each Skolem symbol is defined by choice (see IR):
  - the Skolem symbols are those of the conclusion that are `introduced(_, skolem)` and not in the parent;
  - a δ formula of the parent is opened by the choice axiom of a Skolem term `sK(As)` in its counterpart, so the term is read off the conclusion, and no prover convention (e.g. argument order) is assumed. Its arguments must be distinct eigenvariables, including those of the δ formula, and the definitions of a symbol must agree;
  - the keys forget Skolem terms, so lookups are ambiguous: each counterpart is tried, a disjunction is looked up too (its counterpart may be a `?` not yet opened), and a choice is pruned unless each atom with the bound variable is in the counterpart with the term in its place (`plausible`), as several `?` may be Skolemised at once;
  - a `?` may come between the parent's universals, so a δ formula of the conclusion opens only as many eigenvariables as its counterpart has universals, and a clause conclusion instantiates the parent's universals around its Skolemised `?`;
  - a type may be chosen too (a δ over `$tType`), as in TF1.
- `clausify` reconstructs `cnf_transformation` of a formula: the clause's literals refute the parent, by one part of each conjunction and every branch of each disjunction, closing literals by unification.
  Its only search is the choice of conjunct, pruned to those whose literals the clause's predicates and signs could refute (`fits`).
- A clause conclusion whose variables are not the parent's outermost universal ones (Vampire's AVATAR shape `(! [X] : C) | ~p`) is refuted in the same way.

## Frontends
The job of a frontend is to load the proof of a given system in its own idiom, then match its inference rules to the existing ATP-generic 'tactics' that we know how to reconstruct.

### Vampire (`vampire.pl`)
| Vampire rules | Tactic |
|---|---|
| resolution, forward/backward_subsumption_resolution, unit_resulting_resolution, forward_literal_rewriting | `resolve` |
| factoring, duplicate_literal_removal, sat_conversion, avatar_contradiction_clause, avatar_sat_refutation, reorient_equations, trivial_inequality_removal, equality_resolution | `variant` |
| superposition, forward/backward_demodulation | `paramodulate` |
| equality_factoring | `equality_factor` |
| definition_unfolding | `unfold` |
| definition_folding of function definitions, in a clause | `fold` |
| definition_folding of predicate definitions, in a formula | `transform(fold)` |
| function_definition (introduced) | `definition` |
| predicate_definition_introduction, equality_proxy_definition: `P(Xs) <=> F`, or `F \| ~P(Xs)` (introduced) | `transform(base)`, or `transform(definition)`, from `P_def` |
| inequality_splitting_name_introduction: `~P(T)` (introduced) | `defined(tautology)` from `P_def`, where `P(X)` is `X != T` |
| equality_proxy_replacement, inequality_splitting | `defined(variant)` |
| equality_proxy_axiom | `defined(tautology)` |
| avatar_split_clause | `avatar_split` |
| avatar_component_clause | `avatar_component` |
| rat | `rup` |
| cnf_transformation of a clause | `variant` |
| cnf_transformation of the negated conjecture, an atom | `deny` |
| rectify, flattening | `transform(base)` |
| ennf_transformation | `transform(ennf)` |
| nnf_transformation | `transform(nnf)` |
| true_and_false_elimination | `transform(simplify)` |
| pure_predicate_removal | `transform(pure)` |
| unused_predicate_definition_removal | `transform(definition)` |
| skolemize | `transform(skolem)` |
| cnf_transformation of a formula | `clausify` |

The conjecture becomes `conjecture`, `negated_conjecture` becomes `negated_conjecture`, and any other rule becomes `todo`.
Skolemisation (status `esa`) is an entailment once its symbols are defined by choice; so is a definition, an axiom of its fresh symbol. A predicate definition is printed as Vampire uses it, which may be one direction only, so the front end records the definition itself first, as the step `P_def`, from which the printed one follows. The other steps that preserve only satisfiability are not yet handled: renaming (`consistent_polarity_flipping`) and general splitting.
For `deny`, the front end skips (nil) preprocessing between the negated conjecture and its clause (e.g. `flattening`), and preprocessing of the negated conjecture of an atom is a denial too, so that these steps stay constructive.
A clause-shaped conclusion of a preprocessing step is a clause, like any other, and a clause parent enters a preprocessing tactic by the type of its clause.

## Backends

### Checker (`checker.pl`)
An independent-ish type checker of each ground, annotated term against the type of its conclusion.
- First-order terms are checked against the signature.
- Formula types are kept canonical, so they are compared syntactically (or, failing that, with defined predicates unfolded), and a quantified hypothesis is instantiated by substitution.
- An expansion rule is typed by its first argument (`ir:rule_type/3`).
- The sort of each eigenvariable is well formed.
- The `conjecture` step `G` must cite a refutation of `$false`, and a checked `negated_conjecture` step `~G`.
- A Skolem symbol is defined once, by a well-sorted δ formula of its arguments only (distinct eigenvariables of the sorts of its signature), and its step is exactly its choice axiom.
- A function symbol is defined once, by a well-sorted term of its arguments only, citing only symbols defined before it, and its step is exactly the equation of its definition, either way round. So is a predicate, by a well-sorted formula, and its step is exactly `![Bs] : (P(Xs) <=> F)`.
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
- `∃ₜ` is declared with its introduction and elimination rules.
- The expansion rules are lemmas of the prelude (`and_e`, `nall_e`, ...), proved from Stdlib; the classical ones use `Stdlib.Classic`. Rules over type variables are separate lemmas (`ex_t`, `nall_t`, `nex_t`).
- Skolem symbols are declared with the signature (as `symbol`, so they may be given a rule). A `skolem_def` gives the rule `sK ↪ λ xs, ε (λ y, T)` (`Stdlib.Epsilon`), so that `sK xs` unfolds, and proves its choice axiom by `εᵢ`; for `~!`, by a classical prelude lemma `nall_ε`.
- A function `definition` gives the rule `sF ↪ λ xs, T`, so that its equation is proved by `refl`; a predicate's gives `sP ↪ λ xs, F`, so its definition is proved by `∧ᵢ (λ h, h) (λ h, h)`.
  A type is chosen by `εₜ : (Set → Prop) → Set`, which Stdlib lacks, so it is postulated with its introduction rule `εₜᵢ`, like `∃ₜ` (and `nall_εₜ`).
- Canonical bound variables are printed `yN`, eigenvariables `xN`.
- Type annotations are used where this was shown to improve checking performance, although it should not really be necessary.

### Agda (`agda.pl`)
For a hammer: a term to fill a hole, constructive by the A-translation.
- The output is `Proof.refutation bridge ... bridge`, then `where` and a module `Proof {R : Set} (leaf : type) ...` with one definition per clausal step.
- `R` is the IR's `⊥`. Agda infers it to be the goal, so the goal is never printed; `~F` is `F → R`.
- The leaves are the input clauses and negated conjecture, parameters of the module. The negated conjecture `G → R` is the identity.
- We expect one conjecture, a ground atom (or none: then the term has any type). Inputs are clauses.
- Sequent reading: the Agda term of an input clause is assumed to have type `∀ xs → A₁ → … → Aₙ → B₁ ⊎ … ⊎ Bₘ` (`⊥` if `m = 0`) for its negative literals `~Aᵢ` and positive literals `Bⱼ`, in order.
- Input clauses are transformed to the usual clause type in continuation-passing style.
- Names are printed verbatim: the hammer names symbols, sorts and inputs after their Agda terms. Only the prover's own symbols are renamed (e.g. `spl0_1` is `spl0-1`, as `_` marks an argument place).
- Assumed in scope: `_≡_`, `refl`, `sym`, `trans`, `cong` and `subst`, with their terms left for Agda to infer; for clausal transformation `⊥-elim` and `[_,_]′`.
- `'$inhabited'(S)` is a hole `{! !}`, as is a clause-typed `todo` step. Formula steps and Skolem definitions are not printed.
- A function `definition` is printed as an Agda definition of its symbol in the module (so `agda_file` does not postulate it), and its equation is proved by `refl`. So is a predicate, whose definition step is a formula and is not printed; a body that Agda cannot state (of `&`, `|`, `<=>` or `?`) is a hole.
- A step between formulas (`ir:formula_step/1`) is a hole too: its parent is a formula, and some of its rules are classical. The hammer's inputs are clauses, so it has none.
- Everything is in `Set`: no universe levels, so no split definitions over type variables.
- `agda_file` is a second entry point for testing: a module that postulates the signature and the input clauses, with names mangled such that TPTP names are Agda identifiers.

### SMT-LIB (`smtlib.pl`)
In the manner of "Ground Truth" (Voronkov et al), ground premises of each step in such a way that in combination with the negated conclusion it produces an unsatisfiable SMT instance.
Produces an SMT-LIB script with one `push`/`check-sat`/`pop` per step.
- Each `check-sat` is preceded by `(set-info :status unsat)`.
- Only the instantiations of premises are read from the proof term. Propositional/theory reasoning (including equality) is left to the SMT solver.
- Sorts are sorts, declared with their arity (`(declare-sort |t.list| 1)`), but polymorphic symbols are _monomorphised_: each instance used in a check is declared in its scope.
- SMT-LIB `declare-sort-parameter` could support polymorphism but is not yet supported by mainstream SMT solvers.
- Some inferences are not checkable by nature, e.g. definition introduction, conjecture negation, etc.
- Skolem symbols are uninterpreted, and their definitions are not checked (Skolemisation is a step between formulas). Nor are definitions: the equations of functions are premises of later checks, and monomorphic predicates are defined in the header by `define-fun`.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted.
- `todo` steps are not checked: the solver echoes `warning: name (rule) is not checked` instead.
- Neither are steps between formulas (`ir:formula_step/1`): a formula with `?` under `!` has no ground instance to assert. Asserting the parent and the negated conclusion with their quantifiers would check them, but not in the manner of "Ground Truth".

## Files (`src/`)
| File | Role |
|---|---|
| `main.pl` | `main(Frontend, Backend)`: loads every module, dispatches on both, and exits with a status |
| `ops.pl` | Operators of the internal syntax |
| `load.pl` | `read_tstp/1`: `read/1` with TPTP operators, then normalisation |
| `db.pl` | The shared database: `step/3`, `symbol/4`, `introduced/2`, `ir_step/3`, `split/2`, and `record/1` to add to them |
| `logic.pl` | Formulas and clauses: `formula_clause`, `clause_formula`, `binder_variables`, `complement`, `flip`, `number_vars`, `substitute`, `occurs`, `canonical` |
| `vampire.pl` | Vampire front end: clause or formula, rule table, inputs, the conjecture and AVATAR definitions; unknown rules become `todo` |
| `signature.pl` | The signature: symbol instances and term sorts, typing equations, default sorts for undeclared symbols (any front end); `overloaded/1` |
| `reconstruct.pl` | Proof search and the tactics |
| `matching.pl` | Refuting a literal or formula by a hypothesis, shared by the tactics |
| `normal.pl` | Normal forms of formulas for each preprocessing transformation, as keys |
| `transform.pl` | The tactics for steps between formulas: preprocessing (`transform`) and clausification (`clausify`) |
| `rup.pl` | Reverse unit propagation |
| `close.pl` | Closing terms after search |
| `ir.pl` | IR documentation; `clause_type/2`, `step_type/2`, `builtin_type/2`, `rule_type/3`, `formula_step/1`, `reference/2` |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl`, `smtlib.pl`, `agda.pl` | Back ends |
| `printing.pl` | Shared printing: `out/1` and the `atom`, `number`, `codes` DCGs |
| `utils.pl` | Portable helpers: `each/2`, `warn/1`, `final/2`, `range/3`, `list//1` |

## Known Issues
- Backend scaling: for some backends (lambdapi, Agda) some large (e.g. `HWV057`, `SWV424-1.200`) or otherwise-tricky proofs time out or run out of memory. Not our problem, will be reported upstream if relevant.
- One failure at `read/1`: SYN986+1.004 blows the stack with its deep `succ` terms, but checks with `ulimit -s unlimited`.
- Some slowness during reconstruction in places, under investigation - e.g. `PUZ135_1`'s self-superposition.
- cvc5 exits 0 on `unknown` (`:status unsat` only catches `sat`), so `scripts/checksmt` would not notice a timeout.

## Testing
To test: produce a corpus of TSTP proofs in `solutions/` if not already.
The scripts in `scripts/` each take one file and are run from the top level, e.g. `scripts/genlp solutions/PUZ001+1`.
Use `gen*` to produce transformed proofs via `ising` (or just check the corpus with `check`).
Finally, use `check*` to check the resulting proofs.
All should produce noisy output on failure and play well with GNU parallel.
