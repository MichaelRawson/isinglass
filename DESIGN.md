# Design

Isinglass reads Vampire (and in future other ATPs') TSTP proofs (CNF, FOF, or TFF), reconstructs each inference as an intermediate representation, and emits the result through one of several back ends.
Front ends, reconstruction and back ends are kept separate, so that each prover and each output format can be treated separately.
Reconstruction is backtracking _search_ over the possible instances of an inference like, say, "binary resolution".

Overall: TSTP → front end (e.g. `vampire`) → ATP-agnostic proof → reconstruction → IR → back end (e.g. `lambdapi`)

Usage: `./ising [--trace] [--optimise] [--implicits=Kinds] [--complete] Frontend Backend < proof.p`, where `Frontend` is `vampire` and `Backend` is `lambdapi`, `smtlib`, `agda`, `agda_term`, `agda_file` or `checker`.
The script runs `main(Frontend, Backend, Options)` in `src/main.pl` with SWI.
`--trace` prints each step and its tactic to stderr as its search starts, so a slow step is the last one printed; `--optimise` optimises the IR before it is emitted.
`--implicits=eq,letp` (either) makes the Agda back ends give further type arguments: `eq`, the sort of `_≡_` in types; `letp`, the result `R` of `letp` (`agda_term`).
`--complete` makes the Agda back ends print no proof that would have holes: they fail, naming what each hole would stand for (the rule of a step not reconstructed, `formula_step`, the definition of a predicate, or `inhabited`), for a caller that cannot fill them.

## Design Decisions
- Concise, reasonably-portable Prolog.
- TSTP is read with `read/1`; TPTP operators are declared only while reading (`load.pl`).
- Agnostic to ATP system, in principle.
- The IR attempts to be logic-agnostic and constructive. Back ends make every encoding decision.

## Internal Language (`ops.pl`, `load.pl`, `signature.pl`)
- Rank-1 polymorphic first-order logic. Variables, terms and atoms are Prolog variables and terms.
- Connectives `~F`, `F | G`, `F & G`, `F => G`, `F <=> G`, `'$true'`, `'$false'`. Reading normalises `!=`, `<=`, `<~>`, `~|` and `~&` away.
- Equality is typed, `'$='(A, S, T)` for `S, T` of sort `A`: the front end gives each equation its sort at load time (`signature:typed/3`).
- Quantifiers have one binder each, `'!'(X : Sort, F)` and `'?'(X : Sort, F)`, so `! [X, Y] : F` is `! [X] : ! [Y] : F` and quantifier rules are patterns of unification. Each binder has its own variable: those that `read/1` shares are renamed apart at load time.
- Where formulas are compared, bound variables are named canonically, `'$BOUND'(H)`, with `H` the number of binders nested in its scope (`logic:canonical/2`).
- Sorts are terms (`'$i'`, `'$o'`, type variables, `list(A)`, ...), of sort `$tType` as in TFF1. Sorts are assumed inhabited by `'$inhabited'(S)`, which is avoided where possible for the sake of constructive back ends.
- The signature is `symbol(Name, Params, Args, Sort)` (`db.pl`); a polymorphic symbol takes its type arguments first.
- Clauses are `clause(Bs, Literals)`: binders `X : Sort` and literals `A` or `~A`. Vampire prints clauses as `fof` too, so a statement is a clause if it is clause-shaped and either `cnf`, an input, or derived by clausal reasoning; the conjecture, its negation, preprocessing and definitions are formulas. Vampire's AVATAR shape `(! [X] : C) | ~spl` is a clause.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so each lookup is a fresh instance and instantiation is unification. A reconstructed conclusion is made rigid: a clause's variables are numbered `'$VAR'(N)` in binder order, and a formula's bound variables are named canonically.
- In search, `X-T` is an entry `X : T`; `X : Sort` is always a binder.
- TPTP names statements apart from symbols, so statements are read as `'$step:Name'`, inputs as `'$input:Name'`, and the definition of a symbol `P` is the step `'$def:P'` (`utils:named/3`). Back ends print them apart; warnings print them bare.

## IR (`ir.pl`, `db.pl`)
- Proofs are λ-terms, Curry–Howard style, in minimal logic with an abstract `⊥`. A back end need not be Curry–Howard: SMT-LIB just reads groundings off the proof term.
- Terms are built by application `M @ N` (curried, left-associative) and `'$lam'(X, T, M)`, over variables `'$VAR'(N)` (hypotheses and eigenvariables alike, told apart by the λ's annotation), steps and built-ins. An argument is a term or a proof as the head's type says (`ir:proof_argument/1` tells them apart syntactically in ground IR). A problem symbol `'@'/2` is refused at load time.
- A type is a sort or `'$proof'(F)`, disjoint as `τ` and `π` in Lambdapi, and taken apart only as needed: `'$proof'(F => G)` is `'$proof'(F) → '$proof'(G)`, `~F` is `F => '$false'`, `'$proof'(![X:S] : F)` is `Π X : S. '$proof'(F)`.
- `clause(Bs, [L₀…Lₙ₋₁])` has type `Π Bs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`); `formula(F)` has type `F`.
- Formulas are taken apart by tableau expansion rules: a built-in applied to a proof of the formula and a refutation of each branch, e.g. `'$or' : F | G → (F → ⊥) → (G → ⊥) → ⊥`. One table, `ir:head_type/2`, types every built-in; their parameters are inferred by first-order unification with the expected type and the arguments' types. The preprocessing tactics read the rules' branches off it (`ir:rule_branches/3`).
- Hypotheses bound by an expansion rule are annotated `'$inferred'`, as they follow from its first argument (annotations would be quadratic in a conjunction's size). The checker and `close.pl` infer them, as must back ends that print binder types.
- The rules for `?` and `~!` bind an eigenvariable. `'$nex'` is a γ rule, turning `~?[X] : F` into `![X] : ~F`; over `$tType` it is `'$nex_t'`.
- The hypothesis for a negative literal `~A` is `¬¬A`, so `¬¬`-elimination is never needed and the clausal IR is sound for any reading of `⊥`.
- A head may be any term: `'$lam'(X, F, N) @ M` is a lemma `X : F` proved by `M` (back ends may print a `let`). Its λ states the hypothesis's type.
- Rewriting is `'$rewrite' : Π (P : S > $o). S = T → P S → P T`, with an explicit motive `'$abs'(X:S, A)` (THF's `^[X:S] : A`), as inferring it would be higher-order unification; its application `'$at'(P, T)` is β-reduced as soon as `P` is known (`ir:applied_motives/2`). Arrow sorts and `'$at'` occur only in `ir:head_type/2`, so the logic stays first-order.
- AVATAR splits: a split symbol is a predicate definition of no arguments whose body is its clause's type. A hypothesis `¬¬Split` is used as `H (λ d, d ts …)`, and `¬Split` is refuted by proving the definition, `H (λ xs hs, …)`.
- Function definitions `definition(F, Bs, T)` conclude the unit clause `F(Xs) = T`, either way round; predicate definitions `definition(P, Bs, F)` conclude `![Bs] : (P(Xs) <=> F)`. Both are conservative extensions, so these steps are axioms, and back ends define the symbols. A formula is of any type that differs from it by unfolding definitions (`ir:expanded/2`); a body cites only earlier definitions, so unfolding terminates.
- Skolem symbols: `skolem_def(Sk, Bs, F)` defines `Sk(Xs)` as Hilbert's choice of the δ formula `F = ?[Y:S] : T`. Its step `'$def:Sk'` concludes the choice axiom `![Bs] : (F => T[Sk(Xs)/Y])` (`ir:choice_axiom/4`), which opens `F` like any other step, and is recorded just before its first use.

## Classical Logic and Conjectures
- Large parts of ATP proofs are intuitionistically valid. Proof terms stay in minimal logic with an abstract `⊥`: the clausal IR has no DNE or excluded middle, though steps between formulas may.
- The rules for `~(F => G)`, `~(F <=> G)` and `~!`, and `'$dne'`, are classical; Skolem choice axioms need only choice.
- The negated conjecture is a hypothesis `G → ⊥`, discharged only by the `conjecture` step. A classical back end proves `G` by double-negation elimination; the A-translation takes `⊥ := G` and the negated conjecture to be the identity, so constructive back ends get a constructive proof.
- If no conjecture appears in the proof, or its negation is not recognised, the IR ends at `$false`.

## Reconstruction (`reconstruct.pl`, `transform.pl`, `rup.pl`, `close.pl`)
A tactic builds an IR term of the conclusion's type, given that the step is, say, resolution.

- Conclusion variables and eigenvariables are numbered before search, so unification cannot instantiate them.
- Closing (`close.pl`) runs after search: remaining binders are numbered, and unconstrained term variables get a small inhabitant of their sort found by walking each application against its head's type (else `'$inhabited'(S)`).
- Many rules are variants of a parent, up to instantiation, factoring, reflexivity, literal order, and symmetry of equality.
- Resolution matches the major premise's literals to hypotheses or minor premises (units, in unit-resulting resolution). Paramodulation matches each literal or rewrites it by one equation of the other premise; equality factoring takes the equation from a hypothesis.
- Literals are matched most constrained first (first-fail), taking a literal with one candidate at once. Matching is subsumption, NP-complete, so this is a heuristic: in order, a wide clause of interchangeable literals is searched exponentially (SYO613-1).
- Rewrites respect sorts, from the signature's argument sorts.
- Definition unfolding replaces each defined symbol innermost first, with its context rebuilt from a zipper of frames. Folding of function definitions needs no rewrites, as defined terms unfold by definition (`ir:terms_unfolded/2`): folded terms can be huge (SWV545-1.010).
- `defined(Tactic)`: hypotheses' atoms of the cited definitions are unfolded where their bodies are literals, and `Tactic` refutes the conclusion as if stated with the bodies.
- `tautology`: ground completion of the equations of the negative literals, then a fact is refuted by a hypothesis or a positive equation is reflexive.
- `components` (general splitting) refutes the split hypothesis by proving the component clause, as for AVATAR, then the conclusion is a variant of the parent.
- `first(Tactics)` is the first of `Tactics` that succeeds. A clausal step proves the definitions of its split literals first, so back ends define them before use.
- A failed tactic or unknown rule leaves the step `todo`, with a warning; a `todo` step only warns about parents it cannot prove.

### Preprocessing (`normal.pl`, `transform.pl`)
A general tableau search for preprocessing steps blows up, so each rule names its transformation, and the tactic checks just that one.

- Each transformation has a ground _key_ (`normal:normal/3`) forgetting what it may change: `base` (renaming, `~~`, `=>`, nesting and units of `&`/`|`, operand order, equation orientation, vacuous quantifiers), `ennf` (negation pushed to atoms, but for `<=>`), `nnf` (and `<=>` expanded), `simplify` (`$true`/`$false`), `pure(Ss)`, `skolem(Ss)` (Skolem terms and bound variables blurred). Keys are approximate, so small implementation differences do not matter.
- `transform(Mode)` fails at once unless parent and conclusion have the same key. It then takes them apart in lockstep (`pair`):
  - literals close modulo symmetry, and a formula closes against its negation before either is taken apart (a chain of `<=>` splits exponentially, SYN007+1.014);
  - δ eigenvariables instantiate the γ counterpart, skipping vacuous binders and conjuncts that are units of the key; failing that, only as many δ binders as the γ formula has are opened;
  - otherwise the conjunctive side becomes a _pool_ of parts by key, in which each branch of the other is looked up, or split further. Self-closing parts are found once per pool.
  - in nnf both formulas are also compared the other way round.
- Weakening: `pure` replaces the parent's pure predicates; `definition` weakens one `<=>` to `=>`.
- `transform(fold)` unfolds both sides throughout, then compares as `base`.
- Skolemisation (`transform(skolem)`) opens a δ formula by the choice axiom of a Skolem term read off the conclusion, so no prover convention is assumed. Keys forget Skolem terms, so counterparts are ambiguous: branches are closed smallest first, so a wrong counterpart fails early (ITP009+2). Vampire's `skolemize` hints settle the choice where given (`skolem_hint/2`, checked only by count), without which LCL652+1.015 is exponential. A type may be chosen too.
- `clausify` refutes the parent by the clause's literals: one part of each conjunction, every branch of each disjunction. Its only search is the choice of conjunct. A clause conclusion not over the parent's outermost universals (the AVATAR shape) is refuted the same way.

## Front Ends
A front end loads a prover's proof and maps its rules to the ATP-generic tactics.

### Vampire (`vampire.pl`)
| Vampire rules | Tactic |
|---|---|
| resolution, forward/backward_subsumption_resolution, unit_resulting_resolution, forward_literal_rewriting, extensionality_resolution | `resolve` |
| factoring, duplicate_literal_removal, avatar_contradiction_clause, avatar_sat_refutation, reorient_equations, trivial_inequality_removal, equality_resolution, condensation | `variant` |
| superposition, forward/backward_demodulation, forward/backward_subsumption_demodulation | `paramodulate` |
| equality_factoring, inner_rewriting | `equality_factor` |
| definition_unfolding | `unfold` |
| definition_folding of function definitions, in a clause | `fold` |
| definition_folding of predicate definitions, in a formula | `transform(fold)` |
| function_definition, avatar_definition (introduced) | `definition` |
| predicate_definition_introduction, equality_proxy_definition (introduced) | `transform(base)` or `transform(definition)`, from `'$def:P'` |
| inequality_splitting_name_introduction (introduced) | `defined(tautology)` from `'$def:P'` |
| equality_proxy_replacement, inequality_splitting, consistent_polarity_flipping | `defined(variant)` |
| equality_proxy_axiom | `defined(tautology)` |
| general_splitting_component_introduction (introduced) | `transform(nnf)` from `'$def:P'` |
| general_splitting | `components` |
| sat_conversion | `first([variant, avatar_split])` |
| theory_tautology_sat_conflict (introduced) | `tautology` |
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

- `negated_conjecture` (`conjecture_negation` in later versions) becomes `negated_conjecture`, and any other rule `todo`.
- A predicate definition is printed as Vampire uses it, perhaps one way only, so the front end first records the definition itself, `'$def:P'`, from which the printed one follows. Binders are put in the order of the atom's arguments.
- An AVATAR split `spl <=> C` is restated as `spl <=> T` for the clause type `T` of `C`, kept as `split/2` for the AVATAR tactics.
- General splitting names a component `C` by `P(Xs)`, over the variables it shares with the rest, so `P(Xs)` is defined as `~` the type of `C`.
- Consistent polarity flipping replaces `P` by its negation but keeps the name, so steps after it state `P_flipped`, defined as `~P`. The flipped predicates are those whose signed literals differ between a flipping step and its parent. A step is before flipping if it is an input, an ancestor of a flipping step, or derived only from such steps.
- For `deny`, preprocessing of the negated conjecture of an atom is skipped, so these steps stay constructive.
- A Skolemised `(! [X] : C) | L` stays a formula, as its parent's δ formula is under the disjunction too.

## Optimisation (`optimise.pl`)
An optional pass makes proofs smaller, as statements dominate the output (SYN837-1's 28-binder clauses, with tiny proofs). The result is ordinary IR.
- A clausal step cited only by full applications in clausal steps is inlined if `Uses × (Size − Skeleton) < Size + size of its clause`, where `Skeleton` is the size of a citation, saved if no argument is copied. A step forwarding to another costs nothing.
- A step proving `S = T`, with `S` and `T` the same once defined terms are unfolded, is proved by `refl` and always inlined.
- A function definition is inlined likewise, `Uses × (Size − 1) < Size + 2`; its symbol is dropped, its step becomes `T = T`, and the steps are optimised again.
- Steps no longer cited by the last refutation or the conjecture are dropped, but for definitions.
- Each term is normalised in one top-down pass, binding names to values or closures, so it is linear even for long chains of steps cited once. A hypothesis argument is substituted if cheap or used once, dropped if unused, else kept as a redex; η-reduction for hypotheses; `sym` is pushed down to the hypotheses; a trivial rewrite is its proof. Eigenvariable λs are kept: SMT-LIB reads split eigenvariables off them, and lambdapi type rules.
- An inlined step is checked by SMT-LIB as part of the step that cites it.

## Back Ends

### Checker (`checker.pl`)
An independent-ish type checker of each ground, annotated term against its conclusion's type.
- Terms are checked against the signature; sorts of eigenvariables and motives are well formed.
- Formulas are compared syntactically, or failing that up to `~F` being `F => $false` and unfolding of definitions.
- An application is typed by its head, whose type its arguments take apart in order. The result is unified with the expected type first, then each argument checked against its premise; `'$rewrite'`'s result is a substitution, so its premises are checked first. A type still not ground is rejected.
- A β-redex is checked by binding, without substituting one proof into another. Every binder is fresh.
- The `conjecture` step must cite a refutation and a checked `negated_conjecture`. Skolem symbols, functions and predicates are each defined once, by a well-sorted body of their arguments only (citing only earlier definitions), and their steps are exactly their axioms.
- A term that fails to check is a reconstruction bug: the step is reported and the run fails. A `todo` step is accepted, with a warning.

### Lambdapi (`lambdapi.pl`)
Uses the `Stdlib` encoding of first-order logic.
- Input symbols are `{|f¹|}` (`{|f/n¹|}` if overloaded by arity), inputs `{|name²|}`, steps `{|name³|}`, definitions `{|P⁴|}`.
- A clause is stated with framework-level `Π`/`→`. `'$sym'`, `'$refl'` are `eq_sym`, `eq_refl _`; `'$dne'` is `¬¬ₑ F` with its formula explicit, as `π` reduces; `'$rewrite'` is `rw` (`rewrite` is a keyword), defined by `ind_eq`.
- Sorts are terms of `Set`; `'$inhabited'(S)` is `el S`. The prelude adds `∀ₜ`, `∃ₜ` over `Set` and `εₜ`, and the expansion rules as lemmas (classical ones from `Stdlib.Classic`), with `_t` variants over types.
- Skolem symbols get a rule `sK ↪ λ xs, ε (λ y, T)` (`Stdlib.Epsilon`); function and predicate definitions are rules too, so their axioms hold by `refl` or `∧ᵢ`.

### Agda (`agda.pl`)
For a hammer: a term to fill a hole, constructive by the A-translation.
- Output is `Proof.refutation bridge ... bridge where module Proof {R : Set} (leaf : type) ...`, one definition per clausal step. `R` is the IR's `⊥`, which Agda infers to be the goal; `~F` is `F → R`. The negated conjecture `G → R` is the identity.
- We expect one conjecture, a ground atom (or none), and input clauses. An input's Agda term is assumed to have type `∀ xs → A₁ → … → Aₙ → B₁ ⊎ … ⊎ Bₘ` for its negative literals `~Aᵢ` and positive `Bⱼ`, bridged in continuation-passing style.
- Names from the hammer are printed verbatim; the prover's own are escaped one to one (`spl0_1` is `spl0-1`, other characters `·HH·`), a definition of `P` is `Pᵈᵉᶠ`, and our own names are decorated with as few primes as avoid capture (`agda:decorate/0`).
- Assumed in scope: `_≡_`, `refl`, `sym`, `trans`, `cong`, `subst`, `⊥-elim`, `[_,_]′`. A rewrite of an equation is a path of `trans` and `cong`, whose sorts are given (`{A = …}`, `{B = …}`), as solving them by metas makes large proofs slower to check.
- Vampire's term-algebra rules for a constructor `C` are resolution with lemmas that are inputs, named after `C` and provided by the user of the proof (`vampire.pl`): `C-injI : ∀ xs ys → C(xs) = C(ys) → xI = yI` for positive injectivity (simplifying, and generating in argument `I`), and `C-cong : ∀ xs ys → x0 = y0 → … → C(xs) = C(ys)` for negative injectivity. Their steps are `injI_C` and `cong_C`.
- No λ is printed at a head, where the types of its binders would be metas that every check in the body waits on: a hypothesis λ given a proof or a path is a `let` that states its type, and a rewrite of a negated equation applied to a proof lengthens the path from that proof.
- Holes `{! !}`: `'$inhabited'(S)`, `todo` steps, steps between formulas (some are classical), and predicate bodies Agda cannot state; with `--complete`, an error instead. Everything is in `Set`.
- `agda_term` prints the same proof as one expression, for Agda's reflection (`checkFromStringTC`): the definitions of symbols are a `let`, and the steps are bound by `letp {type} (proof) λ step → …`, where `letp a k = k a` is assumed in scope; Agda substitutes a `let`, which would check a step once per citation, but does not unfold a definition. `agda_file` postulates the signature and inputs, with every name escaped, for testing.

### SMT-LIB (`smtlib.pl`)
In the manner of "Ground Truth" (Voronkov et al.): each step's ground premise instances and its negated conclusion, read off the proof term, form an unsatisfiable instance, one `push`/`check-sat`/`pop` per step, each with `(set-info :status unsat)`. Propositional and theory reasoning is left to the solver.
- Sorts are declared with their arity; polymorphic symbols are monomorphised per check (solvers lack `declare-sort-parameter`). Symbols are `|t.name|`, as cvc5 rejects clashes such as `exists` even when quoted.
- Not checked: `todo` steps (echoing a warning), steps between formulas (no ground instances), Skolem definitions and other definitions. Monomorphic definitions are `define-fun`s in the header, but splits with binders, asserted where used.
- A general split's component is asserted as `C => T`, sound by Skolemisation as for AVATAR.

## Files (`src/`)
| File | Role |
|---|---|
| `main.pl` | `main(Frontend, Backend, Options)`: loads every module, dispatches, exits with a status |
| `ops.pl` | Operators of the internal syntax |
| `load.pl` | `read_tstp/1`: `read/1` with TPTP operators, then normalisation |
| `db.pl` | The shared database, and `record/1` to add to it |
| `logic.pl` | Formulas and clauses |
| `signature.pl` | Symbol instances and sorts, typing equations, default sorts |
| `vampire.pl` | Vampire front end |
| `reconstruct.pl` | Proof search and the clausal tactics |
| `matching.pl` | Refuting a literal by a hypothesis, shared by the tactics |
| `normal.pl` | Keys of formulas for preprocessing |
| `transform.pl` | Tactics for steps between formulas |
| `rup.pl` | Reverse unit propagation |
| `close.pl` | Closing terms after search |
| `optimise.pl` | Optional inlining and simplification of the IR |
| `ir.pl` | The IR, and the types of steps and built-ins |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl`, `smtlib.pl`, `agda.pl` | Back ends |
| `printing.pl` | Shared printing DCGs |
| `utils.pl` | Portable helpers |

## Known Issues
- Back-end scaling: Lambdapi and Agda time out or run out of memory on some large proofs (`HWV057`, `SWV424-1.200`). Not our problem; report upstream if relevant.
- Our lambdapi printer builds its output in memory, and overflows the stack on SWV545-1.010's 885k-node terms.
- SYN986+1.004 blows the stack in `read/1` with its deep `succ` terms, but checks with `ulimit -s unlimited`.
- Some slowness during reconstruction, e.g. `PUZ135_1`'s self-superposition.
- cvc5 exits 0 on `unknown`, so `scripts/checksmt` would not notice a timeout.
- Scryer and Trealla no longer run isinglass (last ported in 979736d).

## Testing
Produce a corpus of TSTP proofs in `solutions/` if not already there.
The scripts in `scripts/` each take one file and are run from the top level, e.g. `scripts/genlp solutions/PUZ001+1`: `gen*` produce proofs via `ising` (or `check` just checks the corpus), and `check*` check the results.
All produce noisy output on failure and play well with GNU parallel.
