# atp2itp: reconstruct once, emit many

`lp.pl` reads Vampire TSTP proofs, reconstructs each inference by backtracking search (literal matching, substitutions, AVATAR, RUP), and prints lambdapi, all in one pass. `src/` splits those jobs apart, so that more provers and more output formats (Lean, SMT-LIB "Ground Truth", Agda with the A-translation) can share one reconstruction:

**TSTP → front end + proof search → λ-term IR → back ends (including a type checker)**

## Constraints
- **Concise, maintainable Prolog.**
- **Reasonably portable Prolog; only SWI must run for now.**
  - Avoid SWI-only features: no SSU `=>`, no `format ~@`, no `sub_term/2`, no `string_*`, no `:- if`.
  - Printing is done with DCGs over code lists, emitted with `phrase/2` and `write/1`.
  - A few common non-ISO library predicates are used: `forall/2`, `msort/2`, `last/2`, `same_length/2`, `foldl/4`, `library(assoc)`.
- **Scryer is deferred.** Its strict reader rejects Vampire's SAT lines, e.g. `cnf(s1, plain, spl0_1 | spl0_2, inference(sat_conversion, ...))`. That is an unparenthesised priority-1102 term in argument position, which is invalid ISO even though it is valid TPTP; SWI accepts it. To be fixed upstream in Vampire.
  - Other Scryer findings, for later:
    - A prefix `!` operator breaks cuts.
    - Scryer has no `:- if` and no `consult/1` directive.
    - `phrase/3` needs `library(dcgs)`, and so does a variable DCG body, which becomes `phrase/3`.
    - Operator atoms must be parenthesised when used as operands: `C == (/)`.
    - A dynamic predicate imported into a second module is not visible there. Use static accessors, or `db:` qualification.
- **TSTP is read with `read/1`.** The TPTP operators are declared at run time in `load.pl`, so they don't affect how the code itself is parsed. Formulas are then normalised into a small internal syntax.
- **The IR is logic-agnostic and constructive** (see below). Back ends own every encoding decision.
- **The `test/` directory is not committed.** It holds a large, generated proof corpus.
- **Tests must cap memory.** lambdapi can exhaust the machine on big proofs; an uncapped run already caused a memout, and Vampire's default memory limit is 128 GB. The test scripts therefore use `ulimit -v` and Vampire's `-m`.

## Internal formula syntax (`src/ops.pl`, `src/load.pl`)
- Connectives: `~F`, `F | G`, `F & G`, `F => G`, `F <=> G`, plus `'$true'` and `'$false'`.
- Quantifiers: `'!'(Xs, F)` and `'?'(Xs, F)`.
- Atoms are Prolog terms, and `S = T` is equality.
- Normalisation on reading:
  - `S != T` becomes `~(S = T)`;
  - `F <= G` becomes `G => F`;
  - `F <~> G` becomes `~(F <=> G)`;
  - `~|` and `~&` become a negated `|` or `&`.
- Clauses are `clause(Xs, Literals)`: a plain list of literals `A` or `~A`.
- Front-end steps (`step/3`) and AVATAR definitions (`split/2`) keep Prolog variables, so each database lookup is a fresh instance and instantiation is unification. When a step is reconstructed, its conclusion is made rigid by numbering its variables `'$VAR'(N)` in binder order; the IR is ground.
- Vampire's AVATAR clause shape `(! [X] : C) | ~spl` is also recognised as a clause.

## The IR (`src/ir.pl`, `src/db.pl`)
```
ir_step(Name, Conclusion, Justification)     % in dependency order, reachable from the final $false
split(Symbol, Clause)                        % index of AVATAR definitions
Conclusion    ::= clause(Xs, Lits) | formula(F)
Justification ::= input(Role, Source) | split_def(Symbol, Clause) | proof(M) | todo(Record, Parents)
M ::= h(N)                 % a hypothesis
    | app(F, Ts, Ms)       % F applied to first-order terms Ts, then to proofs Ms
    | lam(X, T, M)         % X : T is h(N), or an eigenvariable '$VAR'(N) : '$i'
    | let(X, F, M, M')     % lemma X : F
F ::= h(N) | Name | '$sym' % '$sym' : ∀x y. x = y → y = x
```
**Proofs are λ-terms**, Curry–Howard style, in minimal logic with an abstract `⊥`.
- A clause `clause(Xs, [L₀…Lₙ₋₁])` has the type `Π xs. ¬L₀ → … → ¬Lₙ₋₁ → ⊥` (`ir:clause_type/2`), where `¬F` is `F → ⊥`. `M` is a closed term of that type.
- The hypothesis for a negative literal `~A` is honestly `¬¬A`, so `¬¬`-elimination is never needed, and the IR is sound under any reading of `⊥`:
  - classical falsity, for lambdapi, Lean and SMT;
  - the conjecture `G` of the A-translation, for Agda.
- Heads are variables or constants, so terms are β-normal apart from `let`.
- First-order arguments `Ts` are kept apart from proof arguments, so back ends can read premise instances without types.
- Built-ins are few: `'$sym'` now, and rewriting later.

**Split definitions.** A split symbol is a defined proposition: it unfolds to the type of its defining clause (δ-reduction, as lambdapi's `rule`).
- A hypothesis `H : ¬¬Split` is used as `H (λ d, d ts …)`.
- `H : ¬Split` is refuted by proving the definition, `H (λ xs hs, …)`, for eigenvariables `xs`.

**Checking.** The `checker` back end (`checker.pl`) is an independent type checker (about 60 lines) of each ground, fully annotated proof term against the ground type of its conclusion, step by step in order.
- The only Prolog variables it binds are the quantifier binders of fresh instances of steps, split definitions and `'$sym'`: to the ground terms `Ts`, or to eigenvariables under the λs of an unfolded split definition.
- First-order terms must be in scope: every `'$VAR'` is an eigenvariable bound by a λ.
- A step can only cite steps checked before it, so proofs are well-founded.
- A term that fails to check is a search bug: `run(checker)` reports the step and fails. Other back ends don't run the checker.

**Search** (`reconstruct.pl`) builds these terms directly, from hypotheses `X-Type`, annotating each λ with its binder's type as it is built. Annotations share variables with premise instances, so they are ground once the term is: binders are named `h(N)` after search, and leftover term variables become `'$inhabited'` (`close.pl`). The rule → search-procedure table is unchanged.

**Full formulas (M3).** Connective-level reasoning will add built-ins or term formers (pairs, injections, case analysis, ∃-elimination), each chosen to stay sound under the A-translation.

**Equality (M2).** Equality adds built-ins for rewriting and reflexivity.

## Files (`src/`)
| File | Role |
|---|---|
| `ops.pl` | Operators of the internal syntax, exported as a module |
| `load.pl` | `read_tstp/1`: `read/1` with run-time TPTP operators, followed by normalisation |
| `db.pl` | Shared dynamic facts: `step/3` (front-end output), `symbol/3`, `introduced/2`, `ir_step/3`, `split/2` |
| `logic.pl` | `formula_clause`, `clause_formula`, `complement`, `flip`, `number_vars`, `formula_symbol` |
| `vampire.pl` | Front end: maps Vampire rules to search procedures; `file`/AVATAR definitions. Unknown rules become `todo`. |
| `signature.pl` | Default sorts for symbols the front end has not declared, shared by all front ends |
| `reconstruct.pl` | Proof search, building λ-terms: `variant`, `resolve`, `rup`, `avatar_component`, `avatar_split`. Unit propagation is in `rup.pl`, and closing terms in `close.pl`. |
| `close.pl` | Closing a proof term after search: binders named `h(N)`, leftover term variables → `'$inhabited'`, assuming the sort is inhabited |
| `rup.pl` | Reverse unit propagation over ground clauses, building a chain of lemmas: used by `rup` |
| `ir.pl` | IR documentation; `clause_type`, the type of a clause |
| `checker.pl` | Type-checker back end (not `check`, which clashes with SWI's `library(check)`) |
| `lambdapi.pl` | lambdapi back end |
| `smtlib.pl` | SMT-LIB back end: one `push`/`check-sat`/`pop` per step, expecting `unsat` |
| `main.pl` | `run(Backend)`, where `Backend` is a back-end module |

Usage: `swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p`. The back end can be `lambdapi`, `smtlib` or `checker`.

Vampire rule → search procedure:
| Vampire rules | Procedure |
|---|---|
| resolution, forward/backward_subsumption_resolution | `resolve` |
| factoring, duplicate_literal_removal, sat_conversion, avatar_contradiction_clause, avatar_sat_refutation | `variant` |
| avatar_split_clause | `avatar_split` |
| avatar_component_clause | `avatar_component` |
| rat | `rup` |

A front end for another prover (e.g. E) would be a similar small table onto the same search procedures.

## Back-end encodings
**lambdapi.**
- **Statements:** a clause is stated as its IR type `Π xs, π (¬ L₀) → … → π ⊥`, using framework-level `Π`/`→` rather than `` `∀ ``/`⇒`. For a negative literal this is `π (¬ ¬ A)`.
- **Symbols:** `{|f¹|}`, or `{|f/2¹|}` for a name overloaded by arity (TPTP allows it, and Vampire prints both as `f`).
- **Proof terms** are printed directly. `'$sym'` is a prelude symbol `sym`.
- **Lets:** a `let` carries its type, and the binder of a λ value is annotated too. lambdapi does not use a let's type to elaborate its value, and inference was very slow without the annotation (PUZ017-1 went from 2 s to over 60 s).
- **Inputs:** declared as `{|name²|}` with their original formula. The clause is obtained by an `∨ₑ` chain.
- **AVATAR:** a split symbol is a `Prop` with `rule spl ↪ clause`.
- **Formulas:** parenthesised only where needed, using the priorities of the Stdlib notations.
- **Parentheses:** terms are printed bare, and parenthesised only as arguments.

**SMT-LIB.**
- Each step is checked by asserting the ground premise instances `app(Name, Ts, _)` of its proof term and the negated conclusion, with variables as fresh constants.
- AVATAR definitions are asserted as ground implications, using the binder types in the proof term: `spl ⇒ Cσ` when a definition is used, and `C[eigen] ⇒ spl` when one is introduced. The latter is sound by skolemisation.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted. A name overloaded by arity also gets its arity, `|t.f/2|`.
- `todo` steps are checked with universally quantified premises.

## Status: milestone 1 (CNF, no equality, plus AVATAR)
- **Corpus:** `test/corpus.sh` collects proofs of `Problems/*/*-*.p` whose Vampire proofs use only the rules above and no equality: 984 proofs.
- **Checking:** `test/check.sh` checks each proof:
  1. no `todo` steps, and `run(checker)` succeeds;
  2. z3 and cvc5 report `unsat` for every step;
  3. `lambdapi check` succeeds.
- **Result:** 975 of 984 pass.
  - The 9 failures are the largest proofs (lambdapi output 4–245 MB, e.g. HWV057, SWV424-1.200 and up). lambdapi times out or runs out of memory on them.
  - SWV424-1.450 also exceeds 60 s in Prolog: about 25 s reconstruction, 11 s checking, plus output.
- **λ-term IR (10 s timeouts, all 1245 `solutions/`):**
  - `run(checker)` succeeds on every proof.
  - lambdapi times out on 114 proofs, against 132 with the former tactic IR. No proof regressed.
  - The lambdapi output is about 18% larger, because of the `¬¬A` statements and the `λ k, k x` wrappers.
  - z3 reports `unsat` for every step of 40 sampled proofs.
  - On the three largest proofs (MSC015-1.015, SYN885-1, SWV424-1.200), the stored IR is −6% to +9% the size of the tactic IR, and `run(checker)` takes 10–60% longer: at most 5.9 s, for SWV424-1.200.
- **Sanity check:** every mutant of the proof terms of SYN015-2, SYN488-1 and small hand-made equality proofs was rejected (dropped or swapped arguments, wrong `'$sym'` order, wrong lemma type, wrong binder annotation). That was over 23000 mutants for SYN488-1. A bad term makes `run(checker)` fail with an error.
- **Symmetry:** the corpus has no equality, so `'$sym'` was tested on hand-made proofs covering both polarities, through lambdapi and z3.

## Known issues / notes for review
- **lambdapi scaling (upstream?).** Checking cost grows roughly as n⁴ in the number of hypotheses of a single declaration, even flat with all binders typed: n=150 takes 30–50 s. A 451-literal input clause (SWV424-1.450 `f452`) cannot be checked in 4 GB. lambdapi's `let` was also much worse than β-redexes, and a `cut` lemma was worse still.
- **Performance work done** (on 39k steps with 920k `rat` premise references):
  - `rup` keeps an assoc of false literals and a queue of those not yet propagated, re-checking only the clauses containing a newly false literal. Chopping false literals out of clauses was tried, and cost about 25% of the whole run on SWV424-1.200, because each chop updates the clause in an assoc.
  - `split/2` indexes AVATAR definitions.
  - The checker context is an assoc.
  - Clauses are stored with Prolog variables, so premise instances are database copies rather than substitutions (about 1.5–2× faster reconstruction).
- **Remaining cost:** the remaining reconstruction cost is spread over assoc and database lookups. A cheaper index for repeated `rat` premise sets is possible.
- **`avatar_component`'s second clause** (`~L | split`, closed by two complementary hypotheses) is exercised by the corpus, e.g. SYN488-1 `f614`.
- **Resolution search:** as in `lp.pl`, `resolve` lets the minor premise refute only positive literals of the major; both premises are tried as major, so this is complete.
  - Allowing either polarity made the search exponential on wide, mostly-negative clauses: SYO656-1 (27-literal premises, 6 variables) did not finish, and SYO673-1 took 12 s instead of 0.5 s.
  - Literal matching is still naive, in a fixed literal order; matching the most constrained literal first would help if wider clauses blow up again.
- **Proof assistants installed:** lambdapi 3.0.0 + Stdlib, z3, cvc5 and Agda. Lean is not installed yet.

## Next
- **M2: equality.**
  - Add rewriting/reflexivity built-ins to the IR.
  - Tactics for superposition, forward/backward_demodulation, reorient_equations, trivial_inequality_removal and equality_resolution/factoring, using `lp.pl`'s `replace/5` approach.
  - A Lean 4 back end.
- **M3: full formulas.**
  - FOF preprocessing (negated_conjecture, ennf/nnf/cnf_transformation, skolemisation, definitions).
  - Port Agda with the A-translation.
  - Another prover front end.
- **Scryer:** revisit once Vampire parenthesises its SAT lines.
- **Possibly:** a standalone lambdapi reproducer for the scaling issue.
