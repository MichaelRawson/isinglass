# atp2itp: reconstruct once, emit many

`lp.pl` reads Vampire TSTP proofs, reconstructs each inference by backtracking search (literal matching, substitutions, AVATAR, RUP), and prints lambdapi, all in one pass. `src/` splits those jobs apart, so that more provers and more output formats (Lean, SMT-LIB "Ground Truth", Agda with the A-translation) can share one reconstruction:

**TSTP → front end + generic tactics → sketch → elaboration (checker) → IR → back ends**

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
Justification ::= input(Role, Source) | split_def(Symbol, Clause) | refute(R) | todo(Record, Parents)
R   ::= use(P, Ts, [arg(L, A)])  % instantiate premise clause P with Ts; A refutes literal L
      | let(H, L, arg(L, A), R)  % lemma H : ¬L
      | contra(H, K, arg(K', A)) % H : ¬K, and A refutes its complement K'
P   ::= Name                     % a step
      | def(H, Split)            % the definition of Split, from H : ¬~Split
A   ::= hyp(H) | sym(F, H) | assume(H, R)   % sym: H : ¬F, F the flipped L
      | intro(Xs, Hs, R)         % L = ~Split: prove Split's defining clause for eigenvariables Xs
```
Tactics produce a *sketch*: the same term without annotations (`arg(L, A)` becomes `A`, `sym(F, H)` becomes `sym(H)`, `contra` drops `K`, `def(H, Split)` becomes `H`).

**Semantics.** A refutation derives an abstract `⊥` from one hypothesis `h(I) : ¬L_I` per conclusion literal, where `¬L` means "L implies ⊥". The IR never uses `¬¬`-elimination. So it is sound under any reading of `⊥`:
- classical falsity, for lambdapi, Lean and SMT;
- the conjecture `G` of the A-translation, for Agda.

**Split definitions.** A split symbol is read as its defining clause, `Π xs, ¬L₀ → … → ⊥`. A hypothesis `H : ¬~Split` gives only `¬¬Split`, but formulas ending in `⊥` are `¬¬`-stable in minimal logic, so `use(def(H, Split), …)` is constructive. Dually, `intro` refutes `~Split` by proving `Split`. `~Split` can also be refuted propositionally by `assume`, treating `Split` as an atom, as RUP does.

**Checking.** `ir:elaborate/3` is an independent checker, kept separate from the tactics' search. During reconstruction it checks each tactic's sketch and annotates it, producing the stored IR; a sketch that fails to check is a tactic bug, and stops the run with an error. Back ends read the IR directly. `run(check)` just loads and reconstructs the proof, which elaborates every step.

**Full formulas (M3).** "Refute a premise literal" generalises to "refute a premise formula". `Arg` then grows connective-level constructors (`and`, `or`, `all(Term, ...)`, `ex(H, R)`, `imp`, `iff`, skolem), each chosen to stay sound under the A-translation.

**Equality (M2).** Equality adds `rw(Ctx, EqArg, Arg)` and `refl`.

## Files (`src/`)
| File | Role |
|---|---|
| `ops.pl` | Operators of the internal syntax, exported as a module |
| `load.pl` | `read_tstp/1`: `read/1` with run-time TPTP operators, followed by normalisation |
| `db.pl` | Shared dynamic facts: `step/3` (front-end output), `symbol/3`, `introduced/2`, `ir_step/3`, `split/2` |
| `logic.pl` | `clause_form`, `clause_formula`, `complement`, `flip`, `number_vars`, `symbols`, `split_def` |
| `vampire.pl` | Front end: maps Vampire rules to tactics; `file`/AVATAR definitions; default signature. Unknown rules become `todo`. |
| `reconstruct.pl` | Generic tactics: `variant`, `resolve`, `rup`, `avatar_component`, `avatar_split`. Also binder naming and leftover variables → `'$any'`. |
| `ir.pl` | IR documentation; elaboration of sketches (the checker) |
| `lambdapi.pl` | lambdapi back end |
| `smtlib.pl` | SMT-LIB back end: one `push`/`check-sat`/`pop` per step, expecting `unsat` |
| `main.pl` | `run(Backend)`; `run(check)` only loads and reconstructs |

Usage: `swipl -g 'run(lambdapi)' -t halt src/main.pl < proof.p`. The back end can be `lambdapi`, `smtlib` or `check`.

Vampire rule → tactic:
| Vampire rules | Tactic |
|---|---|
| resolution, forward/backward_subsumption_resolution | `resolve` |
| factoring, duplicate_literal_removal, sat_conversion, avatar_contradiction_clause, avatar_sat_refutation | `variant` |
| avatar_split_clause | `avatar_split` |
| avatar_component_clause | `avatar_component` |
| rat | `rup` |

A front end for another prover (e.g. E) would be a similar small table onto the same tactics.

## Back-end encodings
**lambdapi.**
- **Statements:** a clause is stated as `Π xs, π H₀ → … → π ⊥`, using framework-level `Π`/`→` rather than `` `∀ ``/`⇒`. The hypothesis `H` for a positive literal `A` is `¬ A`, and for a negative `~A` it is `A`, as in `lp.pl`.
- **Indirect values:** an `assume` on a negative literal, and a RUP lemma about one, only provide `¬¬A`. Such values are passed in continuation-passing style, `n (λ (c : π A), P … c …)`, which is constructive because the goal is `⊥`.
- **Inputs:** declared as `{|name²|}` with their original formula. The clause is obtained by an `∨ₑ` chain.
- **AVATAR:** a split symbol is a `Prop` with `rule spl ↪ clause`.
- **Formulas:** parenthesised only where needed, using the priorities of the Stdlib notations.
- **Lemmas:** a `let` is printed as lambdapi's `let h ≔ v in …`, for readability (β-redexes were tried for performance, see below).
- **Parentheses:** refutations and values are printed bare, and parenthesised only as arguments, or as heads when they are λs.

**SMT-LIB.**
- Each step is checked by asserting the ground premise instances from its `use`s and the negated conclusion, with variables as fresh constants.
- AVATAR definitions are asserted as ground implications: `spl ⇒ Cσ` when a definition is used, and `C[eigen] ⇒ spl` when one is introduced. The latter is sound by skolemisation.
- Symbols are namespaced as `|t.name|`, because cvc5 rejects clashes such as `exists` even when quoted.
- `todo` steps are checked with universally quantified premises.

## Status: milestone 1 (CNF, no equality, plus AVATAR)
- **Corpus:** `test/corpus.sh` collects proofs of `Problems/*/*-*.p` whose Vampire proofs use only the rules above and no equality: 984 proofs.
- **Checking:** `test/check.sh` checks each proof:
  1. no `todo` steps, and `run(check)` succeeds;
  2. z3 and cvc5 report `unsat` for every step;
  3. `lambdapi check` succeeds.
- **Result:** 975 of 984 pass.
  - The 9 failures are the largest proofs (lambdapi output 4–245 MB, e.g. HWV057, SWV424-1.200 and up). lambdapi times out or runs out of memory on them.
  - SWV424-1.450 also exceeds 60 s in Prolog: about 25 s reconstruction, 11 s checking, plus output.
- **Sanity check:** deliberately corrupted IR steps (a dropped argument, a wrong annotation, a wrong `contra` literal) were rejected by the former IR re-check, and a bad sketch stops reconstruction with an error.

## Known issues / notes for review
- **lambdapi scaling (upstream?).** Checking cost grows roughly as n⁴ in the number of hypotheses of a single declaration, even flat with all binders typed: n=150 takes 30–50 s. A 451-literal input clause (SWV424-1.450 `f452`) cannot be checked in 4 GB. lambdapi's `let` was also much worse than β-redexes, and a `cut` lemma was worse still.
- **Performance work done** (on 39k steps with 920k `rat` premise references):
  - `rup` uses an assoc trail plus occurrence lists, re-checking only clauses containing a newly falsified literal.
  - `split/2` indexes AVATAR definitions.
  - The checker context is an assoc.
  - Clauses are stored with Prolog variables, so premise instances are database copies rather than substitutions (about 1.5–2× faster reconstruction).
- **Remaining cost:** the remaining reconstruction cost is spread over assoc and database lookups. A cheaper index for repeated `rat` premise sets is possible.
- **`avatar_component`'s second clause** (`~L | split`, closed by `mate`) is exercised by the corpus, e.g. SYN488-1 `f614`. It produces `contra` with `hyp`; nothing produces `contra` with `sym` or `assume` yet.
- **Resolution search:** as in `lp.pl`, `resolve` lets the minor premise refute only positive literals of the major; both premises are tried as major, so this is complete.
  - Allowing either polarity made the search exponential on wide, mostly-negative clauses: SYO656-1 (27-literal premises, 6 variables) did not finish, and SYO673-1 took 12 s instead of 0.5 s.
  - Literal matching is still naive, in a fixed literal order; matching the most constrained literal first would help if wider clauses blow up again.
- **Proof assistants installed:** lambdapi 3.0.0 + Stdlib, z3, cvc5 and Agda. Lean is not installed yet.

## Next
- **M2: equality.**
  - Add `rw`/`refl` to the IR.
  - Tactics for superposition, forward/backward_demodulation, reorient_equations, trivial_inequality_removal and equality_resolution/factoring, using `lp.pl`'s `replace/5` approach.
  - A Lean 4 back end.
- **M3: full formulas.**
  - FOF preprocessing (negated_conjecture, ennf/nnf/cnf_transformation, skolemisation, definitions).
  - Port Agda with the A-translation.
  - Another prover front end.
- **Scryer:** revisit once Vampire parenthesises its SAT lines.
- **Possibly:** a standalone lambdapi reproducer for the scaling issue.
