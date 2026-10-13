# Isinglass

Various [automated theorem provers](https://en.wikipedia.org/wiki/Automated_theorem_proving) (ATP) output proofs in the standard [TSTP](https://tstp.tptp.org/) format.
Unfortunately this only specifies the syntax and the logical relation between different parts of the proof: the actual steps are left up to the systems.
In practice, systems give relatively rigorous proofs using variations on well-known inference rules, but leave out fine details like substitution, variable renaming, permutation of literals, etc.
If you want to formally check ATP proofs, or even use them as part of a larger formal proof, you will need to translate the ATP proof, elaborating the detail left out by the ATP.

_Isinglass_ attempts to do this for many ATPs and output formats at once, in a similar way to [LLVM](https://en.wikipedia.org/wiki/LLVM).
Adding an ATP such as Vampire means mapping its dialect of TSTP into a DAG of formulas derived from others by _tactics_.
Tactics are independent of any particular ATP system's inference rules but are similar in spirit.
For example, the `resolution` tactic encompasses Vampire's `binary resolution`, `forward subsumption resolution`, and `backward subsumption resolution` inference rules.

Once the DAG is loaded, the tactics are invoked for each step to _reconstruct_ the details.
These details are kept in an intermediate representation (IR).
Backends like `lambdapi` then need only project out the parts they need from the (very detailed) IR.

Isinglass is currently intended for first-order ATP proofs, i.e. up to TFF1 in the TSTP language.

## Frontend (ATP systems)
- [Vampire](https://github.com/vprover/vampire/) (`vampire`)

## Backends
- A built-in proof checker, (`checker`).
- [lambdapi](https://lambdapi.readthedocs.io/en/latest/), (`lambdapi`)
- SMT-LIB for checking by SMT solvers, in the style of "Ground Truth" (`smtlib`).
- constructive Agda (`agda`, supporting only clausal proofs)

## Usage
Isinglass is written in Prolog, for very good reasons.
Unfortunately, this means you will need a Prolog interpreter to run the program.
I use [SWI](https://www.swi-prolog.org/) for development, but I have also tested it with [Scryer](https://www.scryer.pl/) and [Trealla](https://github.com/trealla-prolog/trealla-prolog) in the recent past.
Other Prolog implementations may also work.

I have provided a shell script `ising` that assumes SWI.
It takes two arguments: the frontend and the backend.
TSTP proofs should be read on standard input.
For example:
```
vampire -p tptp Problems/PUZ/PUZ001+1.p | ./ising vampire lambdapi
```
produces a lambdapi script from the supplied Vampire proof of `PUZ001+1`.

## Bugs, Limitations and Extensions
Isinglass is at an early stage of development.
Items that are still missing that I would like at some point:
- support for Skolemisation
- support for all of Vampire's output, including non-default options
- arithmetic and theories (including datatypes)
- other ATP systems
- the internal formula language rewrites unusual TSTP operators to a more standard form, e.g. `~(p | q)` for `p ~| q` at load time, which it technically shouldn't
- improved error handling
- higher-order logic (?!)

Bugs are no doubt manifest.

## Development
In the interest of speed, much of this has been developed by LLM, but with significant human oversight.
The code is reviewed, but currently not of the best quality; one of the virtues of producing formally-checked scripts is that we can still be confident in the correctness of a proof!

See [DESIGN.md](DESIGN.md) for some notes on the layout of the program.

--------------------

Naming: [isinglass](https://en.wikipedia.org/wiki/Isinglass) is used in traditional beer (wine) manufacture to _clarify_ murky beer.
Of course, using isinglass does not significantly change the [proof](https://en.wikipedia.org/wiki/Alcohol_proof).
Not to be confused with [ising.pl](https://ising.pl/), a popular platform for Polish karaoke enthusiasts.
