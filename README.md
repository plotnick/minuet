# Minuet: An Answer Set Programming System

🎼 Minuet is an early-stage (not yet α quality)
[Answer Set Programming](https://en.wikipedia.org/wiki/Answer_set_programming)
(ASP) system, roughly similar to (a small subset of)
[clingo](https://potassco.org/clingo/). It takes as input a logic program,
expressed in either [a modern, Python-inspired syntax](syntax/minuet1)
or ([eventually](syntax/asp_core2)) the
[ASP-Core-2](https://www.mat.unical.it/aspcomp2013/ASPStandardization)
syntax, grounds it, and computes the [stable models](https://en.wikipedia.org/wiki/Stable_model_semantics)
(aka "answer sets"), which are like the solutions to a Prolog query.
The program is expressed as a set of rules that may include
disjunctive heads, choice rules, aggregates, etc. See the resources at
[Potassco](https://potassco.org/) or [Lifschitz's book](doc/ASP.pdf)
for a thorough introduction to answer set programming.

The program may be parsed from a string as usual, or (for the
native Minuet syntax only) embedded in Rust code via a [procedural
macro](macro/macro.rs) that parses it at Rust compile-time.
The proc macro preserves input spans, so parse errors in your
embedded Minuet programs can often be precisely indicated by your
IDE via `rust-analyzer`.

After parsing, the program is grounded, in which all variables are
replaced with the constant values that they may be bound to. This
is currently the weakest part of Minuet: it grounds using the most
naïve strategy possible (viz., bind every variable to every possible
constant), which severely limits the size and kinds of logic programs
that it can handle. A new grounder based on
[Kaminski & Schaub](https://arxiv.org/abs/2108.04769)
is in progress as of June 2024.

After grounding, a few other meaning-preserving preprocessing steps are
performed to bring the program into a useful normal form, and then it is
compiled into an exact cover problem (again, naïvely; lots of low hanging
fruit there, too) and handed off to the solver to generate solutions,
which are checked for model stability and finally translated back into
answer sets. This effectively "evaluates" the original logic program,
but without anything resembling a traditional evaluator in sight.

The solver is implemented using Don Knuth's beautiful
[Dancing Cells](https://www.youtube.com/watch?v=PUJ_XdmSDZw&list=PLoROMvodv4rOAvKVR_dyCigSBMcYjevYB&index=25)
exact cover algorithm, a sort of sequel to his original
[Dancing Links](https://www.youtube.com/watch?v=_cR9zDlvP88&list=PLoROMvodv4rOAvKVR_dyCigSBMcYjevYB&index=2).
It has been stress-tested using the "extreme XC" problem of
[Knuth 7.2.2.1-(82)](doc/fasc7a.ps.gz): take all 2^_n_ - 1
possible options on _n_ primary items. For _n_ = 17, it found
82,864,869,804 solutions in about 200 hours on one core of
an Intel i9-13900K.

# Intended (Future) Use Cases

* Authorization, à la [Oso](https://github.com/osohq/oso)
* Planning, specifically for [updates to the Oxide rack](https://github.com/oxidecomputer/omicron/tree/main/nexus/reconfigurator/planning/src)
* Interactive REPL for experimentation
* General purpose embedded logic language
