# Thermodynamic.lean

This is a project formalizing some of the bases of thermodynamics with [Lean theorem prover](https://leanprover.github.io/) and [mathlib](https://leanprover-community.github.io/).

The main goal of the project is to precisely state the axioms that are essential to building up the thermodynamics we want. The stuff I have already formalized can be summarized as
* The zeroth law
* Thermodynamic cycles and the first law
* Kelvin-Plank statement, Clausius statement, and Carnot theorem
* The construction of thermodynamic temperature

One can read the source codes in the [src](src) folder in the following order
1. [zeroth_law.lean](src/zeroth_law.lean)
1. [cycle.lean](src/cycle.lean)
1. [second_law.lean](src/second_law.lean)
1. [temperature.lean](src/temperature.lean)
