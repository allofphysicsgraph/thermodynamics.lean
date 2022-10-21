/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import data.real.ereal

/-!
# The ZEROTH Law

This file defines
* the notion of mutual thermodynamics equilibriumm, i.e. `mutual_equil`
* the notion of abstract heat `reservoir`
and states
* the axioms of the zeroth law, including
  `mutual_equil.eqv` : `mutual_equil` is an equivalence relation, and
  `reservoir.linear_order` : there is a linear order defined on `reservoir`
-/

namespace thermodynamics

constant equil_system : Type
constant water_triple_point : equil_system
noncomputable instance : inhabited equil_system := ⟨water_triple_point⟩

constant mutual_equil : equil_system → equil_system → Prop
/--
* The core axiom is the transitivity of `mutual_equil`.
-/
axiom mutual_equil.eqv : equivalence mutual_equil
noncomputable instance : setoid equil_system :=
  { r := mutual_equil,
    iseqv := mutual_equil.eqv }
--

/-- Identify the equivalence classes of `mutual_equil` with heat `reservoir`s.
    `reservoir` is abbreviated as `rsv`,
    and a certain rsv is denoted by script uppercase letters like `𝓣`. -/
@[reducible] def reservoir := quotient equil_system.setoid
/--
* `<` means "colder than".
* The core axiom is the existence of a order and its transitivity.
-/
@[instance] axiom reservoir.linear_order : linear_order reservoir

end thermodynamics
