/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import cycle

/-!
# The SECOND Law and Carnot Theorem

This file defines
* the notion of `cycle`'s satisfying the second law, i.e. `cycle.possible`
* the notion of reversible `cycle`, i.e. `cycle.reversible`
and states
* axioms stating the possibility of some types of `cycle`s, including
  `cycle.trivial_possible`,
  `one_rsv_cycle.exists_possible_dissipate'`, `abs_rel_cycle.exists_possible_transfer'`,
  `usual_engine_cycle.exists_possible`, `usual_pump_cycle.exists_possible`
* axioms stating that connection and scaling preserve the possibility of `cycle`s,
  i.e. `cycle.possible_add` and `cycle.possible_smul_nonneg`
* the axiom of the second law, i.e. `kelvin_stmt`
and proves
* the equivalence of Kelvin-Plank statement and Clausius's statement
* the equivalence of Clausius's statement and Carnot theorem
-/

namespace thermodynamics

/-!
## `possible` `cycle`s
---------------------------------------------------------------------------------------------------/

namespace cycle

/-- abstract `cycle` that is possible according to the second law -/
constant possible : cycle → Prop
/-- The trivial `cycle` is possible. -/
axiom trivial_possible : (0:cycle).possible

/-- The connection of two possible `cycle`s is possible.
* Note that a connection of possible and impossible can be possible.
-/
axiom possible_add {H₁ H₂ : cycle} : H₁.possible → H₂.possible → (H₁ + H₂).possible
/-- The scaling a possible `cycle` with nonnegative is possible. -/
axiom possible_smul_nonneg {c : ℝ} {H : cycle} : 0 ≤ c → H.possible → (c • H).possible

end cycle

/-!
### `one_rsv_cycle`
-/

namespace one_rsv_cycle
variables {𝓣 : reservoir}

/-- There exists possible `one_rsv_cycle 𝓣` that `dissipate`s work into heat. -/
axiom exists_possible_dissipate' : ∃ H : one_rsv_cycle 𝓣, H.possible ∧ H.𝓦 < 0

/- /-- There exists possible `one_rsv_cycle 𝓣` that dissipates a certain work `W > 0`. -/
lemma exists_psbl_dissi {W : ℝ} (hW : 0 < W) :
  ∃ H : one_rsv_cycle 𝓣, H.possible ∧ H.𝓦 = W := sorry -/

end one_rsv_cycle

/-!
### `abs_rel_cycle`
-/

namespace abs_rel_cycle
variables {𝓗 𝓒 : reservoir}

/-- There exists possible `abs_rel_cycle` that
    abs from hotter `𝓗` and fully `transfer`s it to colder `𝓒`. -/
axiom exists_possible_transfer' (𝓒_lt_𝓗 : 𝓒 < 𝓗) :
  ∃ H : abs_rel_cycle 𝓗 𝓒, H.possible ∧ (H.Qabs:ℝ) = H.Qrel
--

/- /-- There exists possible `abs_rel_cycle 𝓗 𝓒` that transfers a certain heat `Q > 0`. -/
lemma exists_psbl_trans (𝓒_lt_𝓗 : 𝓒 < 𝓗) {Q : ℝ} (hQ : 0 < Q) :
  ∃ H : abs_rel_cycle 𝓗 𝓒, H.possible ∧ (H.Qabs:ℝ) = H.Qrel ∧ ↑H.Qabs = Q := sorry -/

end abs_rel_cycle

/-!
### `usual_engine_cycle`
-/

namespace usual_engine_cycle
variables {𝓗 𝓒 : reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

/-- There exists a possible `usual_engine_cycle` between any `𝓒 < 𝓗`. -/
axiom exists_possible : ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.possible

variables {Q : ℝ} (hQ : 0 < Q)
/-- There exists possible `usual_engine_cycle 𝓒_lt_𝓗` that absorbs a certain heat `Q > 0`. -/
lemma exists_psbl_abs : ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.possible ∧ ↑H.Qabs = Q :=
  let ⟨H', hH'⟩ := exists_possible 𝓒_lt_𝓗 in
  let c : ℝ₊ := ⟨Q / H'.Qabs, div_pos hQ H'.do_abs⟩ in
  let H := c • H' in
  ⟨ H,
    cycle.possible_smul_nonneg (le_of_lt c.property) hH',
    calc ↑H.Qabs
         = Q / H'.Qabs * H'.Qabs : cycle.Qabs_smul_pos c.property
      ...= Q                     : div_mul_cancel _ (ne_of_gt H'.do_abs), ⟩
/-- There exists possible `usual_engine_cycle 𝓒_lt_𝓗` that releases a certain heat `Q > 0`. -/
lemma exists_psbl_rel : ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.possible ∧ ↑H.Qrel = Q :=
  let ⟨H', hH'⟩ := exists_possible 𝓒_lt_𝓗 in
  let c : ℝ₊ := ⟨Q / H'.Qrel, div_pos hQ H'.do_rel⟩ in
  let H := c • H' in
  ⟨ H,
    cycle.possible_smul_nonneg (le_of_lt c.property) hH',
    calc ↑H.Qrel
         = Q / H'.Qrel * H'.Qrel : cycle.Qrel_smul_pos c.property
      ...= Q                     : div_mul_cancel _ (ne_of_gt H'.do_rel), ⟩
--

end usual_engine_cycle

/-!
### `usual_pump_cycle`
-/

namespace usual_pump_cycle
variables {𝓒 𝓗 : reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

/-- There exists a possible `usual_pump_cycle` between any `𝓒 < 𝓗`. -/
axiom exists_possible : ∃ H : usual_pump_cycle 𝓒_lt_𝓗, H.possible

variables {W : ℝ} (hW : 0 < W)
/-- There exists possible `usual_pump_cycle 𝓒_lt_𝓗` that consumes a certain work `W > 0`. -/
lemma exists_psbl_consume : ∃ H : usual_pump_cycle 𝓒_lt_𝓗, H.possible ∧ H.𝓦 = -W :=
  let ⟨H', hH'⟩ := exists_possible 𝓒_lt_𝓗 in
  let c : ℝ₊ := ⟨W /(-H'.𝓦), div_pos hW (neg_pos_of_neg H'.consume_work)⟩ in
  let H := c • H' in
  ⟨ H,
    cycle.possible_smul_nonneg (le_of_lt c.property) hH',
    calc H.𝓦
         = W /(-H'.𝓦) * H'.𝓦 : cycle.𝓦_smul
      ...= (-W)/ H'.𝓦 * H'.𝓦 : by rw [div_neg, ←neg_div]
      ...=  -W                 : div_mul_cancel _ (ne_of_lt H'.consume_work), ⟩
--

end usual_pump_cycle

/-!
## `reversible` `cycle`s

* Since an abstract `cycle` is an equivalence class, that it is reversible means
  that there exists a reversible concrete cycle in these class, such as Carnot cycle.
* Note that a concrete cycle in a reversible-`cycle` eqv class is not neccesarily reversible.
---------------------------------------------------------------------------------------------------/

namespace cycle
variables (H : cycle)

def reversible  := H.possible ∧ (-H).possible
-- def psbl_nonrev := H.possible ∧ ¬(-H).possible

lemma trvial_reversible : (0:cycle).reversible :=
  ⟨trivial_possible, by{rw (@neg_zero cycle _), exact trivial_possible}⟩
lemma reversible_add  {H₁ H₂ : cycle} : H₁.reversible → H₂.reversible → (H₁ + H₂).reversible :=
  assume ⟨h₁psbl, h₁rev⟩ ⟨h₂psbl, h₂rev⟩, by {
  split,
  { exact possible_add h₁psbl h₂psbl, },
  { have : -(H₁ + H₂) = -H₁ + -H₂, rw [neg_add_rev, add_comm], rw this,
    exact possible_add h₁rev h₂rev, } }
lemma reversible_smul_nonneg {c : ℝ} {H : cycle} : 0 ≤ c → H.reversible → (c • H).reversible :=
  assume hc ⟨hpsbl, hrev⟩, by {
  split,
  { exact possible_smul_nonneg hc hpsbl, },
  { have : -(c • H) = c • (-H), rw [smul_neg], rw this,
    exact possible_smul_nonneg hc hrev, } }
--

end cycle

/-!
## Kelvin and Clausius statements
---------------------------------------------------------------------------------------------------/

/-- Kelvin-Plank statement : `one_rsv_cycle` cannot do work. -/
@[reducible] def kelvin_stmt' :=
  ∀ 𝓣, ∀ H : one_rsv_cycle 𝓣, 0 < H.𝓦 → ¬H.possible
/-- Clausius statement : Heat cannot be fully transfered from colder rsv `𝓒` to hotter rsv `𝓗`. -/
@[reducible] def clausius_stmt' :=
  ∀ 𝓒 𝓗, (𝓒 < 𝓗) → ∀ H : abs_rel_cycle 𝓒 𝓗, (H.Qabs:ℝ) = H.Qrel → ¬H.possible
--

theorem kelvin_then_clausius : kelvin_stmt' → clausius_stmt' := by {
  -- `K` < kelvin, `C` < clausius
  assume hKelvin, apply @by_contra clausius_stmt',
  simp only [not_forall, not_not, exists_prop, forall_exists_index, and_imp],
  assume 𝓣 𝓗 𝓣_lt_𝓗, assume CH hCH_Q hCH,
  exact
  let ⟨eng, heng, hQ⟩ := usual_engine_cycle.exists_psbl_abs 𝓣_lt_𝓗 CH.do_rel in
  let KH' := CH.to_cycle + eng.to_cycle in
  let KH : one_rsv_cycle 𝓣 :=
    { one_rsv := by {
        have : KH'.𝓠 = CH.𝓠 + eng.𝓠, from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_singleton, ne.def, forall_eq],
          calc CH.𝓠 𝓣 + eng.𝓠 𝓣
               = CH.Qabs  - eng.Qrel : by simp only [CH.Qabs_one_rsv, eng.Qrel_one_rsv,
                                                     sub_neg_eq_add]
            ...= eng.Qabs - eng.Qrel : by simp only [hCH_Q, hQ]
            ...= eng.𝓦              : by rw eng.𝓦_from_Qabs_Qrel
            ...≠ 0                   : ne_of_gt eng.do_work, },
        { have : (CH.𝓠.support ∪ eng.𝓠.support) \ {𝓣} = {𝓗}, {
            rw [CH.two_rsv.elim_left, eng.two_rsv.elim_left],
            ext, simp, split,
              tauto,
              assume this, exact ⟨or.inl this, ne_of_eq_of_ne this eng.two_rsv.elim_right⟩, },
          rw this,
          simp only [finset.mem_singleton, forall_eq],
          calc CH.𝓠 𝓗 + eng.𝓠 𝓗
               = -CH.Qrel + eng.Qabs : by simp only [CH.Qrel_one_rsv, eng.Qabs_one_rsv, neg_neg]
            ...= 0                   : by simp only [hQ, add_left_neg], } },
      ..KH' } in by {
  have : KH.possible, from cycle.possible_add hCH heng,
  refine absurd this (hKelvin _ KH _),
  calc KH.𝓦
       = CH.𝓦             + eng.𝓦 : cycle.𝓦_add
    ...= CH.Qabs - CH.Qrel + eng.𝓦 : by rw CH.𝓦_from_Qabs_Qrel
    ...=                     eng.𝓦 : by simp only [hCH_Q, sub_self, zero_add]
    ...>                     0      : eng.do_work, } }
-- #print axioms kelvin_then_clausius

/-- `reservoir` does not have a minimal element,
    which implies that the absolute zero cannot exist as a `reservoir`. -/
@[reducible] def rsv_no_min' := ∀ 𝓣 : reservoir, ∃ 𝓒, 𝓒 < 𝓣
theorem clausius_then_kelvin : rsv_no_min' → clausius_stmt' → kelvin_stmt' := by {
  -- `K` < kelvin, `C` < clausius
  assume rsv_no_min,
  assume hClausius, apply @by_contra kelvin_stmt',
  simp only [not_forall, not_not, exists_prop, forall_exists_index, and_imp],
  assume 𝓣, assume KH hKH_𝓦 hKH,
  exact
  let ⟨𝓒, 𝓒_lt_𝓣⟩ := rsv_no_min 𝓣 in
  let ⟨pump, hpump, hW⟩ := usual_pump_cycle.exists_psbl_consume 𝓒_lt_𝓣 hKH_𝓦 in
  let CH' := KH.to_cycle + pump.to_cycle in
  have KH_no_𝓒 : KH.𝓠 𝓒 = 0, from by {
    have : 𝓒 ∉ KH.𝓠.support, simp [KH.one_rsv, ne_of_lt 𝓒_lt_𝓣],
    exact (finsupp.not_mem_support_iff).elim_left this, },
  have do_abs_rsv :_ :=
    calc CH'.𝓠 𝓒
         = KH.𝓠 𝓒 + pump.𝓠 𝓒 : rfl
      ...= 0      + pump.Qabs : by rw [KH_no_𝓒, pump.Qabs_one_rsv]
      ...> 0                  : by simp [pump.do_abs],
  have do_rel_rsv :_ :=
    calc CH'.𝓠 𝓣
         = KH.𝓠 𝓣 + pump.𝓠 𝓣   : rfl
      ...= -pump.𝓦 - pump.Qrel : by simp [KH.𝓦_conv_one_rsv, hW, pump.Qrel_one_rsv]
      ...= -pump.Qabs           : by simp [pump.𝓦_from_Qabs_Qrel]
      ...< 0                    : by simp [pump.do_abs],
  let CH : abs_rel_cycle 𝓒 𝓣 :=
    { two_rsv := by {
        refine ⟨_, ne_of_lt 𝓒_lt_𝓣⟩,
        have : CH'.𝓠 = KH.𝓠 + pump.𝓠, from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
          split,
            exact ne_of_gt do_abs_rsv,
            exact ne_of_lt do_rel_rsv, },
        { have : (KH.𝓠.support ∪ pump.𝓠.support) \ {𝓒, 𝓣} = ∅, {
            rw [KH.one_rsv, pump.two_rsv.elim_left],
            ext, simp, tauto, },
          rw this,
          simp only [finset.not_mem_empty, is_empty.forall_iff, implies_true_iff], } },
      do_abs_rsv := do_abs_rsv,
      do_rel_rsv := do_rel_rsv,
      ..CH' } in by {
  have : CH.possible, from cycle.possible_add hKH hpump,
  refine absurd this (hClausius _ _ 𝓒_lt_𝓣 CH _),
  suffices : CH.𝓦 = 0, {
    rw CH.𝓦_from_Qabs_Qrel at this,
    exact sub_eq_zero.elim_left this, },
  calc CH.𝓦
       = KH.𝓦 + pump.𝓦 : cycle.𝓦_add
    ...= 0               : by simp only [hW, add_right_neg], } }
-- #print axioms clausius_then_kelvin

/-!
### Axioms of the second law
-/

axiom   kelvin_stmt   :
  ∀ {𝓣}, ∀ H : one_rsv_cycle 𝓣, 0 < H.𝓦 → ¬H.possible
theorem clausius_stmt :
  ∀ {𝓒 𝓗}, (𝓒 < 𝓗) → ∀ H : abs_rel_cycle 𝓒 𝓗, (H.Qabs:ℝ) = H.Qrel → ¬H.possible :=
  kelvin_then_clausius @kelvin_stmt
copy_doc_string kelvin_stmt'   → kelvin_stmt
copy_doc_string clausius_stmt' → clausius_stmt

/-!
## Carnot theorem
---------------------------------------------------------------------------------------------------/

/-- Carnot theorem : reversible `usual_engine_cycle` has the greatest efficiency. -/
@[reducible] def carnot_thm' :=
  ∀ 𝓒 𝓗 (𝓒_lt_𝓗 : 𝓒 < 𝓗), ∀ H C : usual_engine_cycle 𝓒_lt_𝓗,
  H.possible → C.reversible → H.eff ≤ C.eff
theorem clausius_then_carnot : clausius_stmt' → carnot_thm' := by {
  refine forall₃_imp _, assume 𝓒 𝓗 𝓒_lt_𝓗,
  assume hClausius,
  assume H C hH hC,
  by_contradiction heff, rw not_le at heff,
  let c : ℝ₊ :=
    { val := C.𝓦 / H.𝓦,
      property := div_pos C.do_work H.do_work },
  haveI : fact _ := ⟨c.property⟩,
  -- H'
  let H' := c • H,
  have H'𝓦eqC :=
    calc H'.𝓦
         = C.𝓦 / H.𝓦 * H.𝓦 : cycle.𝓦_smul
      ...= C.𝓦               : div_mul_cancel _ (ne_of_gt H.do_work),
  have this : C.eff / H.eff < 1, from (div_lt_one H.eff_pos).elim_right heff,
  have H'Qabs_ltC :=
    calc (H'.Qabs:ℝ)
         = H'.𝓦 / (c.val • H.to_cycle).eff : H'.Qabs_from_𝓦_eff
      ...= C.𝓦 / H.eff                     : by rw [H'𝓦eqC, cycle.eff_smul_pos]
      ...= C.eff / H.eff * C.Qabs           : by rw [C.𝓦_from_eff_Qabs, mul_div_right_comm]
      ...< C.Qabs                           : (mul_lt_iff_lt_one_left C.do_abs).elim_right this,
  have H'Qrel_gtC :=
    calc (H'.Qrel:ℝ)
         = H'.Qabs - H'.𝓦 : H'.Qrel_from_Qabs_𝓦
      ...< C.Qabs  - C.𝓦  : by simp only [H'Qabs_ltC, H'𝓦eqC, sub_lt_sub_iff_right]
      ...= C.Qrel          : C.Qrel_from_Qabs_𝓦.symm,
  -- ClH', `Cl` < clausius
  let ClH' := H'.to_cycle + C.rev.to_cycle,
  have rel𝓗 :=
    calc ClH'.𝓠 𝓗
         = H'.𝓠 𝓗 - C.𝓠 𝓗 : rfl
      ...= H'.Qabs - C.Qabs : by rw [H'.Qabs_one_rsv, C.Qabs_one_rsv]
      ...< 0                : sub_neg.elim_right H'Qabs_ltC,
  have abs𝓒 :=
    calc ClH'.𝓠 𝓒
         = H'.𝓠 𝓒 - C.𝓠 𝓒  : rfl
      ...= C.Qrel - H'.Qrel : by { rw [H'.Qrel_one_rsv, C.Qrel_one_rsv], ring }
      ...> 0                : sub_pos.elim_right H'Qrel_gtC,
  let ClH : abs_rel_cycle 𝓒 𝓗 :=
    { two_rsv := by {
        refine ⟨_, ne_of_lt 𝓒_lt_𝓗⟩,
        have : ClH'.𝓠 = H'.𝓠 + C.rev.𝓠, from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
          split,
            exact ne_of_gt abs𝓒,
            exact ne_of_lt rel𝓗, },
        { have : (H'.𝓠.support ∪ C.rev.𝓠.support) \ {𝓒, 𝓗} = ∅, {
            rw [H'.two_rsv.elim_left, C.rev.two_rsv.elim_left],
            ext, simp, },
          simp only [this, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff], } },
      do_abs_rsv := abs𝓒,
      do_rel_rsv := rel𝓗,
      ..ClH' },
  have this :=
    calc ClH.Qabs.val
         = ClH.𝓦                           + ClH.Qrel : ClH.Qabs_from_𝓦_Qrel
      ...= H'.𝓦 + (        -C.to_cycle).𝓦 + ClH.Qrel : by { rw cycle.𝓦_add, refl }
      ...=  C.𝓦 + ((-1:ℝ) • C.to_cycle).𝓦 + ClH.Qrel : by rw [H'𝓦eqC, neg_one_smul]
      ...=                                    ClH.Qrel : by { rw cycle.𝓦_smul, ring },
  refine absurd _ (hClausius ClH this),
  exact cycle.possible_add
    (cycle.possible_smul_nonneg (le_of_lt c.property) hH)
    (hC.elim_right), }
-- #print axioms clausius_then_carnot

/-- There exists a reversible `usual_engine_cycle` between any `𝓒 < 𝓗`. -/
@[reducible] def usual_engine_cycle.exists_reversible' :=
  ∀ 𝓒 𝓗 (𝓒_lt_𝓗 : 𝓒 < 𝓗), ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.reversible
theorem carnot_then_clausius : usual_engine_cycle.exists_reversible' →
  carnot_thm' → clausius_stmt' := by {
  assume hexists_rev,
  refine forall₃_imp _, assume 𝓒 𝓗 𝓒_lt_𝓗,
  assume hCarnot,
  assume ClH hQ, -- `Cl` < clausius
  by_contradiction hClH,
  exact
  let ⟨C, hC⟩ := hexists_rev _ _ 𝓒_lt_𝓗 in by {
  let c : ℝ₊ :=
    { val := C.Qrel / 2 / ClH.Qabs,
      property := div_pos
        (div_pos C.do_rel zero_lt_two)
        (ClH.do_abs), },
  -- ClH'
  let ClH' := c • ClH,
  have ClH'no𝓦 :=
    calc ClH'.𝓦
         = (↑c • ClH.to_cycle).𝓦 : rfl
      ...= 0 : by{rw [cycle.𝓦_smul, ClH.𝓦_from_Qabs_Qrel, hQ], ring},
  have ClH'abs_ltCrel :=
    calc (ClH'.Qabs:ℝ)
         =                         ClH'.𝓠 𝓒 : ClH'.Qabs_one_rsv
      ...= C.Qrel / 2 / ClH.Qabs *  ClH.𝓠 𝓒 : rfl
      ...= C.Qrel / 2 : by rw [←ClH.Qabs_one_rsv, div_mul_cancel _ (ne_of_gt ClH.do_abs)]
      ...< C.Qrel     : div_lt_self C.do_rel one_lt_two,
  have hQ' :=
    calc (ClH'.Qabs:ℝ)
         = c * ClH.Qabs : cycle.Qabs_smul_pos c.property
      ...= c * ClH.Qrel : by rw hQ
      ...= ClH'.Qrel    : eq.symm $ cycle.Qrel_smul_pos c.property,
  -- CaH', `Ca` < carnot
  let CaH' := ClH'.to_cycle + C.to_cycle,
  have CaH'𝓦eqC : CaH'.𝓦 = C.𝓦, rw [cycle.𝓦_add, ClH'no𝓦, zero_add],
  have rel𝓒 :=
    calc CaH'.𝓠 𝓒
         = ClH'.𝓠 𝓒  + C.𝓠 𝓒 : rfl
      ...= ClH'.Qabs - C.Qrel : by rw [ClH'.Qabs_one_rsv, C.Qrel_one_rsv, sub_neg_eq_add]
      ...< 0                  : sub_neg.elim_right ClH'abs_ltCrel,
  have abs𝓗 :=
    calc CaH'.𝓠 𝓗
         = ClH'.𝓠 𝓗 + C.𝓠 𝓗  : rfl
      ...= -ClH'.Qrel + C.Qabs : by rw [ClH'.Qrel_one_rsv, neg_neg, C.Qabs_one_rsv]
      ...= C.𝓦 + (C.Qrel - ClH'.Qabs) : by{rw [hQ', C.Qabs_from_𝓦_Qrel], ring}
      ...>         C.Qrel - ClH'.Qabs  : (lt_add_iff_pos_left _).elim_right C.do_work
      ...> 0                           : sub_pos.elim_right ClH'abs_ltCrel,
  let CaH : usual_engine_cycle 𝓒_lt_𝓗 :=
    { two_rsv := by {
        refine ⟨_, ne_of_gt 𝓒_lt_𝓗⟩,
        have : CaH'.𝓠 = ClH'.𝓠 + C.𝓠, from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
          split,
            exact ne_of_gt abs𝓗,
            exact ne_of_lt rel𝓒, },
        { have : (ClH'.𝓠.support ∪ C.𝓠.support) \ {𝓗, 𝓒} = ∅, {
            rw [ClH'.two_rsv.elim_left, C.two_rsv.elim_left],
            ext, simp, },
          simp only [this, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff], } },
      do_abs_rsv := abs𝓗,
      do_rel_rsv := rel𝓒,
      do_work :=
        calc CaH'.𝓦
             = C.𝓦 : CaH'𝓦eqC
          ...> 0    : C.do_work,
      ..CaH' },
  have :=
    calc (CaH.Qabs:ℝ)
         = ClH'.𝓠 𝓗 + C.𝓠 𝓗 : by { rw CaH.Qabs_one_rsv, refl }
      ...= C.Qabs - ClH'.Qrel : by { rw [C.Qabs_one_rsv, ClH'.Qrel_one_rsv], ring }
      ...< C.Qabs             : sub_lt_self _ ClH'.do_rel,
  have :=
    calc CaH.eff
         = CaH.𝓦 / CaH.Qabs : rfl
      ...> C.𝓦 / C.Qabs : by { rw CaH'𝓦eqC, exact div_lt_div_of_lt_left C.do_work CaH.do_abs this}
      ...= C.eff         : rfl,
  refine absurd (hCarnot CaH C _ hC) (not_le_of_gt this),
  exact cycle.possible_add
    (cycle.possible_smul_nonneg (le_of_lt c.property) hClH)
    (hC.elim_left), } }
-- #print axioms carnot_then_clausius

section carnot_thm
variables {𝓒 𝓗 : reservoir} {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H C : usual_engine_cycle 𝓒_lt_𝓗}

theorem carnot_thm : H.possible → C.reversible → H.eff ≤ C.eff :=
  (clausius_then_carnot @clausius_stmt) _ _ 𝓒_lt_𝓗 H C
copy_doc_string carnot_thm' → carnot_thm
/-- An `usual_engine_cycle` is reversible iff it has the greatest efficiency. -/
theorem usual_engine_cycle.rev_iff_eff (hC : C.reversible) : H.reversible ↔ H.eff = C.eff := by {
  split,
  { assume hH,
    have H_le_C := carnot_thm hH.elim_left hC,
    have C_le_H := carnot_thm hC.elim_left hH,
    exact eq_of_le_of_not_lt H_le_C (not_lt_of_ge C_le_H), },
  { assume heff,
    exact let ⟨c, hc⟩ := usual_engine_cycle.eq_smul_pos_of_eff_eq heff in by {
      rw hc,
      exact cycle.reversible_smul_nonneg (le_of_lt c.property) hC, } } }
--

end carnot_thm

end thermodynamics
