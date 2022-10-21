/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import logic.equiv.transfer_instance
import math_lemma
import zeroth_law

/-!
# Thermodynamic Cycles and the FIRST Law

This file defines
* the notion of abstract thermodynamic `cycle`, which satisfies the first law
* some specific types of `cycle`s, including
  `one_rsv_cycle`, `abs_rel_cycle`, `engine_cycle` class,
  `usual_engine_cycle`, `usual_pump_cycle`
* the connection (`add`), scaling (`smul`), and reversion of `cycle`s
and proves
* some basic properties of the various types of `cycle`s
-/

noncomputable theory

namespace thermodynamics

/-!
## General abstract `cycle`

In the spirit of the first law, a thermodynamic `cycle` is a heat-work conversion.
* The abstract `cycle` defined here can be viewd of as the equivalence class of concrete cycles
  that have the same result of heat-work conversion.
* `cycle`s need not to satisfy the second law.
---------------------------------------------------------------------------------------------------/

/-- Abstrct `cycle` (denoted by `H`) :
    finitely many `𝓣`s PROVIDE heat `𝓠 𝓣`, and `H` DOES work `𝓦`, satisfying the first law -/
structure cycle :=
  (𝓠 : reservoir →₀ ℝ)
  (𝓦 : ℝ)
  (energy_conserv : 𝓠.sum_image - 𝓦 = 0)
--

namespace cycle
variables (H : cycle)

lemma 𝓦_from_𝓠 : H.𝓦 = H.𝓠.sum_image :=
  (sub_eq_zero.elim_left H.energy_conserv).symm
/-! Lemmas concerning `Qabs` and `Qrel` should use them as `ℝ`s. -/
/-- `abs`orbed heat `Qabs = ∑(+𝓠 > 0)` -/
def Qabs : nnreal :=
  { val := H.𝓠.support.sum (λ 𝓣, max (H.𝓠 𝓣) 0),
    property := by simp only [finset.sum_nonneg, le_max_iff, le_refl, or_true, implies_true_iff] }
/-- `rel`eased heat `Qrel = ∑(-𝓠 > 0)` -/
def Qrel : nnreal :=
  { val := H.𝓠.support.sum (λ 𝓣, max (- H.𝓠 𝓣) 0),
    property := by simp only [finset.sum_nonneg, le_max_iff, le_refl, or_true, implies_true_iff] }
lemma 𝓠_from_Qabs_Qrel : H.𝓠.sum_image = H.Qabs - H.Qrel := by {
  simp only [Qabs, Qrel, subtype.coe_mk],
  simp only [←finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self], }
lemma 𝓦_from_Qabs_Qrel : H.𝓦 = H.Qabs - H.Qrel :=
  eq.trans H.𝓦_from_𝓠 H.𝓠_from_Qabs_Qrel
lemma Qabs_from_𝓦_Qrel : ↑H.Qabs = H.𝓦 + H.Qrel :=
  calc H.Qabs.val
       = H.Qabs - H.Qrel + H.Qrel : by ring
    ...= H.𝓦 + H.Qrel            : by rw 𝓦_from_Qabs_Qrel
lemma Qrel_from_Qabs_𝓦 : ↑H.Qrel = ↑H.Qabs - H.𝓦 := by {
  apply eq.symm,
  rw 𝓦_from_Qabs_Qrel,
  ring, }
--

@[reducible] def equiv_𝓠 : (reservoir →₀ ℝ) ≃ cycle :=
  { to_fun  := λ 𝓠,
      { 𝓠 := 𝓠,
        𝓦 := 𝓠.sum_image,
        energy_conserv := sub_self _ },
    inv_fun := λ H, H.𝓠,
    left_inv  := λ _, rfl,
    right_inv := λ H, let ⟨_,_,energy_conserv⟩ := H in
      by simp [sub_eq_zero.elim_left energy_conserv] }
/-- `cycle` forms a `add_comm_group`.
* adding two `cycle`s means connecting them
* negating a `cycle` means reversing it
-/
instance : add_comm_group cycle := equiv.add_comm_group equiv_𝓠.symm
/-- `cycle` forms a real vector space.
* multiplying a `cycle` with `c ∈ ℝ` means scaling it `c` times
-/
instance : module ℝ       cycle := equiv.module ℝ      equiv_𝓠.symm

variables {H} {H₁ H₂ : cycle} {c : ℝ}
@[simp] lemma 𝓦_add : (H₁ + H₂).𝓦 = H₁.𝓦 + H₂.𝓦 :=
  calc (H₁ + H₂).𝓦
       = (H₁.𝓠 + H₂.𝓠).sum_image         : 𝓦_from_𝓠 _
    ...= H₁.𝓠.sum_image + H₂.𝓠.sum_image : finsupp.sum_image_add
    ...= H₁.𝓦 + H₂.𝓦                    : by rw [𝓦_from_𝓠, 𝓦_from_𝓠]
@[simp] lemma 𝓦_smul : (c • H).𝓦 = c * H.𝓦 :=
  calc (c • H).𝓦
       = (c • H.𝓠).sum_image : 𝓦_from_𝓠 _
    ...= c * H.𝓠.sum_image   : finsupp.sum_image_smul
    ...= c * H.𝓦            : by rw 𝓦_from_𝓠
@[simp] lemma Qabs_smul_pos (hc : 0 < c) : ↑(c • H).Qabs = c * H.Qabs :=
  have hsupp : (c • H.𝓠).support = H.𝓠.support, from
    finsupp.support_smul_eq (ne_of_gt hc),
  have hmax : ∀ 𝓣, max (c • H.𝓠 𝓣) 0 = c • max (H.𝓠 𝓣) 0, from
    λ _, real.max_mul_nonneg_zero _ _ (le_of_lt hc),
  calc ↑(c • H).Qabs
       = (c • H.𝓠).support.sum (λ 𝓣, max (c • H.𝓠 𝓣) 0) : rfl
    ...= H.𝓠.support.sum (λ 𝓣, max (c • H.𝓠 𝓣) 0) : by rw hsupp
    ...= H.𝓠.support.sum (λ 𝓣, c • max (H.𝓠 𝓣) 0) : by rw (funext hmax)
    ...= c • H.𝓠.support.sum (λ 𝓣, max (H.𝓠 𝓣) 0) : by rw finset.smul_sum
    ...= c * H.Qabs : rfl
@[simp] lemma Qrel_smul_pos (hc : 0 < c) : ↑(c • H).Qrel = c * H.Qrel :=
  have hsupp : (c • H.𝓠).support = H.𝓠.support, from
    finsupp.support_smul_eq (ne_of_gt hc),
  have hmax : ∀ 𝓣, max (-(c • H.𝓠 𝓣)) 0 = c • max (- H.𝓠 𝓣) 0, by {
    assume 𝓣,
    have : -(c • H.𝓠 𝓣) = c * (- H.𝓠 𝓣), rw [smul_eq_mul, mul_neg], rw this,
    exact real.max_mul_nonneg_zero _ _ (le_of_lt hc), },
  calc ↑(c • H).Qrel
       = (c • H.𝓠).support.sum (λ 𝓣, max (-(c • H.𝓠 𝓣)) 0) : rfl
    ...= H.𝓠.support.sum (λ 𝓣, max (-(c • H.𝓠 𝓣)) 0) : by rw hsupp
    ...= H.𝓠.support.sum (λ 𝓣, c • max (- H.𝓠 𝓣 ) 0) : by rw (funext hmax)
    ...= c • H.𝓠.support.sum (λ 𝓣, max (- H.𝓠 𝓣 ) 0) : by rw finset.smul_sum
    ...= c * H.Qrel : rfl
lemma rev_Qabs : ((-H).Qabs:ℝ) = H.Qrel :=
  calc (-H).Qabs.val
       = (-H.𝓠).support.sum (λ 𝓣, max (- H.𝓠 𝓣) 0) : rfl
    ...=   H.𝓠 .support.sum (λ 𝓣, max (- H.𝓠 𝓣) 0) : by rw finsupp.support_neg
    ...= H.Qrel.val : rfl
lemma rev_Qrel : ((-H).Qrel:ℝ) = H.Qabs :=
  have hmax : ∀ 𝓣, max (- (-H.𝓠 𝓣)) 0 = max (H.𝓠 𝓣) 0, {
    assume _, rw neg_neg, },
  calc (-H).Qrel.val
       = (-H.𝓠).support.sum (λ 𝓣, max (- (-H.𝓠 𝓣)) 0) : rfl
    ...=   H.𝓠 .support.sum (λ 𝓣, max (- (-H.𝓠 𝓣)) 0) : by rw finsupp.support_neg
    ...=   H.𝓠 .support.sum (λ 𝓣, max (    H.𝓠 𝓣 ) 0) : by rw (funext hmax)
    ...= H.Qabs.val : rfl
--

end cycle

/-!
## Some types of abstract `cycle`s
---------------------------------------------------------------------------------------------------/

/-!
### `one_rsv_cycle`
-/

/-- `cycle` that exchanges heat with only one `reservoir` -/
structure one_rsv_cycle (𝓣 : reservoir) extends cycle :=
  (one_rsv : 𝓠.support = {𝓣})
--

namespace one_rsv_cycle
variables {𝓣 : reservoir} (H : one_rsv_cycle 𝓣)

lemma Qabs_one_rsv : ↑H.Qabs = max (H.𝓠 𝓣) 0 := by {
  simp only [cycle.Qabs, subtype.coe_mk],
  simp only [H.one_rsv, finset.sum_singleton], }
lemma Qrel_one_rsv : ↑H.Qrel = max (- H.𝓠 𝓣) 0 := by {
  simp only [cycle.Qrel, subtype.coe_mk],
  simp only [H.one_rsv, finset.sum_singleton], }
/-- `𝓦` is `conv`erted from/to one rsv. -/
lemma 𝓦_conv_one_rsv : H.𝓦 = H.𝓠 𝓣 := by {
  rw [H.𝓦_from_𝓠, finsupp.sum_image],
  simp only [H.one_rsv, finset.sum_singleton], }
--

lemma to_cycle_inj : function.injective (λ H : one_rsv_cycle 𝓣, H.to_cycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩, by simp only [imp_self]
instance : has_smul ℝ₊ (one_rsv_cycle 𝓣) := ⟨λ c H, 
  let H' := c.val • H.to_cycle in
  { one_rsv := by {
      have : H'.𝓠 = c.val • H.𝓠, from rfl, rw this,
      exact finsupp.support_smul_exact H.one_rsv c.ne_zero, },
    ..H' } ⟩
--

end one_rsv_cycle

/-!
### `abs_rel_cycle`
-/

/-- `cycle` that absorbs heat `Qabs > 0` from rsv `𝓐` and releases heat `Qrel > 0` to rsv `𝓡` -/
structure abs_rel_cycle (𝓐 𝓡 : reservoir) extends cycle :=
  (two_rsv : 𝓠.support = {𝓐, 𝓡} ∧ 𝓐 ≠ 𝓡)
  (do_abs_rsv : 0 < 𝓠 𝓐) -- does absorb  heat from `𝓐`
  (do_rel_rsv : 𝓠 𝓡 < 0) -- does release heat to   `𝓡`
--

namespace abs_rel_cycle
variables {𝓐 𝓡 : reservoir} (H : abs_rel_cycle 𝓐 𝓡)

lemma Qabs_one_rsv : ↑H.Qabs = H.𝓠 𝓐 := by {
  simp only [cycle.Qabs, subtype.coe_mk],
  simp only [H.two_rsv.elim_left, (finset.sum_pair H.two_rsv.elim_right)],
  simp [le_of_lt H.do_abs_rsv, le_of_lt H.do_rel_rsv], }
lemma Qrel_one_rsv : ↑H.Qrel = - H.𝓠 𝓡 := by {
  simp only [cycle.Qrel, subtype.coe_mk],
  simp only [H.two_rsv.elim_left, (finset.sum_pair H.two_rsv.elim_right)],
  simp [le_of_lt H.do_abs_rsv, le_of_lt H.do_rel_rsv], }
lemma do_abs : (0:ℝ) < H.Qabs :=
  calc H.Qabs.val
       = H.𝓠 𝓐 : H.Qabs_one_rsv
    ...> 0      : H.do_abs_rsv
lemma do_rel : (0:ℝ) < H.Qrel :=
  calc H.Qrel.val
       = - H.𝓠 𝓡 : H.Qrel_one_rsv
    ...> 0       : by simp [H.do_rel_rsv]
lemma 𝓦_from_two_rsv : H.𝓦 = (H.𝓠 𝓐) + (H.𝓠 𝓡) := by {
  rw [H.𝓦_from_Qabs_Qrel],
  rw [H.Qabs_one_rsv, H.Qrel_one_rsv],
  rw [sub_neg_eq_add], }
--

variables {H₁ H₂ : abs_rel_cycle 𝓐 𝓡}
lemma to_cycle_inj : function.injective (λ H : abs_rel_cycle 𝓐 𝓡, H.to_cycle) :=
  λ ⟨_,_,_,_⟩ ⟨_,_,_,_⟩, by simp only [imp_self]
lemma eq_of_Q_eq (habs : (H₁.Qabs:ℝ) = H₂.Qabs) (hrel : (H₁.Qrel:ℝ) = H₂.Qrel) : H₁ = H₂ := by {
  apply to_cycle_inj, apply cycle.equiv_𝓠.symm.injective,
  simp only [equiv.coe_fn_symm_mk],
  apply finsupp.ext_iff'.elim_right, split,
  { rw [H₁.two_rsv.elim_left, H₂.two_rsv.elim_left], },
  { rw H₁.two_rsv.elim_left,
    simp only [finset.mem_insert, finset.mem_singleton, forall_eq_or_imp, forall_eq],
    split,
    { rw [H₁.Qabs_one_rsv, H₂.Qabs_one_rsv] at habs,
      exact habs, },
    { rw [H₁.Qrel_one_rsv, H₂.Qrel_one_rsv] at hrel,
      exact neg_inj.elim_left hrel, } } }
lemma eq_of_Qabs_𝓦_eq (hQabs : (H₁.Qabs:ℝ) = H₂.Qabs) (h𝓦 : H₁.𝓦 = H₂.𝓦) : H₁ = H₂ := by {
  refine eq_of_Q_eq hQabs _,
  rw [H₁.𝓦_from_Qabs_Qrel, H₂.𝓦_from_Qabs_Qrel] at h𝓦,
  simp only [hQabs, sub_right_inj] at h𝓦,
  exact h𝓦, }
--

instance : has_add (abs_rel_cycle 𝓐 𝓡) := ⟨λ H₁ H₂, by {
  let H' := H₁.to_cycle + H₂.to_cycle,
  have do_abs_rsv := add_pos H₁.do_abs_rsv H₂.do_abs_rsv,
  have do_rel_rsv := add_neg H₁.do_rel_rsv H₂.do_rel_rsv,
  exact
  { two_rsv := by {
      refine ⟨_, H₁.two_rsv.elim_right⟩,
      have : H'.𝓠 = H₁.𝓠 + H₂.𝓠, from rfl, rw this,
      apply finsupp.support_add_exact,
      { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
        split,
          exact ne_of_gt do_abs_rsv,
          exact ne_of_lt do_rel_rsv, },
      { have : (H₁.𝓠.support ∪ H₂.𝓠.support) \ {𝓐, 𝓡} = ∅, {
          rw [H₁.two_rsv.elim_left, H₂.two_rsv.elim_left],
          ext, simp, tauto, },
        simp only [this, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff], } },
    do_abs_rsv :=
      calc H'.𝓠 𝓐
           = H₁.𝓠 𝓐 + H₂.𝓠 𝓐 : rfl
        ...> 0                 : do_abs_rsv,
    do_rel_rsv :=
      calc H'.𝓠 𝓡
           = H₁.𝓠 𝓡 + H₂.𝓠 𝓡 : rfl
        ...< 0                : do_rel_rsv,
    ..H' } } ⟩
instance : add_comm_semigroup (abs_rel_cycle 𝓐 𝓡) :=
  function.injective.add_comm_semigroup
    (λ H, H.to_cycle)
    to_cycle_inj
    (λ _ _, rfl)
instance : has_smul ℝ₊ (abs_rel_cycle 𝓐 𝓡) := ⟨λ c H,
  let H' := c.val • H.to_cycle in
  { two_rsv := by {
      refine ⟨_, H.two_rsv.elim_right⟩,
      have : H'.𝓠 = c.val • H.𝓠, from rfl, rw this,
      exact finsupp.support_smul_exact H.two_rsv.elim_left c.ne_zero, },
    do_abs_rsv :=
      calc H'.𝓠 𝓐
           = c * (H.𝓠 𝓐) : rfl
        ...> 0            : mul_pos c.property H.do_abs_rsv,
    do_rel_rsv :=
      calc H'.𝓠 𝓡
           = c * (H.𝓠 𝓡) : rfl
        ...< 0            : mul_neg_of_pos_of_neg c.property H.do_rel_rsv,
    ..H' } ⟩
--

/-- The reverse of an `abs_rel_cycle 𝓐 𝓡` is an `abs_rel_cycle 𝓡 𝓐`. -/
def rev : abs_rel_cycle 𝓡 𝓐 :=
  { two_rsv :=
      ⟨ calc (-H.to_cycle).𝓠.support
             = (-H.𝓠).support : rfl
          ...= {𝓐, 𝓡} : by rw [H.𝓠.support_neg, H.two_rsv.elim_left]
          ...= {𝓡, 𝓐} : by{ext, simp only [finset.mem_insert, finset.mem_singleton], tauto},
        H.two_rsv.elim_right.symm ⟩,
    do_abs_rsv :=
      calc (-H.to_cycle).𝓠 𝓡
           = - H.𝓠 𝓡 : rfl
        ...= H.Qrel  : by rw H.Qrel_one_rsv
        ...> 0       : H.do_rel,
    do_rel_rsv :=
      calc (-H.to_cycle).𝓠 𝓐
           = - H.𝓠 𝓐 : rfl
        ...= - H.Qabs : by rw H.Qabs_one_rsv
        ...< 0        : neg_neg_of_pos H.do_abs,
    ..(-H.to_cycle) }
--

end abs_rel_cycle

/-!
### `engine_cycle` class
-/

/-- `cycle` that does positive work -/
class engine_cycle (H : cycle) :=
  (do_work : 0 < H.𝓦)
--

namespace cycle

variables (H : cycle) [engine_cycle H]

lemma engine_do_work : 0 < H.𝓦 := (infer_instance : engine_cycle H).do_work
/-- absorb heat `Qabs > 0` -/
lemma engine_do_abs : (0:ℝ) < H.Qabs := by {
  suffices : 0 ≠ H.Qabs.val, from lt_of_le_of_ne H.Qabs.property this,
  have :=
    calc H.Qabs.val
         = H.𝓦 + H.Qrel : by simp [H.𝓦_from_Qabs_Qrel]
      ...>        H.Qrel : by simp [H.engine_do_work]
      ...≥ 0             : H.Qrel.property,
  exact ne_of_lt this, }
--

/-- `eff`iciency of `engine_cycle` -/
def eff : ℝ := H.𝓦 / H.Qabs
lemma eff_pos    : 0 < H.eff := div_pos H.engine_do_work H.engine_do_abs
lemma eff_le_one : H.eff ≤ 1 := by {
  refine (@div_le_one ℝ _ _ _ H.engine_do_abs).elim_right _,
  calc H.𝓦
       = H.Qabs - H.Qrel : H.𝓦_from_Qabs_Qrel
    ...≤ H.Qabs          : by simp only [sub_le_self_iff, nnreal.zero_le_coe], }
lemma eff_from_Qabs_Qrel : H.eff = 1 - H.Qrel / H.Qabs :=
  calc H.eff
       =  H.𝓦            / H.Qabs         : rfl
    ...= (H.Qabs - H.Qrel)/ H.Qabs         : by rw H.𝓦_from_Qabs_Qrel
    ...= H.Qabs / H.Qabs - H.Qrel / H.Qabs : sub_div _ _ _
    ...= 1 - H.Qrel / H.Qabs               : by rw [div_self (ne_of_gt H.engine_do_abs)]
lemma 𝓦_from_eff_Qabs : H.𝓦 = H.eff * H.Qabs :=
  calc H.𝓦
       = H.𝓦 / H.Qabs * H.Qabs : eq.symm $ div_mul_cancel _ (ne_of_gt H.engine_do_abs)
    ...= H.eff * H.Qabs         : by rw eff
lemma Qabs_from_𝓦_eff : ↑H.Qabs = H.𝓦 / H.eff := by {
  have :=
    calc H.𝓦 / H.eff
         = H.𝓦 / H.𝓦 * H.Qabs : by { rw div_mul, refl }
      ...= H.Qabs               : by rw [div_self (ne_of_gt H.engine_do_work), one_mul],
  exact this.symm, }
--

variables (H₁ H₂ : cycle) [engine_cycle H₁] [engine_cycle H₂]
instance engine_add : engine_cycle (H₁ + H₂) :=
  ⟨ calc (H₁ + H₂).𝓦
         = H₁.𝓦 + H₂.𝓦 : cycle.𝓦_add
      ...> 0             : add_pos H₁.engine_do_work H₂.engine_do_work ⟩
variables (c : ℝ) [fact (0 < c)]
instance engine_smul_pos : engine_cycle (c • H) :=
  let hc := (infer_instance : fact (0 < c)).out in
  ⟨ calc (c • H).𝓦
         = c * H.𝓦 : cycle.𝓦_smul
      ...> 0        : mul_pos hc H.engine_do_work ⟩
lemma eff_smul_pos {c : ℝ} [fact (0 < c)] : (c • H).eff = H.eff :=
  let hc := (infer_instance : fact (0 < c)).out in
  calc (c • H).eff
       = (c • H).𝓦 / (c • H).Qabs : rfl
    ...= (c * H.𝓦) / (c * H.Qabs) : by rw [cycle.𝓦_smul, cycle.Qabs_smul_pos hc]
    ...= (c / c) * (H.𝓦 / H.Qabs) : mul_div_mul_comm _ _ _ _
    ...=            H.eff          : by rw [div_self (ne_of_gt hc), one_mul, eff]
--

end cycle

/-!
### `usual_engine_cycle`
-/

/-- `abs_rel_cycle` that abs from hotter `𝓗`, rel to colder `𝓒`, and does positive work -/
structure usual_engine_cycle {𝓗 𝓒} (_: 𝓒 < 𝓗) extends (abs_rel_cycle 𝓗 𝓒) :=
  (do_work : 0 < 𝓦)
--

namespace usual_engine_cycle
variables {𝓗 𝓒 : reservoir} {𝓒_lt_𝓗 : 𝓒 < 𝓗} (H : usual_engine_cycle 𝓒_lt_𝓗)

instance : engine_cycle H.to_cycle := ⟨H.do_work⟩
lemma eff_lt_one : H.eff < 1 := by {
  rw H.eff_from_Qabs_Qrel,
  simp only [sub_lt_self_iff],
  exact div_pos H.do_rel H.do_abs, }
lemma eff_from_𝓦_𝓠 : H.eff = H.𝓦 / (H.𝓠 𝓗) :=
  by rw [cycle.eff, H.Qabs_one_rsv]
lemma eff_from_𝓠 : H.eff = 1 - (- H.𝓠 𝓒)/(H.𝓠 𝓗) := by {
  have := H.eff_from_Qabs_Qrel,
  rw [H.Qabs_one_rsv, H.Qrel_one_rsv] at this,
  exact this, }
--

lemma to_abs_rel_cycle_inj :
  function.injective (λ H : usual_engine_cycle 𝓒_lt_𝓗, H.to_abs_rel_cycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩, by simp only [imp_self]
/- lemma to_cycle_inj :
  function.injective (λ H : usual_engine_cycle 𝓒_lt_𝓗, H.to_cycle) :=
  λ ⟨⟨_,_,_,_⟩,_⟩ ⟨⟨_,_,_,_⟩,_⟩, by simp only [imp_self] -/
instance : has_add (usual_engine_cycle 𝓒_lt_𝓗) := ⟨λ H₁ H₂,
  { ..(H₁.to_abs_rel_cycle + H₂.to_abs_rel_cycle),
    ..(cycle.engine_add H₁.to_cycle H₂.to_cycle) } ⟩
instance : add_comm_semigroup (usual_engine_cycle 𝓒_lt_𝓗) :=
  function.injective.add_comm_semigroup
    (λ H, H.to_abs_rel_cycle)
    to_abs_rel_cycle_inj
    (λ _ _, rfl)
instance : has_smul ℝ₊ (usual_engine_cycle 𝓒_lt_𝓗) := ⟨λ c H,
  { ..(c • H.to_abs_rel_cycle),
    ..(@cycle.engine_smul_pos H.to_cycle _ _ ⟨c.property⟩) } ⟩
--

variables {H₁ H₂ : usual_engine_cycle 𝓒_lt_𝓗}
lemma eq_smul_pos_of_eff_eq : H₁.eff = H₂.eff → ∃ c : ℝ₊, H₁ = c • H₂ := by {
  let c : ℝ₊ :=
    { val := H₁.𝓦 / H₂.𝓦,
      property := div_pos H₁.do_work H₂.do_work },
  assume heff, refine ⟨c, _⟩,
  apply to_abs_rel_cycle_inj, apply abs_rel_cycle.eq_of_Qabs_𝓦_eq,
  calc (H₁.Qabs:ℝ)
       = H₁.𝓦 / H₁.𝓦 * H₁.Qabs : by rw [div_self (ne_of_gt H₁.engine_do_work), one_mul]
    ...= H₁.𝓦 / H₁.eff          : by { rw div_mul, refl }
    ...= H₁.𝓦 / H₂.𝓦 * H₂.Qabs : by { rw [heff, div_mul], refl }
    ...= c             * H₂.Qabs : rfl
    ...= (c • H₂).Qabs           : eq.symm $ cycle.Qabs_smul_pos c.property,
  calc H₁.𝓦
       = H₁.𝓦 / H₂.𝓦 * H₂.𝓦 : eq.symm $ div_mul_cancel _ (ne_of_gt H₂.engine_do_work)
    ...= c             * H₂.𝓦 : rfl
    ...= (c • H₂).𝓦           : eq.symm $ cycle.𝓦_smul, }
--

end usual_engine_cycle

/-!
### `usual_pump_cycle`
-/

/-- `abs_rel_cycle` that consumes work, abs from colder `𝓒`, and rel to hotter `𝓗` -/
structure usual_pump_cycle {𝓒 𝓗} (_: 𝓒 < 𝓗) extends (abs_rel_cycle 𝓒 𝓗) :=
  (consume_work : 𝓦 < 0)
--

namespace usual_pump_cycle
variables {𝓒 𝓗 : reservoir} {𝓒_lt_𝓗 : 𝓒 < 𝓗} (H : usual_pump_cycle 𝓒_lt_𝓗)

lemma to_abs_rel_cycle_inj :
  function.injective (λ H : usual_pump_cycle 𝓒_lt_𝓗, H.to_abs_rel_cycle) :=
  λ ⟨_,_⟩ ⟨_,_⟩, by simp only [imp_self]
/- lemma to_cycle_inj :
  function.injective (λ H : usual_pump_cycle 𝓒_lt_𝓗, H.to_cycle) :=
  λ ⟨⟨_,_,_,_⟩,_⟩ ⟨⟨_,_,_,_⟩,_⟩, by simp only [imp_self] -/
instance : has_add (usual_pump_cycle 𝓒_lt_𝓗) := ⟨λ H₁ H₂,
  let H' := H₁.to_abs_rel_cycle + H₂.to_abs_rel_cycle in
  { consume_work :=
      calc H'.𝓦
           = (H₁.to_cycle + H₂.to_cycle).𝓦 : rfl
        ...= H₁.𝓦 + H₂.𝓦                  : cycle.𝓦_add
        ...< 0                              : add_neg H₁.consume_work H₂.consume_work,
    ..H' } ⟩
instance : add_comm_semigroup (usual_pump_cycle 𝓒_lt_𝓗) :=
  function.injective.add_comm_semigroup
    (λ H, H.to_abs_rel_cycle)
    to_abs_rel_cycle_inj
    (λ _ _, rfl)
instance : has_smul ℝ₊ (usual_pump_cycle 𝓒_lt_𝓗) := ⟨λ c H,
  let H' := c • H.to_abs_rel_cycle in
  { consume_work :=
      calc H'.𝓦
           = (c.val • H.to_cycle).𝓦 : rfl
        ...= c * H.𝓦                : cycle.𝓦_smul
        ...< 0                       : mul_neg_of_pos_of_neg c.property H.consume_work,
    ..H' } ⟩
--

end usual_pump_cycle

/-!
### Reverse of `usual_engine_cycle` and `usual_pump_cycle`
-/

section rev_usual_engine_pump_cycle
variables {𝓒 𝓗 : reservoir} {𝓒_lt_𝓗 : 𝓒 < 𝓗}

/-- The reverse of an `usual_engine_cycle` is an `usual_pump_cycle`. -/
def usual_engine_cycle.rev (H : usual_engine_cycle 𝓒_lt_𝓗) : usual_pump_cycle 𝓒_lt_𝓗 :=
  { consume_work :=
      calc H.rev.𝓦
           =         (-H.to_cycle).𝓦 : rfl
        ...= ((-1:ℝ) • H.to_cycle).𝓦 : by rw [neg_one_smul]
        ...=                   - H.𝓦 : by rw [cycle.𝓦_smul, neg_one_mul]
        ...< 0                        : neg_neg_of_pos H.do_work,
    ..H.rev }
/-- The reverse of an `usual_pump_cycle` is an `usual_engine_cycle`. -/
def usual_pump_cycle.rev (H : usual_pump_cycle 𝓒_lt_𝓗) : usual_engine_cycle 𝓒_lt_𝓗 :=
  { do_work :=
      calc H.rev.𝓦
           =         (-H.to_cycle).𝓦 : rfl
        ...= ((-1:ℝ) • H.to_cycle).𝓦 : by rw [neg_one_smul]
        ...=                   - H.𝓦 : by rw [cycle.𝓦_smul, neg_one_mul]
        ...> 0                        : neg_pos_of_neg H.consume_work,
    ..H.rev }
--

end rev_usual_engine_pump_cycle

end thermodynamics
