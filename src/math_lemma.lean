/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import data.real.nnreal
import data.finsupp.basic

/-!
# Some math lemmas

## Notations

This file defines the notation `ℝ₊` for positive real numbers `{c : ℝ // 0 < c}`.
-/

section real

@[reducible] def posreal := {c : ℝ // 0 < c}
notation `ℝ₊` := posreal
namespace posreal
instance coe_nnreal : has_coe ℝ₊ nnreal := ⟨λ c, ⟨c.val, le_of_lt c.property⟩⟩
lemma ne_zero (c : ℝ₊) : (c:ℝ) ≠ 0 := by { rw ←subtype.val_eq_coe, exact ne_of_gt c.property }
end posreal

lemma real.max_mul_nonneg_zero (c x : ℝ) (hc : 0 ≤ c) : max (c * x) 0 = c * (max x 0) :=
  if hx : 0 ≤ x then by {
    have : max (c * x) 0 = c * x, from max_eq_left (mul_nonneg hc hx), rw this,
    have : max      x  0 =     x, from max_eq_left hx                , rw this, }
  else by {
    have hx := le_of_lt (not_le.elim_left hx),
    have : max (c * x) 0 = 0, from
      max_eq_right (mul_nonpos_iff.elim_right (or.inl ⟨hc, hx⟩)), rw this,
    have : max      x  0 = 0, from max_eq_right hx, rw this,
    rw mul_zero, }
--

end real

namespace finsupp
open finset

variables {α : Type*} [decidable_eq α]
variables {R : Type*} [decidable_eq R] [semiring R] [no_zero_smul_divisors R R]
variables {f g : α →₀ R}

@[reducible] def sum_image (f : α →₀ R) := f.support.sum f
lemma extend_support_sum_iamge {s : finset α}
  (s_extend_supp : f.support ⊆ s) : s.sum f = f.sum_image := by {
  rw ←sum_sdiff s_extend_supp,
  simp only [sum_image],
  suffices : (s \ f.support).sum f = 0,
    rw [this, zero_add],
  apply sum_eq_zero, assume x hx,
  simp only [mem_sdiff, mem_support_iff, not_not] at hx,
  exact hx.elim_right, }
lemma sum_image_add : (f + g).sum_image = f.sum_image + g.sum_image := by {
  let s := f.support ∪ g.support,
  have : (f + g).support ⊆ s, from support_add           , rw ←extend_support_sum_iamge this,
  have :  f     .support ⊆ s, from subset_union_left  _ _, rw ←extend_support_sum_iamge this,
  have :      g .support ⊆ s, from subset_union_right _ _, rw ←extend_support_sum_iamge this,
  exact finset.sum_add_distrib, }
lemma sum_image_smul {c : R} : (c • f).sum_image = c • f.sum_image :=
  if hc : c = 0 then by
    simp [hc, sum_image]
  else by {
    unfold sum_image,
    have : (c • f).support = f.support, from support_smul_eq hc, rw this,
    simp [finset.smul_sum], }
--

lemma support_add_exact {supp : finset α}
  (non_zero_on_supp   : ∀ x ∈ supp                           , f x + g x ≠ 0)
  (zero_on_sdiff_supp : ∀ x ∈ (f.support ∪ g.support) \ supp, f x + g x = 0) :
  (f + g).support = supp := by {
  ext x, split,
  { apply function.mtr,
    assume hx_supp,
    exact if hx_union : x ∈ (f.support ∪ g.support) then by {
      simp only [mem_support_iff, coe_add, pi.add_apply, not_not],
      exact zero_on_sdiff_supp x (mem_sdiff.elim_right ⟨hx_union, hx_supp⟩), }
    else by {
      have : (f + g).support ⊆ (f.support ∪ g.support), from support_add,
      exact not_mem_mono this hx_union, } },
  { simp only [mem_support_iff, coe_add, pi.add_apply],
    exact non_zero_on_supp x, } }
--

lemma support_smul_exact {c : R} {supp : finset α}
  (supp_is_supp : f.support = supp)
  (non_zero_smul : c ≠ 0) :
  (c • f).support = supp := by {
  rw ←supp_is_supp,
  exact support_smul_eq non_zero_smul, }
--

end finsupp
