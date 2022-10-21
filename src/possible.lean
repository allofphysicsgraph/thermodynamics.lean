/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import second_law

/-!
# Characterization of `cycle.possible`

TODO
* characterization of possible `usual_engine_cycle` and `usual_pump_cycle`
* sufficient(equivalent) conditions for `cycle.possible` ?
-/

namespace thermodynamics

/-!
### `engine_cycle`
-/

namespace cycle
variables {H : cycle} [engine_cycle H]

lemma abs_every_rsv_if_no_rel (hno_rel : (H.Qrel:ℝ) = 0) {𝓗} (h𝓗supp : 𝓗 ∈ H.𝓠.support) :
  0 < H.𝓠 𝓗 := by {
  by_contradiction this, have := eq_or_lt_of_not_lt this,
  cases this with h𝓗zero h𝓗neg,
  { have := (H.𝓠.mem_support_to_fun 𝓗).elim_left h𝓗supp,
    exact absurd h𝓗zero this.symm, },
  { have : max (- H.𝓠 𝓗) 0 = - H.𝓠 𝓗, from max_eq_left_of_lt (neg_pos_of_neg h𝓗neg),
    have :=
      calc ↑H.Qrel
           = H.𝓠.support.sum (λ 𝓣, max (- H.𝓠 𝓣) 0) : rfl
        ...= - H.𝓠 𝓗 + (H.𝓠.support.erase 𝓗).sum (λ 𝓣, max (- H.𝓠 𝓣) 0) :
              by rw [←finset.add_sum_erase _ _ h𝓗supp, this]
        ...≥ - H.𝓠 𝓗 :
              by simp only [finset.sum_nonneg, ge_iff_le, le_neg_add_iff_add_le, add_right_neg,
                            le_max_iff, le_refl, or_true, implies_true_iff]
        ...> 0 : neg_pos_of_neg h𝓗neg,
    exact absurd hno_rel (ne_of_gt this), }, }
theorem psbl_engine_do_rel (hHpsbl : H.possible) : 0 < H.Qrel := by {
  suffices h : Π n : ℕ, (H.𝓠.support.card = n.succ) → (0 < H.Qrel),
  { exact if hcard : H.𝓠.support.card = 0 then by {
      have : H.𝓠.support = ∅, from finset.card_eq_zero.elim_left hcard,
      have :=
        calc H.𝓦
             = H.𝓠.sum_image : H.𝓦_from_𝓠
          ...= 0             : by rw [finsupp.sum_image, this, finset.sum_empty],
      exact absurd this (ne_of_gt H.engine_do_work), }
    else
      let ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero hcard in
      h k hk },
  assume n, unfreezingI{revert H}, induction n with n ih,
  { assume H engH hHpsbl, haveI := engH, assume hcard,
    exact
    let ⟨𝓣, h𝓣⟩ := finset.card_eq_one.elim_left hcard in
    let H' : one_rsv_cycle 𝓣 :=
      { to_cycle := H,
        one_rsv := h𝓣 } in by {
    have hdo_work : 0 < H'.𝓦 , from H.engine_do_work,
    have hpsbl : H'.possible, from hHpsbl,
    exact absurd hpsbl (kelvin_stmt H' hdo_work), } },
  { assume H engH hHpsbl, haveI := engH, assume hcard,
    by_contradiction hQrel, have hQrel := eq_of_ge_of_not_gt H.Qrel.property hQrel,
    have supp_nonempty := finset.card_pos.elim_left (by { rw hcard, exact nat.succ_pos' }),
    let 𝓒 := H.𝓠.support.min' supp_nonempty,
    let 𝓗 := H.𝓠.support.max' supp_nonempty,
    have 𝓒_supp : 𝓒 ∈ H.𝓠.support, from finset.min'_mem _ _,
    have 𝓗_supp : 𝓗 ∈ H.𝓠.support, from finset.max'_mem _ _,
    have do_abs𝓒 : 0 < H.𝓠 𝓒, from abs_every_rsv_if_no_rel hQrel 𝓒_supp,
    have do_abs𝓗 : 0 < H.𝓠 𝓗, from abs_every_rsv_if_no_rel hQrel 𝓗_supp,
    have 𝓒_lt_𝓗 : 𝓒 < 𝓗, {
      have : 1 < H.𝓠.support.card,
        rw hcard,
        apply nat.succ_lt_succ,
        exact nat.succ_pos',
      exact finset.min'_lt_max'_of_card _ this, },
    exact
    let ⟨eng, heng, hQ⟩ := usual_engine_cycle.exists_psbl_rel 𝓒_lt_𝓗 do_abs𝓒 in
    let H' := H + eng.to_cycle in by {
    haveI : engine_cycle H' :=
      ⟨ calc H'.𝓦
             = H.𝓦 + eng.𝓦 : cycle.𝓦_add
          ...> 0             : add_pos H.engine_do_work eng.do_work ⟩,
    have H'no_𝓒 :=
      calc H'.𝓠 𝓒
           = H.𝓠 𝓒 + eng.𝓠 𝓒    : rfl
        ...= eng.Qrel + eng.𝓠 𝓒 : by rw hQ
        ...= 0                  : by rw [eng.Qrel_one_rsv, add_left_neg],
    have H'do_abs𝓗 :=
      calc H'.𝓠 𝓗
         = H.𝓠 𝓗 + eng.𝓠 𝓗 : rfl
      ...= H.𝓠 𝓗 + eng.Qabs : by rw eng.Qabs_one_rsv
      ...> 0                 : add_pos do_abs𝓗 eng.do_abs,
    have eng_Hsupp : H.𝓠.support ∪ eng.𝓠.support = H.𝓠.support, {
      apply finset.union_eq_left_iff_subset.elim_right,
      rw eng.two_rsv.elim_left,
      apply finset.subset_iff.elim_right,
      simp only [finset.mem_insert, finset.mem_singleton],
      simp only [forall_eq_or_imp, forall_eq],
      exact ⟨𝓗_supp, 𝓒_supp⟩, },
    have lemmaH' : ∀ {𝓣}, (𝓣 ≠ 𝓒) → (𝓣 ∈ H.𝓠.support) → (0 < H'.𝓠 𝓣), {
      assume 𝓣 h𝓣not𝓒 h𝓣_Hsupp,
      exact if h𝓣_𝓗 : 𝓣 = 𝓗 then by {
        rw h𝓣_𝓗, exact H'do_abs𝓗, }
      else by {
        have : eng.𝓠 𝓣 = 0, {
          apply finsupp.not_mem_support_iff.elim_left,
          rw [eng.two_rsv.elim_left, finset.mem_insert, finset.mem_singleton],
          simp only [h𝓣not𝓒, h𝓣_𝓗, or_self, not_false_iff], },
        calc H'.𝓠 𝓣
             = H.𝓠 𝓣 + eng.𝓠 𝓣 : rfl
          ...= H.𝓠 𝓣           : by simp only [this, add_zero]
          ...> 0               : abs_every_rsv_if_no_rel hQrel h𝓣_Hsupp, } },
    have H'supp_erase𝓒 : H'.𝓠.support = H.𝓠.support.erase 𝓒, {
      have : H'.𝓠 = H.𝓠 + eng.𝓠, from rfl, rw this,
      apply finsupp.support_add_exact,
      { simp only [finset.mem_erase, ne.def, and_imp],
        assume 𝓣 h𝓣not𝓒 h𝓣_Hsupp,
        exact ne_of_gt (lemmaH' h𝓣not𝓒 h𝓣_Hsupp), },
      { rw [eng_Hsupp, finset.sdiff_erase 𝓒_supp],
        simp only [finset.mem_singleton, forall_eq],
        exact H'no_𝓒, } },
    have hH'no_rel : H'.Qrel.val = 0, {
      apply finset.sum_eq_zero,
      rw H'supp_erase𝓒,
      simp only [finset.mem_erase, ne.def, max_eq_right_iff, right.neg_nonpos_iff, and_imp],
      assume 𝓣 h𝓣not𝓒 h𝓣_Hsupp,
      exact le_of_lt (lemmaH' h𝓣not𝓒 h𝓣_Hsupp), },
    exact absurd hH'no_rel (ne_of_gt (@ih
      H' _
      (cycle.possible_add hHpsbl heng)
      ( calc H'.𝓠.support.card
           = (H.𝓠.support.erase 𝓒).card : by rw H'supp_erase𝓒
        ...= H.𝓠.support.card - 1       : finset.card_erase_of_mem 𝓒_supp
        ...= n.succ                     : by rw [hcard, nat.succ_sub_one] ) ) ), } } }
theorem psbl_engine_eff_lt_one (hHpsbl : H.possible) : H.eff < 1 := by {
  rw H.eff_from_Qabs_Qrel,
  have : (0:ℝ) < H.Qrel / H.Qabs, from div_pos (psbl_engine_do_rel hHpsbl) H.engine_do_abs,
  simp only [this, sub_lt_self_iff], }
--

end cycle

end thermodynamics
