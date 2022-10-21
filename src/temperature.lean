/-
Copyright (c) 2022 Youjack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youjack
-/
import second_law

/-!
# Thermodynamic Temperature

This file states
* the axiom that reversible `cycle`s do exists, i.e. `usual_engine_cycle.exists_reversible`
and defines
* thermodynamic temperature of `reservoir`, i.e. `reservoir.temp`
-/

noncomputable theory

namespace thermodynamics

/-!
## Existence of reversible `usual_engine_cycle`
---------------------------------------------------------------------------------------------------/

namespace usual_engine_cycle
variables {𝓗 𝓒 : reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

axiom exists_reversible : ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.reversible
copy_doc_string exists_reversible' → exists_reversible

variables {Q : ℝ} (hQ : 0 < Q)
/-- There exists reversible `usual_engine_cycle 𝓒_lt_𝓗` that absorbs a certain heat `Q > 0`. -/
lemma exists_rev_abs : ∃ H : usual_engine_cycle 𝓒_lt_𝓗, H.reversible ∧ ↑H.Qabs = Q :=
  let ⟨H', hH'⟩ := exists_reversible 𝓒_lt_𝓗 in
  let c : ℝ₊ := ⟨Q / H'.Qabs, div_pos hQ H'.do_abs⟩ in
  let H := c • H' in
  ⟨ H, 
    cycle.reversible_smul_nonneg (le_of_lt c.property) hH',
    calc ↑H.Qabs
         = Q / H'.Qabs * H'.Qabs : cycle.Qabs_smul_pos c.property
      ...= Q                     : div_mul_cancel _ (ne_of_gt H'.do_abs), ⟩
--

def rev_eff := (classical.some (exists_reversible 𝓒_lt_𝓗)).eff
lemma rev_eff_universal {H : usual_engine_cycle 𝓒_lt_𝓗} (h : H.reversible) :
  H.eff = rev_eff 𝓒_lt_𝓗 := by {
  apply (usual_engine_cycle.rev_iff_eff _).elim_left h,
  exact classical.some_spec (exists_reversible 𝓒_lt_𝓗), }
--

end usual_engine_cycle

-- lemma usual_pump_cycle.exists_reversible

/-!
## Thermodynamic temperature
---------------------------------------------------------------------------------------------------/

/-!
### Construction of thermodynamic temperature
-/

namespace reservoir

section
variables {𝓗 𝓒 : reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)
/-- `temp`erature `corr`elation function -/
@[reducible] def temp_corr := 1 - usual_engine_cycle.rev_eff 𝓒_lt_𝓗
lemma temp_corr_pos    : 0 < temp_corr 𝓒_lt_𝓗 :=
  sub_pos.elim_right (usual_engine_cycle.eff_lt_one _)
lemma temp_corr_lt_one : temp_corr 𝓒_lt_𝓗 < 1 :=
  sub_lt_self _ (cycle.eff_pos _)
lemma temp_corr_eq_Qratio {H : usual_engine_cycle 𝓒_lt_𝓗} (hH : H.reversible) :
  temp_corr 𝓒_lt_𝓗 = H.Qrel / H.Qabs :=
  calc temp_corr 𝓒_lt_𝓗
       = 1 - H.eff : by rw [usual_engine_cycle.rev_eff_universal _ hH]
    ...= H.Qrel / H.Qabs : by { rw H.eff_from_Qabs_Qrel, ring }
end

section
variables {𝓐 𝓑 𝓒 : reservoir} (𝓒_lt_𝓑 : 𝓒 < 𝓑) (𝓑_lt_𝓐 : 𝓑 < 𝓐)
theorem temp_corr_trans :
  temp_corr (𝓒_lt_𝓑.trans 𝓑_lt_𝓐) = (temp_corr 𝓒_lt_𝓑) * (temp_corr 𝓑_lt_𝓐) :=
  let 𝓒_lt_𝓐 := 𝓒_lt_𝓑.trans 𝓑_lt_𝓐 in
  let ⟨H𝓐𝓑, hH𝓐𝓑⟩ := usual_engine_cycle.exists_reversible 𝓑_lt_𝓐 in
  let ⟨H𝓑𝓒, hH𝓑𝓒, hQ⟩ := usual_engine_cycle.exists_rev_abs 𝓒_lt_𝓑 H𝓐𝓑.do_rel in by {
  let H𝓐𝓒' := H𝓐𝓑.to_cycle + H𝓑𝓒.to_cycle,
  have H𝓑𝓒_no𝓐 : 𝓐 ∉ H𝓑𝓒.𝓠.support, {
    rw H𝓑𝓒.two_rsv.elim_left,
    simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
    exact ⟨ne_of_gt 𝓑_lt_𝓐, ne_of_gt 𝓒_lt_𝓐⟩, },
  have H𝓐𝓑_no𝓒 : 𝓒 ∉ H𝓐𝓑.𝓠.support, {
    rw H𝓐𝓑.two_rsv.elim_left,
    simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
    exact ⟨ne_of_lt 𝓒_lt_𝓐, ne_of_lt 𝓒_lt_𝓑⟩, },
  have H𝓐𝓒'Qabs :=
    calc H𝓐𝓒'.𝓠 𝓐
         = H𝓐𝓑.𝓠 𝓐 + H𝓑𝓒.𝓠 𝓐 : rfl
      ...= H𝓐𝓑.𝓠 𝓐            : by rw [finsupp.not_mem_support_iff.elim_left H𝓑𝓒_no𝓐, add_zero]
      ...= H𝓐𝓑.Qabs            : H𝓐𝓑.Qabs_one_rsv.symm,
  have H𝓐𝓒'Qrel :=
    calc H𝓐𝓒'.𝓠 𝓒
         = H𝓐𝓑.𝓠 𝓒 + H𝓑𝓒.𝓠 𝓒 : rfl
      ...=            H𝓑𝓒.𝓠 𝓒 : by rw [finsupp.not_mem_support_iff.elim_left H𝓐𝓑_no𝓒, zero_add]
      ...=           -H𝓑𝓒.Qrel : by rw [←neg_neg (H𝓑𝓒.𝓠 𝓒), ←H𝓑𝓒.Qrel_one_rsv],
  have do_abs_rsv : H𝓐𝓒'.𝓠 𝓐 > 0, from H𝓐𝓒'Qabs.symm ▸ H𝓐𝓑.do_abs,
  have do_rel_rsv : H𝓐𝓒'.𝓠 𝓒 < 0, {
    rw H𝓐𝓒'Qrel,
    exact neg_lt_zero.elim_right H𝓑𝓒.do_rel, },
  let H𝓐𝓒 : usual_engine_cycle 𝓒_lt_𝓐 :=
    { two_rsv := by {
        refine ⟨_, ne_of_gt 𝓒_lt_𝓐⟩,
        have : H𝓐𝓒'.𝓠 = H𝓐𝓑.𝓠 + H𝓑𝓒.𝓠, from rfl, rw this,
        apply finsupp.support_add_exact,
        { simp only [finset.mem_insert, finset.mem_singleton, ne.def, forall_eq_or_imp, forall_eq],
          split,
            exact ne_of_gt do_abs_rsv,
            exact ne_of_lt do_rel_rsv, },
        { have : (H𝓐𝓑.𝓠.support ∪ H𝓑𝓒.𝓠.support) \ {𝓐, 𝓒} = {𝓑}, {
            rw [H𝓐𝓑.two_rsv.elim_left, H𝓑𝓒.two_rsv.elim_left],
            ext, simp, split,
            { tauto, },
            { assume h𝓑,
              split,
              { exact or.inl h𝓑, },
              { rw [not_or_distrib, h𝓑],
                exact ⟨ne_of_lt 𝓑_lt_𝓐, ne_of_gt 𝓒_lt_𝓑⟩, } } },
          simp only [this, finset.mem_singleton, forall_eq],
          calc H𝓐𝓑.𝓠 𝓑 + H𝓑𝓒.𝓠 𝓑
               = -H𝓐𝓑.Qrel + H𝓑𝓒.Qabs : by rw [H𝓐𝓑.Qrel_one_rsv, neg_neg, H𝓑𝓒.Qabs_one_rsv]
            ...= 0                     : by { rw hQ, ring }, } },
      do_abs_rsv := do_abs_rsv,
      do_rel_rsv := do_rel_rsv,
      do_work :=
        calc H𝓐𝓒'.𝓦
             = H𝓐𝓑.𝓦 + H𝓑𝓒.𝓦 : cycle.𝓦_add
          ...> 0                : add_pos H𝓐𝓑.do_work H𝓑𝓒.do_work,
      ..H𝓐𝓒' },
  have := temp_corr_eq_Qratio 𝓑_lt_𝓐 hH𝓐𝓑, rw this,
  have := temp_corr_eq_Qratio 𝓒_lt_𝓑 hH𝓑𝓒, rw this,
  rw [hQ, div_mul_div_cancel _ (ne_of_gt H𝓐𝓑.do_rel)],
  have : H𝓐𝓒.reversible, from cycle.reversible_add hH𝓐𝓑 hH𝓑𝓒,
  have := temp_corr_eq_Qratio 𝓒_lt_𝓐 this, rw this,
  rw [H𝓐𝓒.Qabs_one_rsv, H𝓐𝓒'Qabs],
  rw [H𝓐𝓒.Qrel_one_rsv, H𝓐𝓒'Qrel, neg_neg], }
/-- `temp_corr 𝓒_lt_𝓗` is `strict_mono` as a function of `𝓒` -/
lemma temp_corr_strict_mono : temp_corr (𝓒_lt_𝓑.trans 𝓑_lt_𝓐) < temp_corr 𝓑_lt_𝓐 := by {
  rw temp_corr_trans 𝓒_lt_𝓑 𝓑_lt_𝓐,
  exact (mul_lt_iff_lt_one_left (temp_corr_pos _)).elim_right (temp_corr_lt_one _), }
end

/-- `ref`erence `sys`tem -/
@[reducible] def ref_sys : equil_system := water_triple_point
/-- reference temperature of `ref_sys` -/
@[reducible] def ref_temp : ℝ₊ := ⟨273.16, by cancel_denoms⟩
/-- thermodynamic `temp`erature of `reservoir`s -/
def temp : reservoir ↪o ℝ₊ := order_embedding.of_strict_mono
  ( λ 𝓣,
    if        heq : 𝓣 = ⟦ref_sys⟧ then
      ref_temp
    else if   hlt : 𝓣 < ⟦ref_sys⟧ then
      ⟨(temp_corr hlt) * ref_temp, mul_pos (temp_corr_pos _) ref_temp.property⟩
    else have hgt : 𝓣 > ⟦ref_sys⟧, from ne.lt_of_le' heq (le_of_not_gt hlt),
      ⟨ref_temp / (temp_corr hgt), div_pos ref_temp.property (temp_corr_pos _)⟩ )
  ( assume 𝓒 𝓗 𝓒_lt_𝓗,
    if        h𝓗lt : 𝓗 < ⟦ref_sys⟧ then by {
      have h𝓒lt := 𝓒_lt_𝓗.trans h𝓗lt,
      simp only [ne_of_lt h𝓒lt, h𝓒lt, ne_of_lt h𝓗lt, h𝓗lt,
        dif_pos, dite_eq_ite, if_false],
      refine mul_lt_mul _ (le_rfl) (ref_temp.property) (le_of_lt (temp_corr_pos _)),
      exact temp_corr_strict_mono 𝓒_lt_𝓗 h𝓗lt, }
    else if   h𝓗eq : 𝓗 = ⟦ref_sys⟧ then by {
      have h𝓒lt : 𝓒 < ⟦ref_sys⟧, from h𝓗eq ▸ 𝓒_lt_𝓗,
      simp only [ne_of_lt h𝓒lt, h𝓒lt, h𝓗eq,
        dif_pos, not_false_iff, dif_neg],
      exact (mul_lt_iff_lt_one_left ref_temp.property).elim_right (temp_corr_lt_one _), }
    else have h𝓗gt : 𝓗 > ⟦ref_sys⟧, from
        ne.lt_of_le (ne.symm h𝓗eq) (le_of_not_gt h𝓗lt), by {
      simp only [ne_of_gt h𝓗gt, not_lt_of_gt h𝓗gt,
        not_false_iff, dif_neg],
      apply subtype.coe_lt_coe.elim_left,
      rw [subtype.coe_mk (↑ref_temp / temp_corr h𝓗gt) _, div_eq_mul_one_div],
      exact if  h𝓒lt : 𝓒 < ⟦ref_sys⟧ then by {
        simp only [ne_of_lt h𝓒lt, h𝓒lt,
          dif_pos, dite_eq_ite, if_false],
        rw [subtype.coe_mk, mul_comm (temp_corr h𝓒lt) _],
        refine mul_lt_mul' (le_rfl) _ (le_of_lt (temp_corr_pos _)) (ref_temp.property),
          apply (lt_div_iff (temp_corr_pos _)).elim_right,
          rw ←temp_corr_trans,
          exact temp_corr_lt_one _, }
      else if   h𝓒eq : 𝓒 = ⟦ref_sys⟧ then by {
        simp only [h𝓒eq, dif_pos],
        apply lt_mul_right ref_temp.property,
          apply (lt_div_iff (temp_corr_pos _)).elim_right,
          rw one_mul,
          exact temp_corr_lt_one _, }
      else have h𝓒gt : 𝓒 > ⟦ref_sys⟧, from
          ne.lt_of_le (ne.symm h𝓒eq) (le_of_not_gt h𝓒lt), by {
        simp only [ne_of_gt h𝓒gt, not_lt_of_gt h𝓒gt,
          not_false_iff, dif_neg],
        rw [subtype.coe_mk, div_eq_mul_one_div _ (temp_corr h𝓒gt)],
        refine mul_lt_mul' (le_rfl) _ _ (ref_temp.property),
        { apply (one_div_lt_one_div (temp_corr_pos _) (temp_corr_pos _)).elim_right,
          rw temp_corr_trans h𝓒gt 𝓒_lt_𝓗,
          exact (mul_lt_iff_lt_one_right (temp_corr_pos _)).elim_right (temp_corr_lt_one _), },
        { exact div_nonneg zero_le_one (le_of_lt (temp_corr_pos _)), } } } )
--

end reservoir

/-!
### Applications of thermodynamic temperature
-/

/- namespace usual_engine_cycle
variables {𝓗 𝓒 : reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

lemma rev_eff_from_temp : rev_eff 𝓒_lt_𝓗 = 1 - 𝓒.temp / 𝓗.temp := sorry

end usual_engine_cycle -/

/-!
## The absolute zero

TODO
* existence of the absolute zero as a limit ?
* require `rsv_no_min` ?
* behavior of `usual_engine_cycle` when 𝓒.temp -> 0
---------------------------------------------------------------------------------------------------/

end thermodynamics
