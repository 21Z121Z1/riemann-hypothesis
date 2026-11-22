import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CuspRegionVolumeFiniteProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk

def B1 (C c : ℝ) : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}

theorem measurableSet_cusp_region (C c : ℝ) : MeasurableSet (B1 C c) := by
  have h1 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.re| :=
    (continuous_abs.comp (Complex.continuous_re.comp continuous_subtype_val)).measurable
  have h2 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.im| :=
    (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)

theorem pt_bound (C c : ℝ) (hc : 0 < c) (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
    1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hb : c ^ 2 ≤ t.im ^ 2 := by
    nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
  have ha : t.re ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
  have hbpos : 0 < t.im ^ 2 := lt_of_lt_of_le hc2 hb
  have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
    have h3 : 1 ≤ t.im ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hbpos (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  calc 1 / t.im ^ 2 = 1 * (1 / t.im ^ 2) := (one_mul _).symm
    _ ≤ ((1 + C ^ 2) * (1 + t.re ^ 2)⁻¹) * ((1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by ring

theorem integ_G : ∫⁻ t : ℂ, ENNReal.ofReal ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ⊤ := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) :=
    h1.mul_prod h1
  have h3 : Integrable (fun t : ℂ => (1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) :=
    (Complex.volume_preserving_equiv_real_prod.integrable_comp h2.aestronglyMeasurable).2 h2
  exact h3.lintegral_lt_top

private theorem volume_eq_lintegral_inv_im_sq_comap (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
    (volume : Measure P) (show Set P from s) = ∫⁻ z in s, ENNReal.ofReal (1 / z.1.im ^ 2)
      ∂(Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
  withDensity_apply _ hs

private theorem lintegral_comap_im_ne_zero_le_lintegral (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume) ≤ ∫⁻ t, f t := by
  have hs : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet
  calc ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume)
      = ∫⁻ t in {z : ℂ | z.im ≠ 0}, f t := lintegral_subtype_comap hs f
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

private theorem lintegral_mul_inv_one_add_sq_lt_top (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t : ℂ, ENNReal.ofReal (K * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) < ⊤ := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top integ_G

private theorem lintegral_B1_inv_im_sq_le_lintegral (C c : ℝ) (hc : 0 < c) :
    ∫⁻ z in B1 C c, ENNReal.ofReal (1 / z.1.im ^ 2) ∂(Measure.comap Subtype.val volume) ≤
      ∫⁻ z : {z : ℂ // z.im ≠ 0}, ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
          ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹)) ∂(Measure.comap Subtype.val volume) := by
  refine le_trans (setLIntegral_mono' (measurableSet_cusp_region C c) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (pt_bound C c hc z.1 hz.1 hz.2)

theorem volume_cusp_region_lt_top (C c : ℝ) (hc : 0 < c) : (volume : Measure P) (show Set P from B1 C c) < ⊤ := by
  have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
  rw [volume_eq_lintegral_inv_im_sq_comap _ (measurableSet_cusp_region C c)]
  exact lt_of_le_of_lt ((lintegral_B1_inv_im_sq_le_lintegral C c hc).trans (lintegral_comap_im_ne_zero_le_lintegral _)) (lintegral_mul_inv_one_add_sq_lt_top _ hK0)

end UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk.CuspRegionVolume in
theorem UpperTheory.Esk.cusp_region_volume_finite_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.E3 := by
  intro hB1a _ hC2 hE0a hE0d
  intro F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -, -, -, -⟩ := hE0a F I Gf D hD
  obtain ⟨-, hsm, -, -, -, -, -, -, -, hsurj, -⟩ := hE0d F I Gf D hD
  haveI : Countable (PG F) := hcnt
  haveI : SigmaFinite (volume : Measure D.Xs) := hsf
  haveI : SigmaFinite (volume : Measure P) := hB1a.1
  haveI : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have h01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
  let T : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S : Set Gf)
  let U : Set D.Xs := Set.univ.pi fun _ : I => (show Set P from B1 C c)
  have hT : T.Finite := S.finite_toSet.image _
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_cusp_region C c
  have hS : MeasurableSet (T ×ˢ U) := (MeasurableSet.of_discrete).prod hU
  have hcover : ∀ y : D.Y, ∃ g : PG F, g • y ∈ T ×ˢ U := by
    intro y
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1)
    obtain ⟨γ, hγ⟩ := hsurj s hs0
    set y' : D.Y := (γ : PG F) • y with hy'
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y)
      rw [hsm ![0, 1] h01 γ y, hγ]
      exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_⟩
    rw [mul_smul, ← hy']
    refine ⟨?_, ?_⟩
    · have hy1 : ((D.rep y'.1 : Gf) : Gf ⧸ D.H) = y'.1 := Quotient.out_eq _
      have hm := D.mk_smulO bb (D.rep y'.1)
      rw [hy1] at hm
      refine ⟨x', hx'S, ?_⟩
      show (show D.Om from ((x' : Gf) : Gf ⧸ D.H)) = (bb : PG F) • y'.1
      rw [hm, hjx]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hhH
    · show (bb : PG F) • y'.2 ∈ U
      rw [D.mk_smulX]
      intro v _
      exact ⟨(hSg v).1, (hSg v).2.1⟩
  have hfin : D.μY (T ×ˢ U) < ⊤ := by
    unfold Dat.μY
    rw [Measure.prod_prod]
    refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 hT) ?_
    change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => (show Set P from B1 C c)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => volume_cusp_region_lt_top C c hc
  exact lt_of_le_of_lt ((hC2 (PG F) D.Y).2 D.μY hPY b hb _ hS hcover) hfin
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E5OfReproducingFormula
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

theorem rep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h := by
  have h1 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  refine ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans h1.symm)⟩, ?_⟩
  simp

theorem ee_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hu' : (h : Gf)⁻¹ * u ∈ D.H := D.H.mul_mem (D.H.inv_mem h.2) hu
    rw [dif_pos hu', dif_pos hu, mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp
  · have hu' : (h : Gf)⁻¹ * u ∉ D.H := fun hh => hu (by simpa using D.H.mul_mem h.2 hh)
    rw [dif_neg hu', dif_neg hu, zero_mul]

theorem ee_one : D.ee 1 = 1 := by
  unfold Dat.ee
  rw [dif_pos D.H.one_mem]
  exact congrArg Units.val (map_one D.χ)

theorem smul_fst (γ : PG F) (ω : D.Om) : γ • ω = (((D.j γ.out * D.rep ω : Gf)) : Gf ⧸ D.H) := by
  have h2 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← h2]
  exact D.mk_smulO γ.out (D.rep ω)

theorem smul_snd (γ : PG F) (w : D.Xs) : γ • w = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

theorem term (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (γ : PG F) (y : D.Y) :
    D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1)) =
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out y.2) * D.J k γ.out y.2) * f (y.2, D.rep y.1) := by
  obtain ⟨h, hh⟩ := rep_eq D (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smul_fst])
  have hs2 : (γ • y).2 = D.act γ.out y.2 := by rw [Prod.smul_snd, smul_snd]
  have key : (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) := by
    group
  rw [hh, hs2, hf.lev, show f (D.act γ.out y.2, D.j γ.out * D.rep y.1) = D.J k γ.out y.2 * f (y.2, D.rep y.1) from hf.aut _ _ _, key, ← ee_mul D h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]
  ring

open Classical in
theorem supp (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (y : D.Y) :
    D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) =
      if y.1 = ((x : Gf) : Gf ⧸ D.H) then qq k z y.2 * f (y.2, x) else 0 := by
  split_ifs with hy
  · obtain ⟨h, hh⟩ := rep_eq D y.1 x hy.symm
    have he := ee_mul D h 1
    rw [ee_one, mul_one] at he
    have key : (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ := by group
    rw [hh, show f (y.2, x * (h : Gf)) = (D.χ h : ℂ) * f (y.2, x) from hf.lev _ _ _, key]
    calc _ = (D.ee ((h : Gf)⁻¹) * (D.χ h : ℂ)) * (qq k z y.2 * f (y.2, x)) := by ring
      _ = _ := by rw [he, one_mul]
  · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := by
      intro hm
      apply hy
      have h1 : ((D.rep y.1 : Gf) : Gf ⧸ D.H) = y.1 := QuotientGroup.out_eq' _
      exact h1.symm.trans (QuotientGroup.eq.2 hm)
    have h0 : D.ee ((D.rep y.1)⁻¹ * x) = 0 := by
      unfold Dat.ee
      rw [dif_neg hn]
    rw [h0, zero_mul]

end UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk UpperTheory.Esk.ReproducingKernelExpansion in
theorem UpperTheory.Esk.e5_of_reproducing_formula : UpperTheory.Esk.B1b → UpperTheory.Esk.C3 → UpperTheory.Esk.E0a → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.MultivariableReproducingFormula → UpperTheory.Esk.E5 := by
  intro hB1 hC3 hE0 _hE4 hB3 F I Gf _ _ _ D hAx k hk _hcomp b hb f hf p
  obtain ⟨z, x⟩ := p
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount
  have := hsf
  have := hborel
  have := hAx.cO
  let ω₀ : D.Om := ((x : Gf) : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ)
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := by
    funext y
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) = a y.1 * h0 y.2
    rw [supp D k f hf z x y]
    by_cases hy : y.1 = ((x : Gf) : Gf ⧸ D.H)
    · rw [if_pos hy]
      have ha : a y.1 = 1 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_pos (show y.1 ∈ ({ω₀} : Set D.Om) from hy)]
      rw [ha, one_mul]
    · rw [if_neg hy]
      have ha : a y.1 = 0 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_neg (show y.1 ∉ ({ω₀} : Set D.Om) from hy)]
      rw [ha, zero_mul]
  have hqc : Continuous fun w : X I => qq k z w := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB1.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hh0c : Continuous fun w : X I => qq k z w * f (w, x) := hqc.mul (hf.hol x).1
  have hh0m : Measurable h0 := hh0c.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) ⟨C, fun w => hC w x⟩ z
  have hh0i : Integrable h0 := hB.1
  have ham : Measurable a := measurable_const.indicator (MeasurableSet.of_discrete)
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff (MeasurableSet.of_discrete)).2
      ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have ha1 : ∫ ω, a ω ∂Measure.count = 1 := by
    simp only [a]
    rw [integral_indicator (MeasurableSet.of_discrete)]
    simp
  have hGm : Measurable G := by
    rw [hG]
    exact (ham.comp measurable_fst).mul (hh0m.comp measurable_snd)
  have hGi : Integrable G D.μY := by
    rw [hG]
    unfold Dat.μY
    exact MeasureTheory.Integrable.mul_prod hai hh0i
  have hKf : ∀ y : D.Y, D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    intro y
    unfold Dat.Kern
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    exact (term D k f hf z x γ y).symm
  have hCC := hC3 (PG F) D.Y D.μY hpres b hb G hGm hGi
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := hCC.2
    _ = ∫ y, a y.1 * h0 y.2 ∂(Measure.count.prod volume) := by rw [hG]; rfl
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := integral_prod_mul _ _
    _ = f (z, x) := by rw [ha1, one_mul]; exact hB.2
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E6OfLinearTraceIdentity
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.LinearTraceIdentity

open UpperTheory.Esk

theorem op_kern {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf)
    (y : D.Y) (hs : ∀ i, Summable fun γ : PG F =>
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * (D.rep y.1 * a i)) * (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)) :
    Dat.Op a (D.Kern k y) (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
  show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
  simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  refine tsum_congr fun γ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

end UpperTheory.Esk.LinearTraceIdentity

theorem UpperTheory.Esk.e6_of_linear_trace_identity : UpperTheory.Esk.E0a → UpperTheory.Esk.FormsStableUnderOperators → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E3 → UpperTheory.Esk.E4 → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.E5 → UpperTheory.Esk.LinTr → UpperTheory.Esk.E6 := by
  intro hE0a hE0b _ hE3 hE4 hE4b hE5 hLin
  intro F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hM : ∀ f, f ∈ D.M k ↔ D.IsForm k f := (hE0b F I Gf D hH.ax k).1
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hE5' := hE5 F I Gf D hH.ax k hH.four hH.compat b hb
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure D.Y, ν = D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact MeasureTheory.isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint : ∀ g : D.Y → ℂ, ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY := by
    intro g
    rw [hν, integral_withDensity_eq_integral_smul hbm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  obtain ⟨K, hK⟩ : ∃ K : D.Y → D.M k, ∀ y, (K y).1 = D.Kern k y :=
    ⟨fun y => ⟨D.Kern k y, (hM _).2 (hE4' y)⟩, fun _ => rfl⟩
  have hn0 : Measurable fun z : X I => nrm k z := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    exact (continuous_abs.measurable.comp
      (Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))).pow_const _
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := hn0.comp measurable_snd
  have hn_pos : ∀ y : D.Y, 0 < nrm k y.2 := fun y =>
    Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.mpr (y.2 v).2) _
  have hK_meas : ∀ p, Measurable fun y => (K y).1 p := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.1
  have hf_meas : ∀ f : D.M k, Measurable fun y : D.Y => f.1 (y.2, D.rep y.1) := by
    intro f
    have hF := (hM f.1).1 f.2
    haveI : Countable D.Om := hH.ax.cO
    refine measurable_from_prod_countable_right fun ω => ?_
    have hc : Measurable fun z : X I => f.1 (z, D.rep ω) := ((hF.hol (D.rep ω)).1).measurable
    exact hc
  have hK_bdd : ∀ p, ∃ C, ∀ y, ‖(K y).1 p‖ ≤ C * nrm k y.2 := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.2
  have hf_bdd : ∀ f : D.M k, ∃ C, ∀ y : D.Y, ‖f.1 (y.2, D.rep y.1)‖ * nrm k y.2 ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := ((hM f.1).1 f.2).bdd
    exact ⟨C, fun y => hC _ _⟩
  have hrep : ∀ (f : D.M k) p, ∫ y, (K y).1 p * f.1 (y.2, D.rep y.1) ∂ν = f.1 p := by
    intro f p
    rw [hint]
    simp only [hK]
    exact hE5' f.1 ((hM f.1).1 f.2) p
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := hLin (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas hn_pos hK_meas hf_meas hK_bdd hf_bdd hrep
  have hval : ∀ y : D.Y, ((Dat.Op a).restrict h (K y)).1 (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    intro y
    rw [LinearMap.restrict_coe_apply, hK]
    exact LinearTraceIdentity.op_kern D k a y (fun i => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm)
  have hm2 : Measurable fun y => ∑' γ : PG F, D.kk k a γ y := by
    simpa only [hval] using hmeas
  refine ⟨?_, ?_⟩
  · have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν := by
      refine (integrable_const C).mono' hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have := hC y
      simp only [hval] at this
      exact this
    rw [hν, MeasureTheory.integrable_withDensity_iff_integrable_smul hbm] at hgi
    refine hgi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  · rw [htr, hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hval]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSumBoundedProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace UpperTheory.Esk

namespace KernelSumBound

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num) h.le) (by positivity)
  · exact le_rfl

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w := by
  unfold Kap
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

theorem bound (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (C₀ : ℝ)
    (hk : ∀ (γ : PG F) (y : D.Y), ‖D.kk k a γ y‖ ≤ C₀ * Kap k y.2 (γ • y.2 : D.Xs))
    (hsupp : ∀ (γ : PG F) (ω : D.Om), D.Te a γ.out (D.rep ω) ≠ 0 →
      ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H))
    (y : D.Y) (B : ℝ)
    (hB : ∀ ω' : D.Om, ∑' γ : {γ : PG F // γ • y.1 = ω'},
      ENNReal.ofReal (Kap k y.2 (γ.1 • y.2 : D.Xs)) ≤ ENNReal.ofReal B) :
    ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
  classical
  have hpt : ∀ γ : PG F, ‖D.kk k a γ y‖ₑ ≤ ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := by
    intro γ
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have hz : D.kk k a γ y = 0 := by
        simp only [Dat.kk, Dat.kt, h0, zero_mul]
      rw [hz, enorm_zero]
      exact zero_le
    · obtain ⟨i, hi⟩ := hsupp γ y.1 h0
      calc ‖D.kk k a γ y‖ₑ = ENNReal.ofReal ‖D.kk k a γ y‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (C₀ * Kap k y.2 (γ • y.2 : D.Xs)) := ENNReal.ofReal_le_ofReal (hk γ y)
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)) :=
            ENNReal.ofReal_mul' (Kap_nonneg k _ _)
        _ = Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
            (Set.indicator_of_mem
              (show γ ∈ {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)
              (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)))).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a j : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ)
            (fun _ _ => zero_le) (Finset.mem_univ i)
  have hsub : ∀ i : ι, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal B := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    exact hB ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)
  calc ∑' γ : PG F, ‖D.kk k a γ y‖ₑ
      ≤ ∑' γ : PG F, ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑ i, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : ι, ENNReal.ofReal C₀ * ENNReal.ofReal B := Finset.sum_le_sum fun i _ => hsub i
    _ = Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end KernelSumBound

end UpperTheory.Esk

theorem UpperTheory.Esk.kernel_sum_bounded_proof : UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.E2 := by
  intro h0c h0d hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨-, -, -, ⟨C₀, hC₀⟩, hsupp, -⟩ := h0c F I Gf ι D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, -⟩ := h0d F I Gf D hyp.ax
  have key : ∀ T : ℝ, ∀ y ∈ D.abelian₂ T, ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≤
      Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal (max C 0 * (1 + T))) := by
    intro T y hy
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hpos : 0 < D.HtY s y := lt_of_lt_of_le hc₀ hcs
    have hle : D.HtY s y ≤ T := hy s hs
    refine UpperTheory.Esk.KernelSumBound.bound D k a C₀ hC₀ hsupp y (max C 0 * (1 + T)) fun ω' => ?_
    refine (hC y s hs hcs ω' y.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left C 0) (by linarith) (by linarith) (le_max_right C 0)
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal), fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := hT y
    have hfin : ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) (key T₀ y (hT₀ T₀ le_rfl))
    exact (ENNReal.summable_toReal hfin).congr fun γ => toReal_enorm _
  · refine (key T y hy).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
    all_goals rfl
end
end

