import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntIntegrableOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PiInvApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0009
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0010

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bePos_hyp (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) : BesselPositivity.Hyp D := by
  have hS := stSInt h
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, a16, -, a18, -, a20, a21, a22, -, -, -, -, -⟩ := h1
  exact ⟨a22, a21, a20, a16, a15, a13 k r Wp Wp D, a18, h17, h16, fun b hb => hS k r Wp D hD b hb⟩

private theorem two_mul_AB_le_aM (k r : ℕ) : 2 * AB k r ≤ aM k r := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  simp only [AB, aM, nR]
  push_cast
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hr hr, mul_nonneg hk hk]

theorem two_AB_le_aM {k r : ℕ} (hk : 1 ≤ k) : 2 * AB k r ≤ aM k r := by
  exact two_mul_AB_le_aM k r

private theorem exists_bessel_coef_of_mem_Vfl {k r : ℕ} (X : SigData k r) (haM : aM k r ≤ X.a) {u : X.Hs}
    (hu : u ∈ Vfl X) : ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, ⟨?_, le_max_right _ _, (two_mul_AB_le_aM k r).trans haM, ?_⟩⟩
  ·
    have h1 := X.rep.2.2 u
    exact (continuous_const.inner continuous_id).comp_continuousOn h1
  · intro y hy
    have ht : 0 ≤ gN y ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact (hC y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)

theorem bePos_coef {k r : ℕ} (X : SigData k r) (hk : 1 ≤ k) (haM : aM k r ≤ X.a) {u : X.Hs} (hu : u ∈ Vfl X) :
    ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  exact exists_bessel_coef_of_mem_Vfl X haM hu

private lemma inner_apply_right_inverse_eq_inner_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T S : E →L[ℂ] E)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hTS : T.comp S = 1) (x : E) : ⟪x, S x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E := ⟨T.toLinearMap, hT⟩
  have h1 : ⟪T x, T (S x)⟫_ℂ = ⟪x, S x⟫_ℂ := L.inner_map_map x (S x)
  have h2 : T (S x) = x := by
    have := congrArg (fun F : E →L[ℂ] E => F x) hTS
    simpa using this
  rw [h2] at h1
  exact h1.symm

theorem bePos_inner_eq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (H : BesselPositivity.Hyp D)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} {C a : ℝ} (hc : BesselPositivity.Coef (mc X u X.w) C a) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ = (d : ℂ) * ∫ g, BesselPositivity.phi D (mc X u X.w) ξ (Matrix.of g) ∂D.μG := by
  obtain ⟨hd0, hdS⟩ := hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hA : ⟪ξ, beOp D X u u ξ⟫_ℂ = ∫ p, ⟪ξ, beInt D X u u p ξ⟫_ℂ ∂(D.μW.prod D.μN) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, integral_inner (hI.apply_continuousLinearMap ξ)]
  have hGae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    first
    | exact ae_iff.2 D.haarG.conc
    | exact measure_mono_null (fun a ha => ha) D.haarG.conc
  rw [hA, ← BesselPositivity.fubini1 D H hc ξ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [BesselPositivity.ae_SS (D := D)] with p hp
  have hs : BesselPositivity.sP p ∈ GV k r := BesselPositivity.sP_mem H.cg hp

  have hSch : ∫ g, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) ∂D.μG =
      mc X u u (BesselPositivity.sP p) / d := by
    have hc1 : ∀ᵐ g ∂D.μG, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) =
        mc X (X.σ (BesselPositivity.sP p) u) X.w (Matrix.of g) * star (mc X u X.w (Matrix.of g)) := by
      filter_upwards [hGae] with g hg
      simp only [mc, X.rep.1.2 _ hg _ hs, ContinuousLinearMap.comp_apply]
    rw [integral_congr_ae hc1, ((hdS (X.σ (BesselPositivity.sP p) u) X.w u X.w).2)]
    simp only [mc, inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hSch]
  have ha := hp.1
  have hinv := inner_apply_right_inverse_eq_inner_of_isometry (D.π (Matrix.of p.1)) (D.π (Matrix.of p.1)⁻¹) (D.π_unitary _ ha) (by
    rw [← D.π_rep.2 _ ha _ ((H.cw k r D.z).inv_mem _ ha), Matrix.mul_nonsing_inv _ ((H.cw k r D.z).unit _ ha),
      D.π_rep.1]) ξ
  have hc2 : star ⟪ξ, D.π (Matrix.of p.1) ξ⟫_ℂ = ⟪D.π (Matrix.of p.1) ξ, ξ⟫_ℂ := inner_conj_symm _ _
  simp only [beInt, BesselPositivity.Kf, BesselPositivity.PiO, BesselPositivity.sP, inner_smul_right, ContinuousLinearMap.smul_apply,
    inner_smul_right, star_mul', hinv, hc2]
  field_simp

theorem bePos_identity (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} (hu : u ∈ Vfl X) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ =
      (d : ℂ) * ((∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG : ℝ) : ℂ) := by
  obtain ⟨C, hc⟩ := exists_bessel_coef_of_mem_Vfl X haM hu
  have H := bePos_hyp h D hD
  rw [bePos_inner_eq D X H hd hc ξ hI, BesselPositivity.phi_eq D H hc ξ]

theorem stBePos (h : UnitaryGroupStructuralFacts) : StBePos := by
  intro k r Wp _ _ _ D X hD hX ha u hu ξ
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hX
  by_cases hI : Integrable (beInt D X u u) (D.μW.prod D.μN)
  swap
  · have h0 : beOp D X u u = 0 := integral_undef hI
    rw [h0]
    simp
  rw [bePos_identity h D X hD ha hd hu ξ hI]
  have h0 : 0 ≤ ∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG :=
    integral_nonneg fun g => mul_nonneg (BesselPositivity.bet_nonneg (D := D) _) (sq_nonneg _)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg hd.1.le h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MinorsOnOfDD
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_scalar (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) {u v : X.Hs} (e f : Wp)
    (hI : Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG)
    (hR : beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ) D.μG ∧
    ⟪e, beOp D X u v f⟫_ℂ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ ∂D.μG := by
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)
  have hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ := fun A => by
    simp [L, innerSL_apply_apply]
  have hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ := fun c A => by
    rw [map_smul, hL, smul_eq_mul]
  refine ⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩
  rw [hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)

theorem opint (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {b : ℝ}
    (hab : AB k r ≤ X.a - b) {u v : X.Hs} (hu : u ∈ Vfl X)
    (hbv : ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨Cc, hCc0, hCc⟩ := coef_bound X ha0 hu
  obtain ⟨Cb, hCb⟩ := hbv
  have hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG :=
    (show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from
      (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)
  refine ((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_
  filter_upwards [ae_G D] with y hy
  rw [norm_smul]
  have e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b := by
    rw [← Real.rpow_add (gN_pos hy)]; ring_nf
  rw [e]
  calc ‖⟪X.σ (Matrix.of y) X.w, u⟫_ℂ‖ * ‖beOp D X (X.σ (Matrix.of y) X.w) v‖
      ≤ (Cc * gN (Matrix.of y) ^ (-X.a)) * (Cb * gN (Matrix.of y) ^ b) :=
        mul_le_mul (hCc _ hy) (hCb _ hy) (norm_nonneg _)
          (mul_nonneg hCc0 (Real.rpow_nonneg (gN_nonneg _) _))
    _ = _ := by ring

theorem ext1 (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {d b : ℝ}
    (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    {u₂ u₄ : X.Hs} (hu₂ : u₂ ∈ Vfl X) (hu₄ : u₄ ∈ Vfl X) (u₃ : X.Hs) (e₁ e₂ e₃ e₄ : Wp)
    (h : ∀ φ : Mat k r → ℂ, IsTestG φ → Mn D X (sigInt D X φ X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) :
    ∀ u ∈ Vfl X, Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  refine vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h
  · let L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)
    let L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)
    have m2 := L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)
    have m4 := L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)
    exact (m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)
  · obtain ⟨C₂, h₂⟩ := hbe u₂ hu₂
    obtain ⟨C₄, h₄⟩ := hbe u₄ hu₄
    refine ⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
      ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩
    simp only [Mn]
    calc ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
          ⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖
        ≤ ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          ‖⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₄ y hy) (by positivity))) (norm_nonneg _))
      _ = _ := by ring
  · intro u hu
    obtain ⟨i2, r2⟩ := repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)
    obtain ⟨i4, r4⟩ := repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)
    have e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ =
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₄ e₄⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ := fun y => by simp only [Mn]; ring
    show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG
    simp only [e5]
    rw [integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]
    simp only [Mn]
    rw [r2, r4]
    ring

theorem mn_swap (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₃ u₂ u₁ u₄ e₃ e₂ e₁ e₄ = -Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ := by
  unfold Mn; ring

theorem mn_herm (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    {u₁ u₂ u₃ u₄ : X.Hs} (h₁ : u₁ ∈ Vfl X) (h₂ : u₂ ∈ Vfl X) (h₃ : u₃ ∈ Vfl X) (h₄ : u₄ ∈ Vfl X)
    (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₂ u₁ u₄ u₃ e₂ e₁ e₄ e₃ = starRingEnd ℂ (Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄) := by
  have kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp,
      ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ := by
    intro u hu v hv e f
    rw [hH v hv u hu e f, inner_conj_symm]
  unfold Mn
  rw [kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]
  simp only [map_sub, map_mul]
  ring

theorem minorsOn_of_DD (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a)
    {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hDD : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) : MinorsOn D X := by
  have hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X := fun φ hφ => ⟨φ, hφ, rfl⟩
  have S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  have S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  have S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃,
      S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]
  have S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
  have : Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  exact sub_eq_zero.1 this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UuInv
section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  let l : Fin (2 * r + k + 1) :=
    ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single l]
  · simp only [Hpk, l, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ l.val := fun h => hb (Fin.ext h)
    simp only [l, Fin.val_mk] at hb'
    have hbl := b.isLt
    apply mul_eq_zero_of_left
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hb' ⊢ <;> first | (exfalso; omega) | rfl
  · intro h
    exact absurd (Finset.mem_univ l) h

lemma uu_inv {z : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {u : Mat k r}
    (hu : u ∈ UUset k r z γ) : u⁻¹ ∈ UUset k r z γ := by
  simp only [UUset, UWset, UH, Set.mem_setOf_eq] at hu ⊢
  obtain ⟨⟨hH, hb, hz⟩, hw⟩ := hu
  have hdH : (Hpk k r).det ≠ 0 := by
    have h := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdu : IsUnit u.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hdH h.symm
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hdu
  have h3 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hdu
  have h2 : (u⁻¹)ᴴ * uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have fix : ∀ v, u *ᵥ v = v → u⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  refine ⟨⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩, fix _ hw⟩
  calc (u⁻¹)ᴴ * Hpk k r * u⁻¹ = (u⁻¹)ᴴ * (uᴴ * Hpk k r * u) * u⁻¹ := by rw [hH]
    _ = ((u⁻¹)ᴴ * uᴴ) * Hpk k r * (u * u⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

theorem core (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (hCI : ConjInv D) (hclW : IsClosed (UWset k r D.z))
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
    (hT6 : ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (hcomm : ∀ u ∈ UUset k r D.z γ, u * g0 = g0 * u)
    (f : Mat k r → ℂ) (hEf : ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS ≠ ∞) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = JF D (scalF Wp f) g0 := by
  have hz : D.z' = D.z := hD.z_eq
  have hπ : D.π' = D.π := hD.π_eq
  have Bc : ∀ F : Mat k r → (Wp →L[ℂ] Wp), ∀ u ∈ UUset k r D.z γ,
      (JF D F g0).comp (D.π u) = (D.π u).comp (JF D F g0) := by
    intro F u hu
    have hu' : u ∈ UWset k r D.z' := hz ▸ hu.1
    have e := J_equiv D hCI hu.1 hu' F g0
    have eg : u⁻¹ * g0 * u = g0 := by
      rw [Matrix.mul_assoc, ← hcomm u hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hu.1.1),
        Matrix.one_mul]
    rw [eg, Lab_apply, hπ] at e
    conv_lhs => rw [e]
    ext v
    simp only [ContinuousLinearMap.comp_apply, pi_inv_apply D hu.1]
  have hB : JF D (scalF Wp f) g0 = ∫ p, Phi D f g0 p ∂D.μSS := J_phi D hD f g0
  have hB' : JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS :=
    J_th D hD γ hE hgW hgN hlam hg0 f
  have hC := aesm_C D hD γ hclW hgW
  have hPC : ∀ᵐ p ∂D.μSS, Psi D γ f g0 p = (Phi D f g0 p).comp (Cf D γ p) ∧
      Phi D f g0 p = (Psi D γ f g0 p).comp (Cb D γ p) ∧ ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
    filter_upwards [ae_in D] with p hp using psi_eq_C D hD γ hWbar hp f g0
  by_cases hm : AEStronglyMeasurable (Phi D f g0) D.μSS
  swap
  · have hm' : ¬ AEStronglyMeasurable (Psi D γ f g0) D.μSS := fun h =>
      hm ((aesm_comp h hC.2).congr (hPC.mono fun p hp => hp.2.1.symm))
    rw [hB, hB', integral_non_aestronglyMeasurable hm, integral_non_aestronglyMeasurable hm']
  have hPhiI : Integrable (Phi D f g0) D.μSS := by
    refine ⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩
    have e : ∀ p, ‖Phi D f g0 p‖ₑ = ‖rho D p (scalF Wp f) g0‖ₑ := fun p => by
      have h1 : ‖ph D p‖ₑ = 1 := by
        rw [enorm_eq_nnnorm, show ‖ph D p‖₊ = 1 from NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact norm_ph D p),
          ENNReal.coe_one]
      rw [show Phi D f g0 p = ph D p • rho D p (scalF Wp f) g0 by rw [rho_scalF, hπ]; rfl, enorm_smul, h1, one_mul]
    calc ∫⁻ p, ‖Phi D f g0 p‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS := lintegral_congr e
      _ < ∞ := hEf.lt_top
  have hPsiM : AEStronglyMeasurable (Psi D γ f g0) D.μSS :=
    (aesm_comp hm hC.1).congr (hPC.mono fun p hp => hp.1.symm)
  have hPsiI : Integrable (Psi D γ f g0) D.μSS := by
    refine hPhiI.norm.mono' hPsiM (hPC.mono fun p hp => ?_)
    rw [hp.1]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp.2.2.1)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0 := ⟨_, rfl⟩
  have hYc : ∀ u ∈ UUset k r D.z γ, Y.comp (D.π u) = (D.π u).comp Y := fun u hu => by
    rw [hY, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, Bc _ u hu, Bc _ u hu]
  have key : ∀ᵐ p ∂D.μSS, trY Y (Psi D γ f g0 p) = trY Y (Phi D f g0 p) := by
    filter_upwards [ae_in D] with p hp
    have hh := hp.1
    have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hz ▸ hp.2.2.1
    have hy : Matrix.of p.1.1 * (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z := uw_mul hh (uw_inv hh')
    obtain ⟨u₀, hu₀, hth⟩ := hT6 _ hy
    have hop : (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹) =
        ((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1 : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
          (((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)).comp
            (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp)) := by
      rw [← D.π_rep.2 _ (hWbar _ hh') _ (uw_inv (hWbar _ hh)), ← th_mul_inv γ hE (isUnit_of_uh hh'.1), hth,
        D.π_rep.2 _ (uw_mul hu₀.1 hy) _ (uw_inv hu₀.1), D.π_rep.2 _ hu₀.1 _ hy, D.π_rep.2 _ hh _ (uw_inv hh')]
      ext v
      rfl
    have h2 : Y.comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) =
        (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp Y := by
      rw [← pi_inv_eq D hu₀.1]
      exact hYc _ (uu_inv hu₀)
    simp only [Psi, Phi, hop, map_smul, trY_conj Y _ _ h2]
  have hI1 : trY Y (∫ p, Psi D γ f g0 p ∂D.μSS) = trY Y (∫ p, Phi D f g0 p ∂D.μSS) := by
    rw [← ContinuousLinearMap.integral_comp_comm _ hPsiI, ← ContinuousLinearMap.integral_comp_comm _ hPhiI]
    exact integral_congr_ae key
  have hYY : trY Y (JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0) = 0 := by
    rw [map_sub, hB, hB', hI1, sub_self]
  rw [← hY] at hYY
  have h0 := trY_self hYY
  rwa [hY, sub_eq_zero] at h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

theorem stSym (hIn : UnitaryGroupStructuralFacts) : StSym := by
  intro k r Wp _ _ _ D X hD hX γ hγ f q _ hq hT hEf
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIall, -, -, -, -, -, -, -, -, hClW, -⟩, -, -, hBCF, hUWb, -⟩ := id hIn
  have hCI : ConjInv D := hCIall k r Wp Wp D
  obtain ⟨-, -, hW1, -, -, -, -, hμN, hμW⟩ := stInvGroup hIn k r Wp D X hD hX γ hγ
  have hChar := stInvChar k r Wp D X hD hX γ hγ
  have hL6 := stTransM hIn k r Wp D X hD hX γ hγ
  have hE : IsUnit (embWb k r γ).det := emb_unit (unit_of_frame hγ.1)
  have hTpos : 0 < Tz k r D.z := D.T_pos
  have hc : ∀ a, q.1 a ≠ 0 := by
    intro a ha0
    have hw : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hq
    unfold bcWeight at hw
    split_ifs at hw with h1
    · have hM : 0 < 2 * (Mdim k r a - 2) := by
        unfold Mdim
        have := a.isLt
        have := D.k_pos
        omega
      have h0 : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Mdim k r b - 2))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha0, norm_zero, zero_pow hM.ne'])
      rw [h0, zero_mul] at hw
      exact lt_irrefl _ hw
    · exact lt_irrefl _ hw
  have hT0 : ((Tz k r D.z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hTpos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = -(q.2 / ((Tz k r D.z : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hd : 1 < ‖d‖ := by
    have h3 : Tz k r D.z < ‖q.2‖ := by
      rw [Complex.normSq_eq_norm_sq] at hT
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg q.2]
    have hnT : ‖((Tz k r D.z : ℝ) : ℂ)‖ = Tz k r D.z := by
      rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]
    rw [hd_def, norm_neg, norm_div, hnT, one_lt_div hTpos]
    exact h3
  have hqd : (q.1, -((Tz k r D.z : ℝ) : ℂ) * d) = q := by
    refine Prod.ext rfl ?_
    show -((Tz k r D.z : ℝ) : ℂ) * d = q.2
    rw [hd_def]
    field_simp
  obtain ⟨-, -, -, hg0th, h₀, hh₀, h₀', hh₀', hgq⟩ := stReps hIn k r Wp D X hD hX γ hγ q.1 d hc hd
  rw [hqd] at hgq
  have hh₀'' : h₀' ∈ UWset k r D.z' := hD.z_eq ▸ hh₀'
  have red : ∀ F : Mat k r → (Wp →L[ℂ] Wp),
      JF D F (gq D q) = (Lab D hh₀ hh₀'').symm (JF D F (g0 k r γ q.1 d)) := fun F => by
    rw [J_equiv D hCI hh₀ hh₀'' F (g0 k r γ q.1 d), ← hgq, ContinuousLinearEquiv.symm_apply_apply]
  have hEf0 : ∫⁻ p, ‖rho D p (scalF Wp f) (g0 k r γ q.1 d)‖ₑ ∂D.μSS ≠ ∞ := by
    rw [E_equiv D hCI hh₀ hh₀'', ← hgq]
    exact hEf
  rw [red, red, core D hD hCI (hClW k r D.z).closed γ hE hμW hμN (fun m hm => (hChar m hm).1) hW1 hL6 hg0th
    (fun u hu => big_cell_commute_frame_element hBCF hUWb D.k_pos hγ hu q.1 d) f hEf0]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

