import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0228
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartHolomorphic
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShFam.ExpCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)
open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

theorem base_eq [Mono (genι Z)] (q : FrPt Xo c (CAt σ)) {w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t ((cxPt Z q).1 ≫ genι Z) v) (hw : w ≫ Z.m.φ = v) :
    w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ GlobalTheory.AllWt.ptF (S := CAt σ) q := by
  have := Z.jQ_open
  refine (cancel_mono (Z.jQ ≫ genι Z)).1 ?_
  have h1 : w ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ genι Z = v ≫ Z.t.G.hom := by
    rw [← hw, Category.assoc, Z.m.cart.1.w]
  rw [Category.assoc, h1, hv.1]
  rfl

theorem mono_genι_of_ringOfIntegers {Xo : Moduli Dw l} {c : Coeff l} (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    Mono (genι Z) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  have : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  infer_instance

theorem exists_expCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → B ⊆ ch.e.target → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ b ∈ B, ∀ y : FrPt Xo c (CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x) → Mono (genι Z) → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ z : ReciprocityTheory.L2DbarEstimates.V d → ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ), (∀ τ k, DifferentiableOn ℂ (fun b => z b τ k) {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)}) ∧ ∀ b ∈ B, ∀ (hy : ch.e.symm b ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((ch.e.symm b).1 ≫ genι Z)), F.IsMap (evHom hy) f → ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k) → ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i (P b) w).left) (z b τ k) (q.u τ k) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch i B P hB hBt hPer hPd hPu hmono V φ F hstr
  set R := {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)} with hR
  rcases B.eq_empty_or_nonempty with hBe | ⟨b₀, hb₀⟩
  · refine ⟨0, fun τ k => ?_, fun b hb => by simp [hBe] at hb⟩
    have : R = ∅ := by
      ext b
      simp [hR, hBe]
    rw [this]
    exact differentiableOn_empty
  let L := EuclideanSpace.equiv (Fin d) ℂ
  set B₁ : Set (Fin d → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let P₂ : (Fin d → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun x => if L.symm x ∈ B then P (L.symm x) else P b₀
  have hP₂ : ∀ x, IsPeriod (Fu.Di i) ty (P₂ x) := fun x => by
    by_cases h : L.symm x ∈ B
    · simp only [P₂, if_pos h]; exact hPer _ h
    · simp only [P₂, if_neg h]; exact hPer _ hb₀
  have hP₂d : ∀ a, DifferentiableOn ℂ (fun x => P₂ x a) B₁ := fun a =>
    ((hPd a).comp L.symm.differentiableOn fun x hx => hx).congr fun x hx => by
      simp only [P₂, if_pos (show L.symm x ∈ B from hx), Function.comp_apply]
  have hP₂L : ∀ b ∈ B, P₂ (L b) = P b := fun b hb => by
    simp only [P₂, ContinuousLinearEquiv.symm_apply_apply, if_pos hb]
  have hover : ∀ x, Fu.u i (P₂ x) ≫ Xo.s = spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun x => by
    rw [Fu.over_σ i _ (hP₂ x), ← Spec.map_comp]
    rfl
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun x => pullback.lift _ _ (hover x)
  have hu : ∀ x, Fu.u i (P₂ x) = p x ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun x => (pullback.lift_fst _ _ _).symm
  have hs : ∀ x, p x ≫ pullback.snd _ _ = spMap σ := fun x => pullback.lift_snd _ _ _
  have hpq : ∀ b ∈ B, ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → p (L b) = GlobalTheory.AllWt.ptF (S := CAt σ) q :=
    fun b hb q hq => by
      refine pullback.hom_ext ?_ ?_
      · rw [← hu, hP₂L b hb, hPu b hb q hq.symm]
        exact (GlobalTheory.TrueCx.ptC_fst q).symm
      · rw [hs]
        exact (GlobalTheory.TrueCx.ptC_snd q).symm
  have hσφ : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom h).comp φ := fun {y} h => by
    have e : spMap σ = spMap ((evHom h).comp φ) := by
      rw [← y.2, ← spMap_evHom h, Category.assoc, hstr, ← Spec.map_comp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hRV : ∀ b ∈ R, ⊤ ≤ (p (L b) ≫ Z.jQ) ⁻¹ᵁ V.1 := fun b hb => by
    have hx : (ch.e.symm b).1 ≫ genι Z = spMap (evHom hb.2.1) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, spMap_evHom hb.2.1]
    obtain ⟨f, -⟩ := F.exists_isMap (evHom hb.2.1) (hσφ hb.2.1) hx
    obtain ⟨q, hq, -⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ Z σ _ hb.2.2 f
    rw [hpq b hb.1 q hq]
    show ⊤ ≤ (cxPt Z q).1 ⁻¹ᵁ V.1
    rw [hq]
    exact hb.2.1
  choose W hW hWd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.T.expCoordinates_tangentField_holomorphic_periodMap _ _ _ _ _ _ _ _ Z σ g ty Fu i d B₁ P₂ p hu V (F.v a.1 a.2) hB₁o hP₂ hP₂d hs (F.tan a.1 a.2)
  refine ⟨fun b τ k => W ⟨τ, k⟩ (L b), fun τ k => ?_, fun b hb hy f hf q hq hw τ k => ?_⟩
  · exact (hW ⟨τ, k⟩).comp L.differentiableOn fun b hb =>
      ⟨by simpa [hB₁] using hb.1, hRV b hb⟩
  · obtain ⟨w, hw1, hw2⟩ := hw τ k
    have hd := hWd ⟨τ, k⟩ (L b) (by simpa [hB₁] using hb) (ch.e.symm b) hy (by rw [hpq b hb q hq, ← hq]; rfl)
    have hfv : spMap (dualMap (evHom hy)) ≫ F.v τ k = w ≫ Z.m.φ := by rw [hw2, hf τ k]
    rw [hfv] at hd
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      rw [hpq b hb q hq]
      exact base_eq Z q (by rw [hq]; exact f.tan τ k) hw2
    have h := isDerivAt0_ex_of_push Z Fu (p (L b)) i (P₂ (L b)) (hP₂ _) (hu _) hbase hd
    rw [hw1, hP₂L b hb] at h
    exact h

end GlobalTheory.ShFam.ExpCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem period_growth_mono_bound (x C : ℝ) (k K : ℕ) (hx : 0 ≤ x) (hk : k ≤ K) :
    C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ K := by
  have h1 : (1:ℝ) ≤ 1 + x := by linarith
  calc C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) (le_max_right _ _)

theorem period_matrix_polynomial_growth : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a d τ c hτ hpos hc

  have key : ∀ v : Fin d → ℝ, v ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
      ‖∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro v hv
    apply GlobalTheory.upper_half_growth n a
    · have hij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) (logDom n a) :=
        fun i j => differentiableOn_pi.1 (differentiableOn_pi.1 hτ i) j
      fun_prop
    · intro s hs; exact hpos s hs v hv
  have e1 : ∀ (M : Fin d → Fin d → ℂ) (i : Fin d),
      ∑ i', ∑ j', (((Pi.single i (1:ℝ) : Fin d → ℝ) i' : ℝ) : ℂ) * M i' j' * (((Pi.single i (1:ℝ) : Fin d → ℝ) j' : ℝ) : ℂ) = M i i := by
    intro M i
    simp [Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
  have e2 : ∀ (M : Fin d → Fin d → ℂ) (i j : Fin d),
      ∑ i', ∑ j', ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) i' : ℝ) : ℂ) * M i' j' * ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) j' : ℝ) : ℂ) = M i i + M j j + M i j + M j i := by
    intro M i j
    simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
    ring
  have ne1 : ∀ i : Fin d, (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
    intro i h
    have := congrFun h i
    simp at this
  have ne2 : ∀ i j : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ) ≠ 0 := by
    intro i j h
    have := congrFun h i
    simp [Pi.single_apply] at this
    split_ifs at this <;> linarith

  have entry : ∀ i j : Fin d, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s i j‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro i j
    obtain ⟨C1, k1, h1⟩ := key _ (ne2 i j)
    obtain ⟨C2, k2, h2⟩ := key _ (ne1 i)
    obtain ⟨C3, k3, h3⟩ := key _ (ne1 j)
    refine ⟨(max C1 0 + max C2 0 + max C3 0 + ‖c i j‖) / 2, max k1 (max k2 k3), by positivity, ?_⟩
    intro s hs hl him
    set K := max k1 (max k2 k3)
    have hx : 0 ≤ ‖s‖ := norm_nonneg _
    have b1 := (h1 s hs hl him).trans (period_growth_mono_bound ‖s‖ C1 k1 K hx (by omega))
    have b2 := (h2 s hs hl him).trans (period_growth_mono_bound ‖s‖ C2 k2 K hx (by omega))
    have b3 := (h3 s hs hl him).trans (period_growth_mono_bound ‖s‖ C3 k3 K hx (by omega))
    rw [e2] at b1
    rw [e1] at b2 b3
    have hP : 1 ≤ (1 + ‖s‖) ^ K := one_le_pow₀ (by linarith)
    have hcc : ‖c i j‖ ≤ ‖c i j‖ * (1 + ‖s‖) ^ K := le_mul_of_one_le_right (norm_nonneg _) hP
    have hid : (2:ℂ) * τ s i j = (τ s i i + τ s j j + τ s i j + τ s j i) - τ s i i - τ s j j + c i j := by
      rw [← hc s hs i j]; ring
    have h2n : ‖(2:ℂ) * τ s i j‖ ≤ ‖τ s i i + τ s j j + τ s i j + τ s j i‖ + ‖τ s i i‖ + ‖τ s j j‖ + ‖c i j‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    rw [norm_mul] at h2n
    norm_num at h2n
    nlinarith
  choose Ce ke hCe hke using entry
  refine ⟨∑ i, ∑ j, Ce i j, Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2), ?_⟩
  intro s hs hl him
  set K := Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2)
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ (1 + ‖s‖) ^ K := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, Ce i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCe i j
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hk : ke i j ≤ K := Finset.le_sup (f := fun p : Fin d × Fin d => ke p.1 p.2) (Finset.mem_univ (i, j))
  have b := (hke i j s hs hl him).trans (period_growth_mono_bound ‖s‖ (Ce i j) (ke i j) K hx hk)
  rw [max_eq_left (hCe i j)] at b
  have hle : Ce i j ≤ ∑ i, ∑ j, Ce i j :=
    (Finset.single_le_sum (f := fun j => Ce i j) (fun j _ => hCe i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Ce i j) (fun i _ => Finset.sum_nonneg fun j _ => hCe i j) (Finset.mem_univ i))
  exact b.trans (mul_le_mul_of_nonneg_right hle hP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnifSqCompare

theorem mem_sq {X : Scheme.{0}} {L : LB X} {x : X} {j : L.ι} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ↔ x ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun _ => h⟩

end UnifSqCompare

set_option maxHeartbeats 1000000 in
open UnifCompare UnifSqCompare in

theorem unif_sq_polarised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' hL
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hGF : GlobalFnsSt := allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := allSixLaws.1.secBaseChange
  have hA : AmpleSt := allSixLaws.1.ample
  obtain ⟨wL₀, hwL₀⟩ := hL
  obtain ⟨wL, hwL, hrig⟩ := GlobalTheory.T.exists_rescale_rigidified_square_iso _ G U.LG U'.LG wL₀ hwL₀
  choose β hβm hβ using unifPre_abelianPart_iso R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre
  choose v hvg hv using fun e =>
    GlobalTheory.T.polarization_squares_agree_at_each_thickening hGF R (maximalIdeal R) hR D D' A A' G hG U.toUnifPre U'.toUnifPre wL hwL hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R (maximalIdeal R) e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q U'.toUnifPre, Category.assoc, hβl,
      trans_comp_q U.toUnifPre, ← Category.assoc, hβl]
  have hR' := hR
  obtain ⟨hN, -, -, hC⟩ := hR'
  obtain ⟨Φ, w, hw, H⟩ := GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square hS hA R (maximalIdeal R) D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R (maximalIdeal R) e D'.toPre.P.A).left,
        y ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') →
        thickMap R (maximalIdeal R) e D'.toPre.P.A y ∈
          ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β (e + 1)).hom.left ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) (e + 1) D'.toPre.P.A).left).U (fun _ => fun _ => j') := by
      intro y hy
      have k : thickMap R (maximalIdeal R) e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫
          (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG (maximalIdeal R) (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j)) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
          (fun _ => 2)).U (fun _ => j')) (trans_comp_proj e _)).mpr (mem_pull.1 hy.2))⟩
    have hz : r z ∈ ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
            ((β e).hom.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left)).U (fun _ => fun _ => j) ⊓
          ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
            (fstG (maximalIdeal R) e D'.toPre.P.A).left).U (fun _ => fun _ => j') :=
      ⟨mem_pull.2 (mem_sq.2 hj), mem_pull.2 (mem_sq.2 hj')⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_sq.1 (mem_pull.1 hx.1))
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_sq.1 (mem_pull.1 hx.2)
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R (maximalIdeal R) e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U'.toUnifPre e x j' jL' hM' hL', gw_trans U.toUnifPre e x j jL hM hL, trans_comp_q U'.toUnifPre,
      trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have hpG : ∀ e, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot (maximalIdeal R)
  have hΦ : IsMonHom Φ.hom := by
    refine AbelianPartIso.isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine AbelianPartIso.isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R (maximalIdeal R) e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (hpG e)))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨Φ, w, wL, hw, hwL, hΦ, fun e => ⟨hpG e, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
    ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
  rw [Category.assoc] at h
  exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.matrix_mul_bounded_poly_growth | exact GlobalTheory.matrix_mul_bounded_poly_growth | (intros; apply GlobalTheory.matrix_mul_bounded_poly_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.growth_bound_of_spanning_combinations | exact GlobalTheory.growth_bound_of_spanning_combinations | (intros; apply GlobalTheory.growth_bound_of_spanning_combinations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartSection
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.LChart

theorem diag_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V] {n : ℕ} (c : Fin n → V)
    (hc : LinearIndependent k c) (j : Fin n) (cf : Fin n → k) (d : k) (hcf : ∀ m, j < m → cf m = 0)
    (h : (∑ m, cf m • c m) - d • c j ∈ Submodule.span k (c '' {m | m < j})) : d = cf j := by
  have h1 : (∑ m, cf m • c m) - cf j • c j ∈ Submodule.span k (c '' {m | m < j}) := by
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ j)]
    refine Submodule.sum_mem _ fun m hm => ?_
    rcases lt_trichotomy m j with hlt | heq | hgt
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hlt, rfl⟩)
    · exact absurd heq (Finset.ne_of_mem_erase hm)
    · rw [hcf m hgt, zero_smul]
      exact Submodule.zero_mem _
  have h2 := Submodule.sub_mem _ h1 h
  rw [sub_sub_sub_cancel_left, ← sub_smul] at h2
  by_contra hne
  have h3 := (Submodule.smul_mem_iff _ (sub_ne_zero.2 hne)).1 h2
  exact hc.notMem_span_image (s := {m | m < j}) (x := j) (lt_irrefl j) h3

theorem exists_ringHom {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ f ⁻¹ᵁ U) : ∃ ψ : Γ(X, U) →+* k, spMap ψ ≫ hU.fromSpec = f := by
  have hr : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact h (Set.mem_univ x)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift hU.fromSpec f hr)).hom =
      IsOpenImmersion.lift hU.fromSpec f hr := Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem ne_zero_of_chart {R k : Type} [CommRing R] [Field k] {N : ℕ} (c : R →+* k) (v : Fin (N + 1) → k)
    (hv : Ideal.span (Set.range v) = ⊤) (i : Fin (N + 1)) (h : ⊤ ≤ pt c v hv ⁻¹ᵁ chart R N i) : v i ≠ 0 := by
  intro h0
  rw [pt_preimage_chart, h0] at h
  have h1 := h (Set.mem_univ (IsLocalRing.closedPoint k))
  exact h1 (Ideal.zero_mem _)

theorem gen_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k) (cf : Fin (Dw.mult (u kk).1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L'.U i → (∀ m, (u kk).2 < m → cf m = 0) → IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ (u kk).1) cf ((Z.fr a').bc φ' (u kk).1 (u kk).2) → valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf (u kk).2 := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T n u kk h₀ h₁ L' ix q₀ q₁ r hL k _ a a' i φ φ' cf hφ hi hcf hcomb
  have hle := (spMap φ ≫ Z.chart a).preimage_mono (hL.le i)
  have hle1 := hi.trans hle
  have hU : ⊤ ≤ (spMap φ ≫ Z.chart a ≫ Z.π) ⁻¹ᵁ L.U (ix i) := fun x hx => (hle1 hx).1
  have hφπ : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π := by
    rw [← Category.assoc, hφ, Category.assoc]
  obtain ⟨ψ, hψ⟩ := exists_ringHom _ (aff (ix i)) hU
  have fa := T.frame a k φ
  have fa' := T.frame a' k φ'
  rw [← hφπ] at fa'
  have sf := GlobalTheory.T.pre_model_chart_compatible E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a a' φ φ' hφ
  rw [T.ty] at sf
  obtain ⟨t1, t2, -⟩ := GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd T.emb (ix i) k ψ _ _ _ _ _ hψ fa fa'
  obtain ⟨d, hd⟩ := t1.1 sf
  have hc := (T.emb.comb_iff (ix i) ψ hψ (fun j => (fa.1 (u kk).1 j).1) (fa'.1 (u kk).1 (u kk).2).1 cf).1 hcomb
  have hdc : d (u kk) = cf (u kk).2 := by
    refine diag_eq _ (t2 (u kk).1) (u kk).2 cf _ hcf ?_
    have := hd (u kk)
    simp only [hc] at this
    exact this
  have P0 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₀) (q₀ i)
  have P1 := congrFun (plk_tri _ _ _ _ _ _ d _ _ hd h₁) (q₁ i)
  have v := hL.val k a i φ ψ hψ hi
  have v' := hL.val k a' i φ' ψ (hψ.trans hφπ) (hφ ▸ hi)
  obtain ⟨hu, hp⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ix i) φ' ψ (hψ.trans hφπ)
    ⟨kk + 1, _, h₁⟩
  have hne := ne_zero_of_chart _ _ hu (q₁ i) (by
    rw [← hp, ← Category.assoc, ← hφ]
    exact fun x hx => (hle1 hx).2.2)
  rw [← hφ] at v'
  have hprod : ∏ l : Fin (kk + 1), d ((u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2)) l) =
      (∏ l : Fin kk, d ((u ∘ Fin.castLE kk.2.le) l)) * d (u kk) := by
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hprod, hdc] at P1
  simp only [Pi.smul_apply, smul_eq_mul] at P0 P1
  dsimp only at v v' hne
  rw [P1] at hne
  rw [P0, P1, ← v] at v'
  have hD := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP := right_ne_zero_of_mul hne
  apply mul_right_cancel₀ (mul_ne_zero hD hP)
  linear_combination -v'

end GlobalTheory.FlagEmb.LChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartTransitionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_transition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (w w' : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k), w ≫ Z.π = w' ≫ Z.π → Z.FlagAt w u → Z.FlagAt w' u → w = w' := by
  first | exact @GlobalTheory.FlagEmb.flagAt_unique | exact GlobalTheory.FlagEmb.flagAt_unique | (intros; apply GlobalTheory.FlagEmb.flagAt_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalyticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatFam_comp_of_analyticOnNhd : ∀ (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ), GlobalTheory.ShFam.Hor.LogCh.IsLatFam B K → IsOpen B' → AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → GlobalTheory.ShFam.Hor.LogCh.IsLatFam B' (fun b => K (φ b)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic | exact GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.IsLatFam.pullback_analytic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalyticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  first | exact @GlobalTheory.logDom_chart_props | exact GlobalTheory.logDom_chart_props | (intros; apply GlobalTheory.logDom_chart_props <;> assumption)
end

