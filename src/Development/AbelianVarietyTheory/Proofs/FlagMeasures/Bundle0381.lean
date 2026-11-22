import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeTwoFlagsGeneralPosition
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolumeGen

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  GlobalTheory.Amp.YInv.N_sub_S z hn

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := by
  have h : Continuous (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := continuous_two a b
  exact h.measurable

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have hla : Measurable (lmulM a : Mt k r → Mt k r) := by
    have h : (lmulM a : Mt k r → Mt k r) = fun x => (Matrix.of.symm (a * Matrix.of x * 1) : Mt k r) := by
      funext x; apply Matrix.of.injective; (rw [Equiv.apply_symm_apply, Matrix.mul_one]) <;> rfl
    rw [h]; exact measurable_two a 1
  have hrb : Measurable (rmulM b : Mt k r → Mt k r) := (GlobalTheory.SgInf.continuous_rmulM b).measurable
  have h1 : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [h1, ← Measure.map_map hrb hla, hl, hr]

theorem fibre_volume : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' γ → DeOK k r z z' γ De → 0 < s → NormR k r γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yv k r z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y / s) := by
  intro k r z z' γ De s μR hr hk hTF hDe hs hNR g₁ hg₁
  obtain ⟨n₁, hn₁, n₂, hn₂, g₀, β, hNorm, rfl, rfl⟩ := hNR
  obtain ⟨hz, hz', hT, hT', -, hGf, hDr⟩ := hTF
  have hg₀G : g₀ ∈ GG k r := hNorm.1
  have hn₁S : n₁ ∈ Sset k r z := GlobalTheory.Amp.YInv.N_sub_S z hn₁
  have hn₂S : n₂ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂
  have hn₂G : n₂ ∈ GG k r := hn₂.1
  have hu2 : IsUnit n₂.det := GG_unit hn₂G
  have hn₂i : n₂⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₂ hn₂
  have hn₂iS : n₂⁻¹ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂i
  have c1 : ∀ B : Mat k r, n₂ * (n₂⁻¹ * B) = B := fun B => Matrix.mul_nonsing_inv_cancel_left n₂ B hu2
  have c2 : ∀ B : Mat k r, n₂⁻¹ * (n₂ * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n₂ B hu2

  have hDmin : ∀ l, Dmin k r z z' (n₁ * g₀ * n₂) l = Dmin k r z z' g₀ l :=
    fun l => dInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀ l
  have hGf0 : Gf k r z z' (n₁ * g₀ * n₂) = Gf k r z z' g₀ := gInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀
  have hDr0 : Dr k r z z' (n₁ * g₀ * n₂) = Dr k r z z' g₀ := by unfold Dr; rw [hDmin]
  have hTF0 : TwoFl k r z z' g₀ := ⟨hz, hz', hT, hT', hg₀G, by rw [← hGf0]; exact hGf, by rw [← hDr0]; exact hDr⟩
  have hDe0 : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl hne => ?_⟩
    rw [← hDmin] at hne ⊢
    exact hDe.2 l hl hne

  obtain ⟨n', hn', a, ha, m, hm, κ, hκ, hdec⟩ := GlobalTheory.Amp.Iwa.iwasawa k r (n₂ * g₁) (GG_mul hn₂G hg₁)
  have hB := GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound k r z z' g₀ β De hr hk hTF0 hNorm hDe0 m hm a ha
  set A := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hn'G : n' ∈ GG k r := hn'.1
  have hdec' : n₂ * g₁ = n' * A * κ := by rw [hdec, hA]; simp only [mul_assoc]
  have c3 : ∀ B : Mat k r, n'⁻¹ * (n' * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n' B (GG_unit hn'G)
  have hAK : A * κ ∈ GG k r := by
    have : A * κ = n'⁻¹ * (n₂ * g₁) := by rw [hdec']; simp only [mul_assoc, c3]
    rw [this]; exact GG_mul (GG_inv hn'G) (GG_mul hn₂G hg₁)
  have hg : n₂⁻¹ * (n' * (A * κ)) = g₁ := by rw [← mul_assoc n' A, ← hdec', c2]

  have hl2 : (lebN k r).map (lmulM n₂) = lebN k r := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r).2.2.2 n₂ hn₂
  have hr2 : (lebN k r).map (rmulM (n₂⁻¹ * n')) = lebN k r :=
    ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r)).1.1 _ ((nSubgroup k r).2.1 _ hn₂i _ hn')
  have hu' : IsUnit (n₂⁻¹ * n').det := GG_unit (GG_mul (GG_inv hn₂G) hn'G)
  obtain ⟨e, he_map, he⟩ : ∃ e : Mt k r ≃ᵐ Mt k r, (lebN k r).map e = lebN k r ∧
      ∀ n, Matrix.of (e n) = n₂ * Matrix.of n * (n₂⁻¹ * n') :=
    ⟨twoEquiv n₂ (n₂⁻¹ * n') hu2 hu', map_twoEquiv hu2 hu' hl2 hr2, fun _ => rfl⟩
  have key : ∀ n : Mt k r, Matrix.of n * g₁ = n₂⁻¹ * (Matrix.of (e n) * A) * κ := by
    intro n; rw [he n]; simp only [mul_assoc, c2, hg]

  have hYv : ∀ W : Mat k r, Yv k r z z' (n₁ * g₀ * n₂) (n₂⁻¹ * W * κ) = Yv k r z z' g₀ W := by
    intro W
    rw [GlobalTheory.Amp.YInv.Yv_N hz hz' g₀ hn₁ hn₂]
    have : n₂ * (n₂⁻¹ * W * κ) = W * κ := by simp only [mul_assoc, c1]
    rw [this, GlobalTheory.Amp.YInv.Yv_K z z' g₀ W hκ.1 hκ.2]
  have hGGW : ∀ W : Mat k r, n₂⁻¹ * W * κ ∈ GG k r ↔ W ∈ GG k r := by
    intro W
    constructor
    · intro h
      have : W = n₂ * (n₂⁻¹ * W * κ) * κ⁻¹ := by
        simp only [mul_assoc, c1, Matrix.mul_nonsing_inv _ (GG_unit hκ.1), Matrix.mul_one]
      rw [this]; exact GG_mul (GG_mul hn₂G h) (GG_inv hκ.1)
    · intro h; exact GG_mul (GG_mul (GG_inv hn₂G) h) hκ.1
  have hSg' : ∀ W ∈ GG k r, Sg k r z' (n₂⁻¹ * W * κ) = Sg k r z' W :=
    fun W hW => ((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 W hW n₂⁻¹ hn₂iS κ hκ).2
  have hSg : ∀ W ∈ GG k r, Sg k r z (n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ)) = Sg k r z (g₀ * W) := by
    intro W hW
    have : n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ) = n₁ * (g₀ * W) * κ := by simp only [mul_assoc, c1]
    rw [this]; exact ((GlobalTheory.Amp.LInv.lengths_basic k r z hz).1 (g₀ * W) (GG_mul hg₀G hW) n₁ hn₁S κ hκ).2
  refine ⟨?_, ?_⟩
  · have hset : {n : Mt k r | Yv k r z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0} =
        e ⁻¹' {ν | Yv k r z z' g₀ (Matrix.of ν * A) = 0} := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_preimage, key n, hYv]
    rw [hset, ← MeasurableEquiv.map_apply, he_map]
    exact hB.1
  · intro φ hφ R₀ y hR₀ hy
    have hl : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (lmulM b x) = b * Matrix.of x := fun _ _ => rfl
    have hc : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (conjM b x) = b * Matrix.of x * b⁻¹ := fun _ _ => rfl
    have hmeas : ∀ (f : Mt k r → Mt k r) (b c : Mat k r), (∀ x, Matrix.of (f x) = b * Matrix.of x * c) →
        Measurable f := by
      intro f b c h
      have : f = fun x => (Matrix.of.symm (b * Matrix.of x * c) : Mt k r) :=
        funext fun x => Matrix.of.injective (by rw [h] <;> rfl)
      rw [this]; exact measurable_two b c
    obtain ⟨P, hPm, hP⟩ : ∃ P : Mt k r → Mt k r, Measurable P ∧
        ∀ ν, Matrix.of (P ν) = n₂⁻¹ * Matrix.of ν * (A * κ) :=
      ⟨fun ν => Matrix.of.symm (n₂⁻¹ * Matrix.of ν * (A * κ)), measurable_two _ _, fun _ => rfl⟩

    have hsub : SubCut (Nset k r) (lebR k r β) (fun ν => ENNReal.ofReal s * φ (P ν)) := by
      refine ⟨(hφ.1.comp hPm).const_mul _, fun x hx => ?_⟩
      have hx0 : Matrix.of (P x) ∈ GG k r := by
        rw [hP, mul_assoc]; exact GG_mul (GG_inv hn₂G) (GG_mul hx.1 hAK)
      have h1 := hφ.2 (P x) hx0
      have hm1 : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (P x)) :=
        hφ.1.comp (hmeas _ 1 (Matrix.of (P x)) fun ρ => by simp only [hl, Matrix.one_mul])
      have hm2 : Measurable (conjM n₂⁻¹ : Mt k r → Mt k r) := hmeas _ n₂⁻¹ n₂⁻¹⁻¹ fun x => hc _ _
      rw [lintegral_map hm1 hm2, lintegral_smul_measure] at h1
      have hPl : ∀ ρ : Mt k r, P (lmulM (Matrix.of ρ) x) = lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x) := by
        intro ρ
        apply Matrix.of.injective
        simp only [hl, hc, hP, Matrix.nonsing_inv_nonsing_inv _ hu2, mul_assoc, c1]
      calc ∫⁻ ρ, ENNReal.ofReal s * φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β
          = ENNReal.ofReal s * ∫⁻ ρ, φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal s * ∫⁻ ρ, φ (lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x)) ∂lebR k r β := by
            congr 1; exact lintegral_congr fun ρ => by rw [hPl ρ]
        _ ≤ 1 := by first | exact h1 | (rw [smul_eq_mul] at h1; exact h1)
    have hmain := hB.2 (fun ν => ENNReal.ofReal s * φ (P ν)) hsub R₀ y hR₀ hy
    have hmem : ∀ n : Mt k r, rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y ↔
        rmulM A (e n) ∈ Eset k r z z' g₀ R₀ y := by
      intro n
      simp only [Eset, Set.mem_setOf_eq, GlobalTheory.SgInf.of_rmulM]
      rw [key n]
      generalize Matrix.of (e n) * A = W
      rw [hGGW W, hYv W]
      constructor
      · rintro ⟨hW, h1, h2, h3, h4⟩
        rw [hSg' W hW] at h1; rw [hSg W hW] at h2; exact ⟨hW, h1, h2, h3, h4⟩
      · rintro ⟨hW, h1, h2, h3, h4⟩
        exact ⟨hW, by rw [hSg' W hW]; exact h1, by rw [hSg W hW]; exact h2, h3, h4⟩
    have hpt : ∀ n : Mt k r, rmulM g₁ n = P (e n) := by
      intro n
      apply Matrix.of.injective
      rw [GlobalTheory.SgInf.of_rmulM, hP, key n]
      simp only [mul_assoc]
    have hint : ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂lebN k r
        = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂lebN k r := by
      calc _ = ∫⁻ n, (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) (e n) ∂lebN k r := by
            refine lintegral_congr fun n => ?_
            have hind : (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator (1 : Mt k r → ℝ≥0∞) (rmulM g₁ n) =
                (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A (e n)) := by
              by_cases h : rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y
              · simp only [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem n).1 h), Pi.one_apply]
              · have h' : rmulM A (e n) ∉ Eset k r z z' g₀ R₀ y := fun h' => h ((hmem n).2 h')
                first
                  | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
                  | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h']
                  | simp [Set.indicator, h, h']
            dsimp only
            rw [hind, hpt n]
        _ = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂((lebN k r).map e) :=
            (lintegral_map_equiv (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) e).symm
        _ = _ := by rw [he_map]
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
    rw [hint, ENNReal.ofReal_div_of_pos hs,
      ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm _ (ENNReal.ofReal s), ← lintegral_const_mul' (ENNReal.ofReal s) _ ENNReal.ofReal_ne_top]
    refine le_trans (le_of_eq ?_) hmain
    refine lintegral_congr fun ν => ?_
    simp only [mul_assoc]

end GlobalTheory.Amp.FibreVolumeGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory

open Classical in

theorem equivFinsuppOfBasisLeft_lTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : M ⊗[K] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem AL_eq_zero_of_compAt (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L)
    (h : ∀ v, ReciprocityTheory.Aut.compAt L v a = 0) : a = 0 := by
  classical
  set K := maximalRealSubfield L
  let b := Module.finBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b
  have hc : ∀ i, e a i = 0 := by
    intro i
    refine RestrictedProduct.ext _ _ (fun v => ?_)
    have h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x =
        LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x := by
      intro x
      simp only [ReciprocityTheory.Aut.compAt]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
    have h2 := equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i
    rw [← h1 a, h v, map_zero, Finsupp.zero_apply] at h2
    exact h2.symm
  have : e a = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.IsotConjFix

open Formalism.IndefR.principalLevelFrame

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f g = f (g * h) := rfl

theorem range_equivariantMap_stable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (h : Formalism.AUTREP.GAf L n) (y : A) (hy : y ∈ LinearMap.range Φ) :
    ρ h y ∈ LinearMap.range Φ := by
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hy
  exact ⟨_, hΦ h f⟩

theorem zero_or_inj {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) : Φ = 0 ∨ Function.Injective Φ := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (LinearMap.ker Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [hΦ h f, hf, map_zero]
  rcases σ.irr K hle hst with hK | hK
  · right
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hf, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    exact (Submodule.mem_bot _).2 (Subtype.ext hm)
  · left
    apply LinearMap.ext
    intro f
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    simpa using hg

theorem inf_bot_or_le {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n} {Φ : σ.S →ₗ[ℂ] A}
    (hΦ : IsEqvA ρ σ Φ) (W : Submodule ℂ A) (hW : ∀ h, ∀ y ∈ W, ρ h y ∈ W) :
    LinearMap.range Φ ⊓ W = ⊥ ∨ LinearMap.range Φ ≤ W := by
  let K : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := (W.comap Φ).map σ.S.subtype
  have hle : K ≤ σ.S := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hst : ∀ h, ∀ f ∈ K, Formalism.L2.NG.rt L n h f ∈ K := by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨⟨_, σ.stable h f f.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hf ⊢
    rw [hΦ h f]
    exact hW h _ hf
  rcases σ.irr K hle hst with hK | hK
  · left
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_range] at hy
    obtain ⟨⟨f, rfl⟩, hy⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := ⟨f, hy, rfl⟩
    rw [hK, Submodule.mem_bot] at hm
    have e : f = 0 := Subtype.ext hm
    rw [e, map_zero]
    exact Submodule.zero_mem _
  · right
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    have hm : (f : Formalism.AUTREP.GAf L n → ℂ) ∈ K := by rw [hK]; exact f.2
    obtain ⟨g, hg, hgf⟩ := hm
    have e : g = f := Subtype.ext hgf
    subst e
    exact hg

def Indep {J : Type} (R : J → Submodule ℂ A) (t : Finset J) : Prop :=
  ∀ v : J → A, (∀ j ∈ t, v j ∈ R j) → ∑ j ∈ t, v j = 0 → ∀ j ∈ t, v j = 0

theorem select {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {J : Type} [DecidableEq J] (R : J → Submodule ℂ A)
    (hst : ∀ j h, ∀ y ∈ R j, ρ h y ∈ R j)
    (hirr : ∀ j (W : Submodule ℂ A), (∀ h, ∀ y ∈ W, ρ h y ∈ W) → R j ⊓ W = ⊥ ∨ R j ≤ W) (s : Finset J) :
    ∃ t ⊆ s, Indep R t ∧ ⨆ j ∈ t, R j = ⨆ j ∈ s, R j := by
  have stab : ∀ t : Finset J, ∀ h, ∀ y ∈ ⨆ j ∈ t, R j, ρ h y ∈ ⨆ j ∈ t, R j := by
    intro t h y hy
    have hle : (⨆ j ∈ t, R j) ≤ (⨆ j ∈ t, R j).comap (ρ h) := by
      refine iSup₂_le fun j hj => ?_
      intro z hz
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj) (hst j h z hz)
    exact hle hy
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨∅, subset_rfl, fun v _ _ j hj => by simp at hj, rfl⟩
  | insert k s hk ih =>
    obtain ⟨t, hts, hind, heq⟩ := ih
    rcases hirr k (⨆ j ∈ t, R j) (stab t) with hd | hle
    · have hkt : k ∉ t := fun h => hk (hts h)
      refine ⟨insert k t, Finset.insert_subset_insert k hts, ?_, ?_⟩
      · intro v hv hsum j hj
        rw [Finset.sum_insert hkt] at hsum
        have hvk : v k = 0 := by
          have h1 : v k ∈ R k ⊓ ⨆ j ∈ t, R j := by
            refine Submodule.mem_inf.2 ⟨hv k (Finset.mem_insert_self k t), ?_⟩
            have e : v k = -∑ j ∈ t, v j := eq_neg_of_add_eq_zero_left hsum
            rw [e]
            refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
            exact le_iSup₂ (f := fun j (_ : j ∈ t) => R j) j hj (hv j (Finset.mem_insert_of_mem hj))
          rw [hd] at h1
          exact (Submodule.mem_bot _).1 h1
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hvk
        · rw [hvk, zero_add] at hsum
          exact hind v (fun i hi => hv i (Finset.mem_insert_of_mem hi)) hsum j hj
      · rw [Finset.iSup_insert, Finset.iSup_insert, heq]
    · refine ⟨t, hts.trans (Finset.subset_insert k s), hind, ?_⟩
      rw [Finset.iSup_insert, ← heq, sup_eq_right.2 hle]

theorem fix_sum_of_mem {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {σ : Formalism.L2.NG.FinTyp L n}
    (P : (σ.S →ₗ[ℂ] A) → Prop) (U : Set (Formalism.AUTREP.GAf L n)) {ι : Type} [Fintype ι] (b : ι → ℂ)
    (lf : ι → Formalism.AUTREP.GAf L n)
    (H : ∀ ψ ∈ σ.S, (∀ κ ∈ U, Formalism.L2.NG.rt L n κ ψ = ψ) → ∑ i, b i • Formalism.L2.NG.rt L n (lf i) ψ = ψ)
    (x : A) (hx : x ∈ ⨆ (Φ : σ.S →ₗ[ℂ] A) (_ : IsEqvA ρ σ Φ ∧ P Φ), LinearMap.range Φ)
    (hU : ∀ κ ∈ U, ρ κ x = x) : ∑ i, b i • ρ (lf i) x = x := by
  classical
  let J := {Φ : σ.S →ₗ[ℂ] A // IsEqvA ρ σ Φ ∧ P Φ}
  let R : J → Submodule ℂ A := fun j => LinearMap.range j.1
  rw [iSup_subtype'] at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨t, -, hind, heq⟩ := select (ρ := ρ) R (fun j h y hy => range_equivariantMap_stable j.2.1 h y hy)
    (fun j W hW => inf_bot_or_le j.2.1 W hW) s
  rw [← heq] at hs
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hs
  have hψ : ∀ j : J, ∃ ψ : σ.S, j.1 ψ = μ j := fun j => LinearMap.mem_range.1 (μ j).2
  choose ψ hψ using hψ
  have hx' : x = ∑ j ∈ t, j.1 (ψ j) := by
    rw [← hμ]
    exact Finset.sum_congr rfl fun j _ => (hψ j).symm
  have hfix : ∀ j ∈ t, ∀ κ ∈ U, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = j.1 (ψ j) := by
    intro j hj κ hκ
    have h0 := hind (fun j => j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ - j.1 (ψ j))
      (fun j _ => Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)) ?_ j hj
    · exact sub_eq_zero.1 h0
    · rw [Finset.sum_sub_distrib]
      have e : ∑ j ∈ t, j.1 ⟨Formalism.L2.NG.rt L n κ (ψ j), σ.stable κ _ (ψ j).2⟩ = ρ κ x := by
        rw [hx', map_sum]
        exact Finset.sum_congr rfl fun j _ => j.2.1 κ (ψ j)
      rw [e, hU κ hκ, ← hx', sub_self]
  have hterm : ∀ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) = j.1 (ψ j) := by
    intro j hj
    rcases zero_or_inj j.2.1 with h0 | hinj
    · simp [h0]
    · have hψfix : ∀ κ ∈ U, Formalism.L2.NG.rt L n κ ((ψ j : σ.S) : Formalism.AUTREP.GAf L n → ℂ) = ψ j :=
        fun κ hκ => congrArg Subtype.val (hinj (hfix j hj κ hκ))
      have hH := H _ (ψ j).2 hψfix
      have e : ∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S) = ψ j := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa using hH
      calc ∑ i, b i • ρ (lf i) (j.1 (ψ j))
          = j.1 (∑ i, b i • (⟨Formalism.L2.NG.rt L n (lf i) (ψ j), σ.stable (lf i) _ (ψ j).2⟩ : σ.S)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul, j.2.1 (lf i) (ψ j)]
        _ = j.1 (ψ j) := by rw [e]
  calc ∑ i, b i • ρ (lf i) x = ∑ j ∈ t, ∑ i, b i • ρ (lf i) (j.1 (ψ j)) := by
        rw [hx']
        simp only [map_sum, Finset.smul_sum]
        exact Finset.sum_comm
    _ = x := by
        rw [Finset.sum_congr rfl hterm, ← hx']

end Gen

theorem isotIn_conjT_fix_sum : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  intro D n A _ _ ρ C π U ι _ a lf hyp S hS hU
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  refine fix_sum_of_mem (σ := FinTyp.conjT π) (fun Φ => LinearMap.range Φ ≤ C) U (fun i => star (a i)) lf ?_ S hS hU
  intro ψ hψ hfix
  have hφ : (fun g => star (ψ g)) ∈ π.S := hψ
  have h1 := hyp _ hφ (fun κ hκ => by rw [← conj_rt, hfix κ hκ])
  rw [finsum_eq_sum_of_fintype] at h1
  funext g
  have h2 := congrArg star (congrFun h1 g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', star_star, rt_apply] at h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rt_apply]
  exact h2

end GlobalTheory.IsotConjFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.principalLevelFrame GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.RowFrameParts

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R F X0), StdPsi Y.hF Y.PY ∧ ∀ σ, R.HE.e (Y.eE (D.what₂.onb σ)) ∈ isotE R.θ Y.PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rowRepR R.θ (Y.eFT (D.what₂.ft σ))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y
  refine ⟨Y.stdPsi.1, fun σ => ?_⟩
  have h := Y.tied.sharp.ft σ
  have h1 := Y.prtE (D.what₂.ft σ)
  have h2 := Y.eE_read (D.what₂.onb σ)
  have h3 := h1 ▸ h
  obtain ⟨z, hz, hze⟩ := h3
  rw [h2] at hze
  have : z = R.HE.e (Y.eE (D.what₂.onb σ)) := LinearEquiv.injective _ hze
  rw [← this]
  exact hz

end GlobalTheory.Mem.R3.RowFrameParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotentStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_commutes_with_unipotent : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetup.exists_setup_both | exact GlobalTheory.Amp.LocalSetup.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetup.exists_setup_both <;> assumption)
end

