import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCells
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.CellQuotInt

theorem isQuotInt_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ J hJ f hfJ hfR T hT
  classical
  obtain ⟨bX, lX, sX, -, -, -, hXH, hXR⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -, -, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  obtain ⟨hN, -, hH, hRi, hconj⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p hp hpc ν
  haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μX.IsMulRightInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]
    infer_instance
  have hRm : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p :=
    fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)
  have hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) :=
    (GlobalTheory.QuotInt.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let S : GL (n ⊕ Fin c) k → Set (GL n k × N k n c p) :=
    fun h => {z | h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J}
  have hSo : ∀ h, IsOpen (S h) := fun h =>
    hJ.1.preimage ((continuous_const.mul hm).mul continuous_const)
  have hScomp : ∀ h, ∃ D, IsCompact D ∧ S h ⊆ D := by
    intro h
    have hK : IsCompact ((fun x => h * x * h⁻¹) '' (J : Set (GL (n ⊕ Fin c) k))) :=
      hJ.2.image (by fun_prop)
    obtain ⟨D, hD, hDm⟩ := GlobalTheory.QuotInt.compact_preimage hN hK
    exact ⟨D, hD, fun z hz => hDm z ⟨_, hz, by group⟩⟩
  have hvol : ∀ h, volCell ν μX p J h = (μX.prod (volN ν n c p)) (S h) := by
    intro h
    rw [Measure.prod_apply (hSo h).measurableSet]
    rfl
  have hvol0 : ∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤ := by
    intro h
    obtain ⟨D, hD, hSD⟩ := hScomp h
    rw [hvol]
    exact ⟨(hSo h).measure_ne_zero _ ⟨(1, 1), by simp [S, J.one_mem]⟩,
      ((measure_mono hSD).trans_lt hD.measure_lt_top).ne⟩

  have hcell : ∀ h, ∫ g, (∫ u : N k n c p, (if h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0)
      ∂(volN ν n c p)) ∂μX = (((volCell ν μX p J h).toReal : ℝ) : ℂ) := by
    intro h
    have e : (fun z : GL n k × N k n c p =>
        if h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0) =
        (S h).indicator (fun _ => (1 : ℂ)) := by
      funext z
      simp [S, Set.indicator_apply]
    have hint : Integrable ((S h).indicator (fun _ => (1 : ℂ))) (μX.prod (volN ν n c p)) := by
      rw [integrable_indicator_iff (hSo h).measurableSet]
      exact integrableOn_const (by rw [← hvol]; exact (hvol0 h).2)
    rw [← e] at hint
    have h2 := integral_prod _ hint
    simp only at h2
    rw [← h2, e, integral_indicator_const _ (hSo h).measurableSet, Measure.real, ← hvol]
    simp
  have hmod : ∀ (φ : GL (n ⊕ Fin c) k → ℂ) (g₀ : GL n k) (u₁ : GL (n ⊕ Fin c) k), u₁ ∈ N k n c p →
      ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p)) ∂μX
        = ((nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) *
          ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX := by
    intro φ g₀ u₁ hu₁
    have hpos : ∀ y : kˣ, 0 < nabs k y := fun y => (nabs_properties k).2.1 y
    have e3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^ (-((c : ℝ) + 1 - 2 * p)) =
        nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) := by
      have h3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
        simp [nabs]
      rw [h3, Real.inv_rpow (hpos _).le, ← Real.rpow_neg (hpos _).le, neg_neg]
    have step : ∀ g : GL n k,
        ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p)) •
            ∫ u : N k n c p, φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p) := by
      intro g
      have e1 := hconj g₀⁻¹ (fun y => φ (embX c (g * g₀) * y * u₁))
      have e2 := integral_mul_right_eq_self (μ := volN ν n c p)
        (fun u : N k n c p => φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k))) ⟨u₁, hu₁⟩
      simp only [Subgroup.coe_mul, ← mul_assoc] at e2
      rw [e3, e2] at e1
      rw [← e1]
      congr 1
      funext u
      congr 1
      simp only [map_mul, map_inv]
      group
    simp only [step]
    rw [integral_smul, Complex.real_smul]
    congr 1
    have := integral_mul_right_eq_self (μ := μX)
      (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) g₀
    simpa using this

  have hv0 : ∀ h, (volCell ν μX p J h).toReal ≠ 0 := fun h =>
    ENNReal.toReal_ne_zero.2 (hvol0 h)
  let F : GL (n ⊕ Fin c) k → ℂ := fun x =>
    ∑ t ∈ T, if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0
  have hFsb : F ∈ SB (GL (n ⊕ Fin c) k) := by
    have := GlobalTheory.QuotInt.sb_of_quot J hJ.1 hJ.2 (T.image (QuotientGroup.mk : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k ⧸ J))
      (fun q => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = q then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0)
      (fun q hq => Finset.sum_eq_zero fun t ht => if_neg fun e => hq (Finset.mem_image.2 ⟨t, ht, e⟩))
    have hFeq : F = fun x : GL (n ⊕ Fin c) k => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = (x : GL (n ⊕ Fin c) k ⧸ J) then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0 := by
      funext x
      simp only [F, QuotientGroup.eq]
    rw [hFeq]
    exact this
  have hFint : ∫ x, F x ∂μG =
      ∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
    have hind : ∀ t : GL (n ⊕ Fin c) k,
        Integrable (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) μG ∧
        ∫ x, (if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) ∂μG =
          ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
      intro t
      have e : (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) =
          fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) (t⁻¹ * x) := by
        funext x
        simp [Set.indicator_apply]
      have hi : Integrable ((J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ))) μG := by
        rw [integrable_indicator_iff hJ.1.measurableSet]
        exact integrableOn_const hJ.2.measure_lt_top.ne
      rw [e]
      refine ⟨hi.comp_mul_left t⁻¹, ?_⟩
      rw [integral_mul_left_eq_self (fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) x) t⁻¹,
        integral_indicator_const _ hJ.1.measurableSet]
      simp only [Measure.real, Complex.real_smul]
      have := hv0 t
      push_cast
      field_simp
    show ∫ x, (∑ t ∈ T, _) ∂μG = _
    rw [integral_finset_sum _ (fun t _ => (hind t).1)]
    exact Finset.sum_congr rfl fun t _ => (hind t).2

  have hRinv : ∀ (y t : GL (n ⊕ Fin c) k), t⁻¹ * y ∈ J →
      DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t := by
    intro y t hy
    rw [DoubleCoset.eq]
    exact ⟨1, one_mem _, (t⁻¹ * y)⁻¹, J.inv_mem hy, by group⟩
  have hmkR : ∀ r ∈ R k n c p, ∀ y,
      DoubleCoset.mk (R k n c p) J (r * y) = DoubleCoset.mk (R k n c p) J y := by
    intro r hr y
    rw [DoubleCoset.eq]
    exact ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩
  have hFcell : ∀ t₀ ∈ T, ∀ y, DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t₀ →
      F y = if t₀⁻¹ * y ∈ J then f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) else 0 := by
    intro t₀ ht₀ y hy
    show (∑ t ∈ T, _) = _
    rw [Finset.sum_eq_single t₀]
    · intro t ht hne
      rw [if_neg]
      intro hmem
      exact hne (hT.1 (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht₀) ((hRinv y t hmem).symm.trans hy))
    · intro h
      exact absurd ht₀ h
  have hFoff : ∀ y, (∀ t ∈ T, DoubleCoset.mk (R k n c p) J y ≠ DoubleCoset.mk (R k n c p) J t) → F y = 0 := by
    intro y hy
    exact Finset.sum_eq_zero fun t ht => if_neg fun hmem => hy t ht (hRinv y t hmem)
  have havg : ∀ x, f x = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * x)
      ∂(volN ν n c p)) ∂μX := by
    intro x
    by_cases hx : ∃ t ∈ T, DoubleCoset.mk (R k n c p) J x = DoubleCoset.mk (R k n c p) J t
    · obtain ⟨t₀, ht₀, hxt⟩ := hx
      obtain ⟨r, hr, j, hj, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 hxt.symm
      obtain ⟨g₀, u₁, hu₁, rfl⟩ := Radical.exists_of_mem_R hr
      set φ : GL (n ⊕ Fin c) k → ℂ := fun y => f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) *
              (if t₀⁻¹ * y * t₀ ∈ J then (1 : ℂ) else 0) with hφ
      have key : ∀ (g : GL n k) (u : N k n c p),
          F (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j)) =
            φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) := by
        intro g u
        have hw : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁) ∈ R k n c p :=
          mul_mem (hRm g u) hr
        have e : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j) =
            (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        have hmk : DoubleCoset.mk (R k n c p) J
            ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            DoubleCoset.mk (R k n c p) J t₀ := by
          rw [DoubleCoset.eq]
          exact ⟨_, inv_mem hw, j⁻¹, J.inv_mem hj, by group⟩
        rw [e, hFcell t₀ ht₀ _ hmk]
        have e2 : t₀⁻¹ * ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            t₀⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        simp only [hφ, e2, J.mul_mem_cancel_right hj]
        split_ifs <;> simp
      simp only [key]
      rw [hmod φ g₀ u₁ hu₁]
      simp only [hφ, integral_const_mul]
      rw [hcell t₀, hfJ _ j hj, hfR g₀ u₁ hu₁ t₀]
      rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 (hv0 t₀))]
    · have hf0 : f x = 0 := by
        by_contra h0
        exact hx (hT.2 x h0)
      rw [hf0]
      have : ∀ (g : GL n k) (u : N k n c p), F (embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        apply hFoff
        intro t ht e
        exact hx ⟨t, ht, (hmkR _ (hRm g u) x).symm.trans e⟩
      simp [this]
  have hz₀ : IsQuotInt ν μX μG p f
      (∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t) :=
    ⟨F, hFsb, havg, hFint.symm⟩
  have huniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).1
  exact ⟨hvol0, fun z => ⟨fun hz => huniq _ _ hz hz₀, fun e => by rw [e]; exact hz₀⟩⟩

end GlobalTheory.CellQuotInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section Field
variable {F : Type} [Field F] {κ l : ℕ}

theorem mul_fromBlocks_inl (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin κ) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inl j) = ∑ t, M a (Sum.inl t) * C t j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_fromBlocks_inr (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin l) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inr j) = M a (Sum.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pat_of_mul (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by
  intro a b hab
  have hv : (u * embX l γ).val = u.val * fromBlocks γ.val 0 0 1 := by
    rw [Units.val_mul, Radical.embX_val]
  rw [hv]
  rcases a with i | i <;> rcases b with j | j <;> simp only [FreeTop, not_lt] at hab
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inl i) (Sum.inl t) = if i = t then 1 else 0 := fun t => by
      rw [hu (Sum.inl i) (Sum.inl t) le_rfl, Matrix.one_apply]; simp
    simp only [hu', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hγ i j (by exact_mod_cast hab)]
    simp [Matrix.one_apply]
  · rw [mul_fromBlocks_inr, hu (Sum.inl i) (Sum.inr j) (Nat.succ_le_succ hab)]
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
      rw [hu (Sum.inr i) (Sum.inl t) (Nat.succ_le_succ hab)]; simp
    simp [hu']
  · rw [mul_fromBlocks_inr, hu (Sum.inr i) (Sum.inr j) (Nat.succ_le_succ hab)]

theorem exists_of_pat (ρ : ℕ) (gb : GL (Fin κ ⊕ Fin l) F)
    (h : ∀ a b, ¬ FreeTop ρ a b → gb.val a b = (1 : Matrix _ _ F) a b) :
    ∃ u : GL (Fin κ ⊕ Fin l) F, InN (ρ + 1) u ∧ ∃ γ : GL (Fin κ) F,
      IsUpperUnip Fin.val γ.val ∧ gb = u * embX l γ := by
  have hU : IsUpperUnip Fin.val gb.val.toBlocks₁₁ := fun r t hrt => by
    have := h (Sum.inl r) (Sum.inl t) (by simp only [FreeTop, not_lt]; exact hrt)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have hdet : gb.val.toBlocks₁₁.det = 1 := Radical.Uni.det (b := Fin.val) hU
  let γ : GL (Fin κ) F := ⟨gb.val.toBlocks₁₁, gb.val.toBlocks₁₁⁻¹,
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one),
    Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)⟩
  refine ⟨gb * (embX l γ)⁻¹, ?_, γ, hU, (inv_mul_cancel_right gb _).symm⟩
  have hv : (gb * (embX l γ)⁻¹).val = gb.val * fromBlocks (γ⁻¹).val 0 0 1 := by
    rw [Units.val_mul, ← map_inv, Radical.embX_val]
  intro r t hrt
  rw [hv]
  rcases r with i | i <;> rcases t with j | j
  · rw [mul_fromBlocks_inl]
    have hm : ∑ q, gb.val (Sum.inl i) (Sum.inl q) * (γ⁻¹).val q j =
        (1 : Matrix (Fin κ) (Fin κ) F) i j := by
      have := congrFun (congrFun γ.mul_inv i) j
      rw [Matrix.mul_apply] at this
      exact this
    rw [hm]
    simp [Matrix.one_apply]
  · have hrt' : j.val + 1 ≤ ρ + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; omega)
  · have hrt' : ρ + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inl]
    have hz : ∀ q, gb.val (Sum.inr i) (Sum.inl q) = 0 := fun q => by
      have := h (Sum.inr i) (Sum.inl q) (by simp only [FreeTop, not_lt]; omega)
      simpa [Matrix.one_apply] using this
    simp [hz]
  · have hrt' : j.val + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; exact Fin.le_def.mpr (by omega))

end Field

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem valuation_lt_one_iff_residue_eq_zero (y : 𝒪[k]) :
    valuation k (y : k) < 1 ↔ IsLocalRing.residue 𝒪[k] y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm

theorem entry_lt_iff (g₀ : GL ι 𝒪[k]) (a b : ι) :
    valuation k ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b) < 1 ↔
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b = (1 : Matrix ι ι 𝓀[k]) a b := by
  have e1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b =
      ((g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b : 𝒪[k]) : k) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  have e2 : (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b -
      (1 : Matrix ι ι 𝓀[k]) a b = IsLocalRing.residue 𝒪[k] (g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e1, valuation_lt_one_iff_residue_eq_zero, ← e2, sub_eq_zero]

end Local

end GlobalTheory.SymPattern

theorem GlobalTheory.SymChain.SymData.mem_J_iff_pattern :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k),
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  intro k _ _ _ _ s κ S g
  rw [S.sym.1 g]
  constructor
  · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
    refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
    rw [← hg₀, SymPattern.entry_lt_iff, hgb]
    exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
  · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
    obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
        rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
    exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiEqSumCoupIdx
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.Couple

theorem psi_eq_sum_coupIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by
  intro k _ _ _ _ _ _ s X _ _ Z _ _ T A c₁ c₂ hA ψ hψ ν _ ε S hS g hg x₀
  classical
  have key : ∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := by
    intro y
    have hc : ∀ yb, cosetInd (box _ c₂) yb y = if Submodule.Quotient.mk y = yb then 1 else 0 := by
      intro yb; simp [cosetInd, Set.indicator_apply]
    simp_rw [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · exact (Chain.xiPen_mk hA hg y x₀).symm
    · by_contra hne
      exact hm (Finset.mem_coe.1 (hS ⟨y, (hA g hg x₀ y).1 hne, rfl, g, hg, x₀, hne⟩))
  refine ⟨key, fun η => ?_⟩
  have hfun : T.Psi g x₀ = fun y => ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := funext key
  rw [hfun]
  simp only [GlobalTheory.StepData.hat, Finset.sum_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun yb _ => ?_
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro yb _
    simp_rw [mul_assoc]
    exact (integrable_hat ψ ν ε hψ (cosetInd_mem_SB c₂ yb) η).const_mul _

end GlobalTheory.Couple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardOrderSymmInr
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymChain.NonZeroAt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Coords
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change (fromBlocks 1 0 0 (diagonal _) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · simp
  · simp [mul_inv_cancel₀, pow_ne_zero]

end Coords

section Ord
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ord

section Chain
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable (k) in

def Est (j : ℕ) : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k :=
  fun P Q => if P = ixSucc _ t j (.inl Q) then 1 else 0

def xst (j c : ℕ) (h : j + c = s) :
    Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k :=
  (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega))).bas.val *
    (Est k (κ := κ) (s := s) t j).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)).symm
      (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)).symm *
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).bas⁻¹).val

end Chain

section Entry
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Entry

section Main
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Main

section Final
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Final

end GlobalTheory.SymChain.NonZeroAt

namespace GlobalTheory.SymChain

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalOne

theorem zonalInt_one_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] :
    μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  intro hK γ ψ hψ
  have h1 : ψ 1 = 1 := by
    rw [hψ.2 1 (one_mem _) (fun _ => 1) (fun i => by simp)]
    simp [ord]
  have hκ : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := by
    intro κ hκ
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun GlobalTheory.SplitFlip.isOpen_KO.measurableSet hκ]
  simp [Measure.real, hK]

end GlobalTheory.ZonalOne
end

