import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsDistSectionMulBlock
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.SectionHsCompare

variable {P Q P' Q' : ℕ}

section Frob
open scoped Matrix.Norms.Frobenius

theorem frob_sq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

theorem frob_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖Z‖ ^ 2 = ‖Z (e none) (e none)‖ ^ 2 + ∑ b, ‖Z (e none) (e (some b))‖ ^ 2 +
      ∑ i, ‖Z (e (some i)) (e none)‖ ^ 2 + ∑ i, ∑ b, ‖Z (e (some i)) (e (some b))‖ ^ 2 := by
  have h : ∀ x, ∑ w, ‖Z x w‖ ^ 2 = ∑ o, ‖Z x (e o)‖ ^ 2 := fun x =>
    (e.sum_comp (fun w => ‖Z x w‖ ^ 2)).symm
  rw [frob_sq, Finset.sum_congr rfl (fun x _ => h x),
    ← e.sum_comp (fun x => ∑ o, ‖Z x (e o)‖ ^ 2)]
  simp only [Fintype.sum_option, Finset.sum_add_distrib]
  ring

theorem add_le_mul_pow_of_sq_le_of_le_mul {t η R W : ℝ} (ht : 1 < t) (hη : η = (t - 1) / (3 * t)) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (h1 : W ≤ R + η * R) (h2 : R ≤ W + η * R) :
    R ^ 2 ≤ t * W ^ 2 ∧ W ^ 2 ≤ t * R ^ 2 := by
  have h3 : 0 < 3 * t := by linarith
  have hη0 : 0 ≤ η := by rw [hη]; exact div_nonneg (by linarith) h3.le
  have key : η * (3 * t) = t - 1 := by rw [hη]; field_simp
  have hηt : η < 1 / 3 := by nlinarith
  constructor
  ·
    have hW' : (1 - η) * R ≤ W := by linarith
    have hsq : ((1 - η) * R) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by nlinarith) hW' 2
    have hge : 1 ≤ t * (1 - η) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ t), sq_nonneg R]
  ·
    have hW' : W ≤ (1 + η) * R := by linarith
    have hsq : W ^ 2 ≤ ((1 + η) * R) ^ 2 := pow_le_pow_left₀ hW hW' 2
    have hle : (1 + η) ^ 2 ≤ t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]

private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  nlinarith

theorem hsDist_section_mul_block : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  intro P Q P' Q' e j hj t ht
  set η : ℝ := (t - 1) / (3 * t) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by linarith)
  have hη3 : η < 1 / 3 := by
    rw [hη, div_lt_iff₀ (by linarith)]; linarith
  set c : ℝ := η / 3 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c < 1 := by linarith
  refine ⟨min 1 (c ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro y a hy hya hrow hblk g
  have hyc : ptSq e y < c ^ 2 := lt_of_lt_of_le hy (min_le_right _ _)
  have hy1 : ptSq e y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨h00, h0b, ha0, hab⟩ := hj g

  have hcol : ∀ x, UpqT.mat a x (e none) = y x := by
    intro x
    have := congrFun hya x
    simpa [act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set S : ℝ := ∑ i, ‖y (e (some i))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hpt : ptSq e y = ‖y (e none) - 1‖ ^ 2 + 2 * S := rfl
  have hSpt : S ≤ ptSq e y := by nlinarith [sq_nonneg ‖y (e none) - 1‖]
  have hSc : S < c ^ 2 := lt_of_le_of_lt hSpt hyc
  have hS1 : S < 1 := lt_of_le_of_lt hSpt hy1

  have hn1 : 1 ≤ ‖1 + y (e none)‖ := by
    have h1 : ‖y (e none) - 1‖ < 1 := by
      nlinarith [norm_nonneg (y (e none) - 1), sq_nonneg ‖y (e none) - 1‖]
    have h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖1 + y (e none)‖ + ‖y (e none) - 1‖ := by
      rw [h2]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith

  set M := UpqT.mat a with hM
  set K := UpqT.mat (j g) - 1 with hK
  set Ep : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun x w =>
    (e.symm x).elim 0 (fun _ => (e.symm w).elim 0 (fun _ => (M - 1) x w)) with hEp
  set Z0 := (M - 1) + K - Ep with hZ0
  set Z := UpqT.mat (a * j g) - 1 with hZ
  have hmul : UpqT.mat (a * j g) = M * UpqT.mat (j g) := rfl
  have hZe : Z = (M - 1) + K + (M - 1) * K := by
    rw [hZ, hmul, hK]; noncomm_ring
  have hdiff : Z - Z0 = Ep + (M - 1) * K := by
    rw [hZe, hZ0]; abel

  have hK2 : ‖K‖ ^ 2 = hsDist g := by
    rw [frob_split e K]
    simp [hK, Matrix.sub_apply, Matrix.one_apply, h00, h0b, ha0, hab, hsDist]
  have hEp2 : ‖Ep‖ ^ 2 = ∑ i, ∑ b, ‖(M - 1) (e (some i)) (e (some b))‖ ^ 2 := by
    rw [frob_split e Ep]
    simp [hEp, Matrix.of_apply]
  have hEpS : ‖Ep‖ ^ 2 ≤ S ^ 2 := by
    rw [hEp2, sq, hS, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    rw [hblk i b, div_pow, ← mul_pow]
    have hp : 0 ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := sq_nonneg _
    calc (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / ‖1 + y (e none)‖ ^ 2
        ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / 1 :=
          div_le_div_of_nonneg_left hp one_pos (by nlinarith)
      _ = (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := div_one _
  have hM2 : ‖M - 1‖ ^ 2 = ptSq e y + ‖Ep‖ ^ 2 := by
    rw [frob_split e (M - 1), hEp2, hpt]
    simp [Matrix.sub_apply, Matrix.one_apply, hcol, hrow]
    rw [hS, Fintype.sum_sum_type]
    ring
  have e00 : Z0 (e none) (e none) = y (e none) - 1 := by
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, hcol, h00]
  have e0b : ∀ b, Z0 (e none) (e (some b)) = M (e none) (e (some b)) := by
    intro b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, h0b]
  have ei0 : ∀ i, Z0 (e (some i)) (e none) = y (e (some i)) := by
    intro i
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hcol, ha0]
  have eib : ∀ i b, Z0 (e (some i)) (e (some b)) = (UpqT.mat g - 1) i b := by
    intro i b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hab]
  have hZ02 : ‖Z0‖ ^ 2 = ptSq e y + hsDist g := by
    rw [frob_split e Z0, e00]
    simp only [e0b, ei0, eib, hrow]
    rw [hpt, hS]
    unfold hsDist
    ring
  have hZ2 : ‖Z‖ ^ 2 = hsDist (a * j g) := by
    rw [frob_sq]; rfl

  have hR0 : 0 ≤ ‖Z0‖ := norm_nonneg _
  have hEpb : ‖Ep‖ ≤ c * ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [mul_pow, hZ02]
    have hg : 0 ≤ hsDist g := by rw [← hK2]; positivity
    calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
      _ = S * S := sq S
      _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
      _ ≤ ptSq e y * c ^ 2 := mul_le_mul_of_nonneg_right hSpt (sq_nonneg c)
      _ ≤ c ^ 2 * (ptSq e y + hsDist g) := by
        rw [mul_comm, mul_add]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hg)
  have hMb : ‖M - 1‖ ≤ 2 * c := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [hM2]
    have h1 : ‖Ep‖ ^ 2 ≤ c ^ 2 :=
      calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
        _ = S * S := sq S
        _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
        _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hS1.le (sq_nonneg c)
        _ = c ^ 2 := one_mul _
    have h2 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
    rw [h2]
    linarith [sq_nonneg c]
  have hKb : ‖K‖ ≤ ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg hR0
    rw [hK2, hZ02]
    have : 0 ≤ ptSq e y := by rw [hpt]; positivity
    linarith
  have hdb : ‖Z - Z0‖ ≤ η * ‖Z0‖ := by
    rw [hdiff]
    calc ‖Ep + (M - 1) * K‖ ≤ ‖Ep‖ + ‖(M - 1) * K‖ := norm_add_le _ _
      _ ≤ ‖Ep‖ + ‖M - 1‖ * ‖K‖ := by gcongr; exact Matrix.frobenius_norm_mul _ _
      _ ≤ c * ‖Z0‖ + 2 * c * ‖Z0‖ := by gcongr
      _ = η * ‖Z0‖ := by rw [hc]; ring
  have h1 : ‖Z‖ ≤ ‖Z0‖ + η * ‖Z0‖ := by
    calc ‖Z‖ = ‖Z0 + (Z - Z0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖Z0‖ + ‖Z - Z0‖ := norm_add_le _ _
      _ ≤ ‖Z0‖ + η * ‖Z0‖ := by gcongr
  have h2 : ‖Z0‖ ≤ ‖Z‖ + η * ‖Z0‖ := by
    calc ‖Z0‖ = ‖Z - (Z - Z0)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Z‖ + ‖Z - Z0‖ := norm_sub_le _ _
      _ ≤ ‖Z‖ + η * ‖Z0‖ := by gcongr
  obtain ⟨hA, hB⟩ := add_le_mul_pow_of_sq_le_of_le_mul ht hη hR0 (norm_nonneg _) h1 h2
  rw [hZ02, hZ2] at hA hB
  exact ⟨hA, hB⟩

end Frob

end GlobalTheory.SectionHsCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqIintLeLiminf
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLower

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

omit [FiniteDimensional ℂ G] in
theorem hs_eq_sum (A : H →L[ℂ] G) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hs_adjoint [CompleteSpace H] [CompleteSpace G] (A : H →L[ℂ] G) :
    hsNormSq (ContinuousLinearMap.adjoint A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  have h1 : ∀ j, ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)‖ ^ 2 =
      ∑ i, ‖⟪stdOrthonormalBasis ℂ H i, ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)⟫_ℂ‖ ^ 2 :=
    fun j => ((stdOrthonormalBasis ℂ H).sum_sq_norm_inner_right _).symm
  have h2 : ∀ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 =
      ∑ j, ‖⟪A (stdOrthonormalBasis ℂ H i), stdOrthonormalBasis ℂ G j⟫_ℂ‖ ^ 2 :=
    fun i => ((stdOrthonormalBasis ℂ G).sum_sq_norm_inner_left _).symm
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

omit [FiniteDimensional ℂ G] in
theorem hs_isom_comp (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  simp [hU]

theorem hs_unitary [CompleteSpace H] [CompleteSpace G] (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (V : H →L[ℂ] H) (hV : ∀ v, ‖ContinuousLinearMap.adjoint V v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp (A.comp V)) = hsNormSq A := by
  rw [hs_isom_comp U hU, ← hs_adjoint, ContinuousLinearMap.adjoint_comp, hs_isom_comp _ hV, hs_adjoint]

omit [FiniteDimensional ℂ G] in
theorem hs_continuous : Continuous (hsNormSq : (H →L[ℂ] G) → ℝ) := by
  have : (hsNormSq : (H →L[ℂ] G) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 :=
    funext hs_eq_sum
  rw [this]
  fun_prop

end LinAlg

theorem exists_compact_approx {X E : Type} [PseudoMetricSpace X] [ProperSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ μ' : Measure X) [SFinite μ] [SFinite μ'] (S S' : Set X) (hS : IsClosed S) (hS' : IsClosed S')
    (h0 : μ Sᶜ = 0) (h0' : μ' S'ᶜ = 0) (F : X × X → E) (hF : Integrable F (μ.prod μ')) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C C' : Set X, IsCompact C ∧ C ⊆ S ∧ IsCompact C' ∧ C' ⊆ S' ∧
      ∀ A A' : Set X, MeasurableSet A → MeasurableSet A' → C ⊆ A → C' ⊆ A' →
        ‖∫ p, F p ∂((μ.restrict A).prod (μ'.restrict A')) - ∫ p, F p ∂(μ.prod μ')‖ < δ := by
  obtain ⟨o⟩ := ‹Nonempty X›
  let K : ℕ → Set (X × X) := fun n =>
    ((S ∩ Metric.closedBall o n) ×ˢ (S' ∩ Metric.closedBall o n))ᶜ
  have hKm : ∀ n, MeasurableSet (K n) := fun n =>
    ((hS.inter Metric.isClosed_closedBall).measurableSet.prod
      (hS'.inter Metric.isClosed_closedBall).measurableSet).compl
  have hKa : Antitone K := by
    intro m n hmn
    have hb : Metric.closedBall o (m : ℝ) ⊆ Metric.closedBall o n :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    exact Set.compl_subset_compl.2
      (Set.prod_mono (Set.inter_subset_inter_right _ hb) (Set.inter_subset_inter_right _ hb))
  have hlim := tendsto_setIntegral_of_antitone (f := fun p => ‖F p‖) (μ := μ.prod μ') hKm hKa
    ⟨0, hF.norm.integrableOn⟩
  have hnull : (μ.prod μ') (⋂ n, K n) = 0 := by
    have hsub : (⋂ n, K n) ⊆ (Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ S'ᶜ) := by
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
        not_or, not_not] at hc
      obtain ⟨n, hn⟩ := exists_nat_ge (max (dist p.1 o) (dist p.2 o))
      exact Set.mem_iInter.1 hp n ⟨⟨hc.1, (le_max_left _ _).trans hn⟩, hc.2, (le_max_right _ _).trans hn⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_) <;> rw [Measure.prod_prod]
    · rw [h0, zero_mul]
    · rw [h0', mul_zero]
  rw [setIntegral_measure_zero _ hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨S ∩ Metric.closedBall o n, S' ∩ Metric.closedBall o n,
    (isCompact_closedBall o n).inter_left hS, Set.inter_subset_left,
    (isCompact_closedBall o n).inter_left hS', Set.inter_subset_left, fun A A' hA hA' hCA hCA' => ?_⟩
  rw [Measure.prod_restrict, ← integral_add_compl (hA.prod hA') hF, sub_add_cancel_left, norm_neg]
  refine (norm_integral_le_integral_norm _).trans_lt (lt_of_le_of_lt ?_ hn)
  refine setIntegral_mono_set hF.norm.integrableOn (Eventually.of_forall fun p => norm_nonneg _)
    (HasSubset.Subset.eventuallyLE ?_)
  exact Set.compl_subset_compl.2 (Set.prod_mono hCA hCA')

theorem le_liminf_of_ratio (b : ENNReal) (hb : b ≠ ⊤) (u m m' n n' : ℕ → ENNReal)
    (hn : ∀ j, 0 < n j ∧ n j < ⊤) (hn' : ∀ j, 0 < n' j ∧ n' j < ⊤)
    (h : Tendsto (fun j => m j / n j) atTop (𝓝 1)) (h' : Tendsto (fun j => m' j / n' j) atTop (𝓝 1))
    (hu : ∀ j, b * (m j * m' j) ≤ u j) : b ≤ liminf (fun j => u j / (n j * n' j)) atTop := by
  have ht : Tendsto (fun j => b * (m j / n j * (m' j / n' j))) atTop (𝓝 (b * (1 * 1))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul h (Or.inl one_ne_zero) h' (Or.inl one_ne_zero))
      (Or.inr hb)
  rw [mul_one, mul_one] at ht
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
  have e : b * (m j / n j * (m' j / n' j)) = b * (m j * m' j) / (n j * n' j) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (hn j).1.ne') (Or.inl (hn j).2.ne)]
    ring
  rw [e]
  exact ENNReal.div_le_div_right (hu j) _

variable {k r : ℕ}

theorem measurableSet_rmul_image {t : Mat k r} (ht : IsUnit t.det) {A : Set (Mt k r)}
    (hA : MeasurableSet A) : MeasurableSet (rmulM t '' A) := by
  have : rmulM t '' A = rmulM t⁻¹ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : rmulM t⁻¹ (rmulM t y) = y := Matrix.mul_nonsing_inv_cancel_right t (Matrix.of y) ht
      rw [Set.mem_preimage, this]; exact hy
    · intro hx
      exact ⟨_, hx, Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht⟩
  rw [this]
  exact (continuous_rmulM _).measurable hA

theorem subset_rmul_image {t : Mt k r} (ht : IsUnit (Matrix.of t : Mat k r).det) {C Oc Om : Set (Mt k r)}
    (h : ∀ c ∈ C, ∀ x ∈ Oc, lmulM (Matrix.of c) x ∈ Om) (hO : invM t ∈ Oc) :
    C ⊆ rmulM (Matrix.of t) '' Om := fun c hc =>
  ⟨_, h c hc _ hO, Matrix.nonsing_inv_mul_cancel_right (Matrix.of t) (Matrix.of c) ht⟩

theorem hsNormSq_Iint_le_liminf : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ Om Om' : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → IsFolner (Sset k r z') μS' Om' → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ)) ≤ Filter.liminf (fun j => (∫⁻ p, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of (act2 γ p)))) ∂(μS.prod μS')) / (μS (Om j) * μS' (Om' j))) Filter.atTop := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' Om Om' hF hF'
    x hx y hy ξ ξ' γ hγ
  have hint := (GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' y hy x hx ξ ξ' γ hγ).1
  have hcl := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hS.1 hS.2.1).2.2.2.1
  have hcl' := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hS'.1 hS'.2.1).2.2.2.1
  have hP := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hS.1 hS.2.1 hS.2.2.1
  have hP' := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hS'.1 hS'.2.1 hS'.2.2.1
  have hinv := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hS.1 hS.2.1 μS).1 hS.2.2.2.1).2
  have hinv' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hS'.1 hS'.2.1 μS').1 hS'.2.2.2.1).2
  haveI := hS.2.2.2.1.1
  haveI := hS'.2.2.2.1.1
  have h0 := hS.2.2.2.1.2.2.1
  have h0' := hS'.2.2.2.1.2.2.1
  refine ENNReal.le_of_forall_nnreal_lt fun b hb => ?_
  have hb' : (b : ℝ) < hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ) := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg b.coe_nonneg] at hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hs_continuous (H := Wq) (G := Wp)).continuousAt.eventually (lt_mem_nhds hb'))
  obtain ⟨C, C', hC, hCS, hC', hCS', happ⟩ := exists_compact_approx μS μS'
    {x | Matrix.of x ∈ Sset k r z} {x | Matrix.of x ∈ Sset k r z'} hcl.2.1 hcl'.2.1 h0 h0' _ hint hδ
  obtain ⟨Oc, hOc, hlim⟩ := hF.2 C hC hCS
  obtain ⟨Oc', hOc', hlim'⟩ := hF'.2 C' hC' hCS'
  refine le_liminf_of_ratio b ENNReal.coe_ne_top _ _ _ _ _ (fun j => (hF.1 j).2.2.2)
    (fun j => (hF'.1 j).2.2.2) hlim hlim' fun j => ?_
  have e1 : μS (Oc j) = μS (invM ⁻¹' Oc j) := by
    rw [← Measure.map_apply measurable_invM (hOc j).1, hinv]
  have e2 : μS' (Oc' j) = μS' (invM ⁻¹' Oc' j) := by
    rw [← Measure.map_apply measurable_invM (hOc' j).1, hinv']
  rw [e1, e2, ← Measure.prod_prod, ← lintegral_indicator_const
    ((measurable_invM (hOc j).1).prod (measurable_invM (hOc' j).1))]
  have hae : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z ∧ Matrix.of p.2 ∈ Sset k r z' :=
    (Measure.quasiMeasurePreserving_fst.ae (p := fun x => Matrix.of x ∈ Sset k r z) h0).and
      (Measure.quasiMeasurePreserving_snd.ae (p := fun x => Matrix.of x ∈ Sset k r z') h0')
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  by_cases hm : p ∈ (invM ⁻¹' Oc j) ×ˢ (invM ⁻¹' Oc' j)
  swap
  · rw [Set.indicator_of_notMem hm]; exact zero_le
  rw [Set.indicator_of_mem hm, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : IsUnit (Matrix.of p.1 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl.1 hp.1)
  have hu' : IsUnit (Matrix.of p.2 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl'.1 hp.2)
  have heq := GlobalTheory.T.Iint_equivariant_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' x y ξ ξ' (Om j) (Om' j)
    (hF.1 j).1 (hF'.1 j).1 γ hγ.1 _ hp.1 _ hp.2
  have ha : (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹ := rfl
  rw [ha, heq, hs_unitary _ (hP.2.1.2.1 _ hp.1)]
  · refine (hball ?_).le
    rw [dist_eq_norm]
    exact happ _ _ (measurableSet_rmul_image hu (hF.1 j).1) (measurableSet_rmul_image hu' (hF'.1 j).1)
      (subset_rmul_image hu (hOc j).2.2 hm.1) (subset_rmul_image hu' (hOc' j).2.2 hm.2)
  · rw [← (hP'.2.2.1 _ hp.2).2, ContinuousLinearMap.adjoint_adjoint]
    exact hP'.2.1.2.1 _ hp.2

end GlobalTheory.SgInf.FolnerLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilation
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreScaling

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_real_smul (r : ℝ) (x : Sp P Q) : qf (r • x) = r ^ 2 * qf x := by
  simp only [qf, Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal, mul_sub,
    Finset.mul_sum, sq]

theorem finrank_sp : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem map_dx_smul {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (P + Q)) • (dx P Q).map (fun y => Real.sqrt t • y) = dx P Q := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h := Measure.map_addHaar_smul (volume : Measure (Sp P Q)) hs
  rw [finrank_sp, pow_mul, Real.sq_sqrt ht.le, abs_of_pos (by positivity)] at h
  rw [dx, Measure.map_smul, h, smul_comm, smul_smul (ENNReal.ofReal _),
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_smul]

theorem lintegral_inv_mul {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ b, g (t⁻¹ * b) = ENNReal.ofReal t * ∫⁻ b, g b := by
  have h := (Homeomorph.mulLeft₀ t⁻¹ (inv_ne_zero ht.ne')).measurableEmbedding.lintegral_map
    (μ := volume) g
  rw [Homeomorph.coe_mulLeft₀, Real.map_volume_mul_left (inv_ne_zero ht.ne'), inv_inv,
    abs_of_pos ht, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

theorem isDxDq_scale {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) {t : ℝ} (ht : 0 < t) :
    IsDxDq fun b => ENNReal.ofReal (t ^ (P + Q) / t) •
      (fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hc : Continuous (fun y : Sp P Q => Real.sqrt t • y) := continuous_const_smul _
  have hm := hc.measurable
  have hpre : (fun y : Sp P Q => Real.sqrt t • y) ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} :=
    Set.ext fun x => by simp [hs]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hsu hts => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ :=
      ((qf_continuous.measurable (measurableSet_singleton _)).inter isOpen_ne.measurableSet).compl
    have h0 : ((fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y))
        (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ = 0 := by
      rw [Measure.map_apply hm hS]
      convert h.1 (t⁻¹ * b) using 2
      rw [Set.preimage_compl, Set.preimage_inter, hpre]
      congr 2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id, qf_real_smul, Real.sq_sqrt ht.le]
      exact (eq_inv_mul_iff_mul_eq₀ ht.ne').symm
    rw [Measure.smul_apply, h0, smul_zero]
  · simp only [lintegral_smul_measure, lintegral_map hφ hm, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_mul ht fun b => ∫⁻ y, φ (Real.sqrt t • y) ∂(fib b),
      ← h.2.1 (fun x => φ (Real.sqrt t • x)) (hφ.comp hm), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ ht.ne']
    conv_lhs => rw [← map_dx_smul ht]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      Measure.restrict_map hm isOpen_ne.measurableSet, lintegral_map hφ hm, hpre]
  · have hs' : HasCompactSupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) :=
      hsu.comp_homeomorph (Homeomorph.smulOfNeZero (Real.sqrt t) hs)
    have ht' : tsupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) ⊆ {x | x ≠ 0} := by
      rw [← hpre]
      exact (tsupport_comp_subset_preimage φ hc).trans (Set.preimage_mono hts)
    obtain ⟨h1, h2⟩ := h.2.2 _ (hφ.comp hc) hs' ht'
    refine ⟨fun b _ => ?_, ?_⟩
    · exact ((integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).2
        (h1 _ trivial)).smul_measure ENNReal.ofReal_ne_top
    · simp only [integral_smul_measure, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
      exact (((continuousOn_univ.1 h2).comp (continuous_const_mul t⁻¹)).const_smul
        (ENNReal.ofReal (t ^ (P + Q) / t)).toReal).continuousOn

theorem lintegral_fibre_scale : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib →
    β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂(fib (t * β)) =
        ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  intro P Q fib β t h hβ ht φ hφ
  have hO : (qf : Sp P Q → ℝ) ⁻¹' {t * β} ⊆ {x | x ≠ 0} := by
    rintro x hx rfl
    exact mul_ne_zero ht.ne' hβ (by simpa [qf] using hx.symm)
  have e := GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
    Set.univ fib _ (t * β) qf_continuous.measurable isOpen_ne subset_rfl subset_rfl hO isOpen_univ
    isOpen_univ trivial trivial h (isDxDq_scale h ht)
  rw [e, lintegral_smul_measure, smul_eq_mul, inv_mul_cancel_left₀ ht.ne',
    lintegral_map hφ (continuous_const_smul _).measurable]

end GlobalTheory.FibreScaling
end
end

