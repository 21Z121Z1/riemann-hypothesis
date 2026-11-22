import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

def zeroExt (m k : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m + k)) where
  toFun x := WithLp.toLp 2 (Fin.append (fun i => x i) 0)
  map_add' x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' c x := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem norm_zeroExt (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp

theorem isometry_zeroExt (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)

theorem coordBall_mass {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
      · rw [← norm_zeroExt m k]
        convert hy using 2
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
      · ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro hi
        simp at hi
        omega
      · intro _
        simp [zeroExt]
  rw [hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  rw [hd]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

def linProjₗ {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := linProj π
  map_add' x y := by
    ext i
    simp [linProj, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [linProj, Finset.mul_sum, mul_left_comm]

theorem ae_fibreCount_eq_zero {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩

theorem ConeIntegralMass.proof (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

theorem ConeMapArea.proof (h : ConeMapAreaOne.Statement) : ConeMapArea.Statement := by
  intro n e ι _ U D v F hUD hinj hF
  let g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n) := fun i q => q.2 • WithLp.toLp 2 (v i q.1)
  let S : ι → Set ((Fin e → ℂ) × ℂ) := fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}
  have himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, x, t⟩, hq, rfl⟩
      exact ⟨i, (x, t), hq, rfl⟩
    · rintro ⟨i, ⟨x, t⟩, hq, rfl⟩
      exact ⟨(i, x, t), hq, rfl⟩
  have hinj_i : ∀ i, Set.InjOn (g i) (S i) := by
    intro i p hp p' hp' hpp
    exact (Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2
  have hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩
    exact hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm
  have hmeas : ∀ i, MeasurableSet (g i '' S i) := by
    intro i
    obtain ⟨-, hD, hDU, hv⟩ := hUD i
    refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)
    · exact (measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)
    · have hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn
          ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)
      exact continuousOn_snd.smul hc
  rw [himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  obtain ⟨hU, hD, hDU, hv⟩ := hUD i
  exact h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeMeetNull.null_of_mem_not_mem (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {g} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) :=
    ZeroLocusDimH.le_of_add_one_le_succ
      ((ZeroLocusDimH.ringKrullDim_quot_sup_add_one_le W g hgW).trans hW)

  let φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hφ : ∀ y, φ y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective φ := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz φ).mp hinj

  have hsub : coneBall h W ∩ coneBall h W' ⊆ φ ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, ⟨-, hyW'⟩⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hyW' g hgW'
    intro q hq
    rw [hφ]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ coneBall h W') ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ coneBall h W') < (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

theorem ConeMeetNull.proof (hZ : ZeroLocusDimH.Statement) : ConeMeetNull.Statement := by
  intro n e h W W' hWp hW'p hne hW hW'
  by_cases hle : W' ≤ W
  ·
    have hnle : ¬ W ≤ W' := fun h' => hne (le_antisymm h' hle)
    obtain ⟨g, hgW, hgW'⟩ := Set.not_subset.mp hnle
    rw [Set.inter_comm]
    exact ConeMeetNull.null_of_mem_not_mem hZ h W' W hW' g hgW hgW'
  · obtain ⟨g, hgW', hgW⟩ := Set.not_subset.mp hle
    exact ConeMeetNull.null_of_mem_not_mem hZ h W W' hW g hgW' hgW

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFiniteFibresDimLe
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem isMaximal_of_zeroLocus_finite {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [hP : P.IsPrime]
    (hfin : (zeroLocus ℂ P : Set (Fin n → ℂ)).Finite) : P.IsMaximal := by
  have hle : (hfin.toFinset.inf fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) ≤ P := by
    intro q hq
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff]
    intro z hz
    have hq' := (Finset.inf_le (f := fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ)))
      (hfin.mem_toFinset.2 hz)) hq
    exact (mem_vanishingIdeal_iff.1 hq') z rfl
  obtain ⟨z, -, hz⟩ := hP.inf_le'.1 hle
  have hmax : (vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨z, rfl⟩
  rwa [← hmax.eq_of_le hP.ne_top hz]

theorem FiniteFibresDimLe.proof : FiniteFibresDimLe.Statement := by
  intro n d Q A hQ hfin
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  set y : Fin d → ℂ := A.mulVec x with hy
  let B := MvPolynomial (Fin n) ℂ ⧸ Q
  let _ : CommRing B := Ideal.Quotient.commRing Q
  let _ : IsDomain B := Ideal.Quotient.isDomain Q
  let _ : Algebra ℂ B := Ideal.Quotient.algebra ℂ
  let _ : Algebra.FiniteType ℂ B := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ Q))
  let m : Ideal B := M.map (Ideal.Quotient.mk Q)
  have hm : m.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hmp : m.IsPrime := hm.isPrime
  have hmh : (m.height : WithBot ℕ∞) = ringKrullDim B :=
    NumbersDVR.MaximalIdealHeightFG.proof ℂ B m hm
  have hlin : ∀ (z : Fin n → ℂ) (i : Fin d), eval z (ComplexSets.linPoly A i) = A.mulVec z i := by
    intro z i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_comm]
  let f : Fin d → B := fun i => Ideal.Quotient.mk Q (ComplexSets.linPoly A i - C (y i))
  have hfm : Set.range f ⊆ m := by
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_map_of_mem
    rw [hx, mem_vanishingIdeal_singleton_iff]
    simp [hlin, hy]
  have hK := Ideal.height_le_height_add_encard_of_subset (Set.range f) hfm
  have hcard : (Set.range f).encard ≤ d := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  let I : Ideal B := Ideal.span (Set.range f)
  have hIm : I ≤ m := by rw [Ideal.span_le]; exact hfm
  let p := m.map (Ideal.Quotient.mk I)
  have hpp : p.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIm
  have hp0 : p.height ≠ 0 := by
    intro h0
    change m.height ≤ p.height + _ at hK
    rw [h0, zero_add] at hK
    have : (m.height : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      exact_mod_cast hK.trans hcard
    exact absurd (hmh ▸ this) (not_le.2 hlt)
  change (⟨p, hpp⟩ : PrimeSpectrum (B ⧸ I)).asIdeal.height ≠ 0 at hp0
  rw [PrimeSpectrum.height_eq_orderHeight, ne_eq, Order.height_eq_zero] at hp0
  obtain ⟨P, hPlt⟩ := not_isMin_iff.1 hp0
  let π : MvPolynomial (Fin n) ℂ →+* B ⧸ I := (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk Q)
  have hπ : Function.Surjective π :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  let P' : Ideal (MvPolynomial (Fin n) ℂ) := P.asIdeal.comap π
  have hP' : P'.IsPrime := Ideal.comap_isPrime π P.asIdeal
  have hP'max : ¬ P'.IsMaximal := by
    intro hmax
    have hPm : P.asIdeal.IsMaximal := by
      have := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (m := P') (by
        intro a ha
        change π a ∈ P.asIdeal
        rw [RingHom.mem_ker.1 ha]; exact P.asIdeal.zero_mem)
      rwa [Ideal.map_comap_of_surjective π hπ] at this
    have hle : P.asIdeal ≤ p := hPlt.le
    exact (ne_of_lt hPlt) (PrimeSpectrum.ext (hPm.eq_of_le hpp.ne_top hle))
  apply hP'max
  apply isMaximal_of_zeroLocus_finite
  refine (hfin y).subset ?_
  intro z hz
  rw [mem_zeroLocus_iff] at hz
  have hz' : ∀ q ∈ P', eval z q = 0 := fun q hq => by simpa using hz q hq
  refine ⟨fun q hq => hz' q ?_, ?_⟩
  · change π q ∈ P.asIdeal
    have : π q = 0 := by
      simp [π, Ideal.Quotient.eq_zero_iff_mem.2 hq]
    rw [this]; exact P.asIdeal.zero_mem
  · funext i
    have hmem : ComplexSets.linPoly A i - C (y i) ∈ P' := by
      change π _ ∈ P.asIdeal
      have : π (ComplexSets.linPoly A i - C (y i)) = 0 := by
        change Ideal.Quotient.mk I (f i) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
      rw [this]; exact P.asIdeal.zero_mem
    have := hz' _ hmem
    rw [map_sub, eval_C, hlin, sub_eq_zero] at this
    exact this

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem localMult_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by
  let := Localization.AtPrime.algebraOfLiesOver W W'
  have : IsLocalHom (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have htow : (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')).comp
      (algebraMap A (Localization.AtPrime W)) =
      (algebraMap B (Localization.AtPrime W')).comp (algebraMap A B) := by
    ext x
    exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A (Localization.AtPrime W))).map
      (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) := by
    intro I
    rw [Ideal.map_map, Ideal.map_map, htow]
  have key := IsLocalRing.length_baseChange (Localization.AtPrime W) (Localization.AtPrime W')
    (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W')
    (J.map (algebraMap A (Localization.AtPrime W)))).toLinearEquiv.length_eq, hmap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), hmap, hfib] at key
  have : IsSimpleModule (Localization.AtPrime W')
      (Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one (R := Localization.AtPrime W')
    (M := Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')), mul_one] at key
  unfold localMult
  rw [dif_pos ‹W'.IsPrime›, dif_pos ‹W.IsPrime›, key]

section MinimalPrimes

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc

theorem comap_mem_minimalPrimes {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by
  have hPp : P.IsPrime := hP.1.1
  obtain ⟨W₀, hW₀, hW₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hP.1.2)
  have hW₀p : W₀.IsPrime := hW₀.1.1
  obtain ⟨P₀, hP₀, hP₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hW₀le)
  have hP₀p : P₀.IsPrime := hP₀.1.1
  have hEq : P₀ = P :=
    le_antisymm hP₀le (hP.2 ⟨hP₀p, (Ideal.map_mono hW₀.1.2).trans hP₀.1.2⟩ hP₀le)
  subst hEq
  rw [hc W₀ hW₀p P₀ hP₀]
  exact ⟨hW₀, hP₀⟩

theorem mem_minimalPrimes_map {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨hPp, (Ideal.map_mono hW.1.2).trans hP.1.2⟩, fun Q hQ hQP => ?_⟩
  have hQp : Q.IsPrime := hQ.1
  obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hQ.2
  obtain ⟨h1, -⟩ := comap_mem_minimalPrimes f hc hQ₀
  have hle : Q₀.comap f ≤ W := by
    rw [← hc W hWp P hP]
    exact Ideal.comap_mono (hQ₀le.trans hQP)
  have hWQ : W ≤ Q₀.comap f := hW.2 h1.1 hle
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  exact (hP.2 ⟨hQ₀p, Ideal.map_le_iff_le_comap.mpr hWQ⟩ (hQ₀le.trans hQP)).trans hQ₀le

end MinimalPrimes

theorem isRelevant_comap_map_iff {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) L)) :
    IsRelevant (P.comap (MvPolynomial.map σ)) ↔ IsRelevant P := by
  simp [IsRelevant, Ideal.mem_comap, MvPolynomial.map_X]

theorem fundCycle_apply {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (J W : Ideal (MvPolynomial (Fin n) R)) [Decidable (W ∈ relComps J)] :
    fundCycle J W = if W ∈ relComps J then localMult J W else 0 := by
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  congr

theorem FundCycleBaseChange.proof (h : MinimalPrimeComap.Statement) : FundCycleBaseChange.Statement := by
  classical
  intro K L _ _ _ σ n J
  have hc : ∀ I : Ideal (MvPolynomial (Fin n) K), I.IsPrime →
      ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes, P.comap (MvPolynomial.map σ) = I :=
    fun I hI P hP => h K L σ (Fin n) I hI P hP
  have hrad := RadicalBaseChange.proof
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
      (N := MvPolynomial (Fin n) L) (h := Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin n) K) (R' := L)
        (S' := MvPolynomial (Fin n) L))
  have hsupp : ∀ W ∈ (fundCycle J).support, W ∈ relComps J := by
    intro W hW
    by_contra hn
    exact Finsupp.mem_support_iff.mp hW (by rw [fundCycle_apply, if_neg hn])
  have hone : ∀ W : Ideal (MvPolynomial (Fin n) K), W.IsPrime → ∀ P,
      P ∈ relComps (W.map (MvPolynomial.map σ)) → localMult (W.map (MvPolynomial.map σ)) P = 1 :=
    fun W hW P hP => localMult_eq_one_of_isRadical (hrad K L σ (Fin n) W hW.isRadical) hP.1
  ext P
  rw [Finsupp.finsetSum_apply, fundCycle_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs with hP
  · obtain ⟨hWmin, hPW⟩ := comap_mem_minimalPrimes _ hc hP.1
    have hWrel : P.comap (MvPolynomial.map σ) ∈ relComps J :=
      ⟨hWmin, (isRelevant_comap_map_iff σ P).mpr hP.2⟩
    have hWp : (P.comap (MvPolynomial.map σ)).IsPrime := hWmin.1.1
    have hPp : P.IsPrime := hP.1.1.1
    have : P.LiesOver (P.comap (MvPolynomial.map σ)) := ⟨rfl⟩
    have hmult : localMult (J.map (MvPolynomial.map σ)) P =
        localMult J (P.comap (MvPolynomial.map σ)) :=
      localMult_map_of_flat J _ P (map_eq_maximalIdeal_of_isRadical
        (hrad K L σ (Fin n) _ hWp.isRadical) hPW)
    rw [hmult, Finset.sum_eq_single (P.comap (MvPolynomial.map σ))]
    · rw [fundCycle_apply J, if_pos hWrel,
        fundCycle_apply (Ideal.map (MvPolynomial.map σ) (P.comap (MvPolynomial.map σ))) P,
        if_pos ⟨hPW, hP.2⟩, hone _ hWp P ⟨hPW, hP.2⟩, mul_one]
    · intro W₀ hW₀ hne
      rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W₀) P, if_neg, mul_zero]
      intro hPW₀
      exact hne (hc W₀ (hsupp W₀ hW₀).1.1.1 P hPW₀.1).symm
    · intro hW
      rw [Finsupp.notMem_support_iff.mp hW, zero_mul]
  · refine (Finset.sum_eq_zero fun W hW => ?_).symm
    rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W) P, if_neg, mul_zero]
    intro hPW
    exact hP ⟨mem_minimalPrimes_map _ hc (hsupp W hW).1 hPW.1, hPW.2⟩

end GroundTheory.Heights₂.Heights
end

