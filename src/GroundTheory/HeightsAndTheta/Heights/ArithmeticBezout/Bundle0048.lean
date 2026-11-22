import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralComponents
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace ConeIntegralComponents

variable {n : ℕ}

theorem eq_zero_of_pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit (Matrix.transpose h.mat) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
  have h0 : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [Matrix.mulVec_zero]; exact hy)
  ext i
  simpa using congrFun h0 i

theorem coneBall_subset (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsRadical) :
    coneBall h J ⊆ {0} ∪ ⋃ W ∈ (fundCycle J).support, coneBall h W := by
  classical
  rintro y ⟨hy1, hyJ⟩
  have : (RingHom.ker (eval (h.pointOf y))).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le
    (fun q hq => (RingHom.mem_ker).2 (hyJ q hq) : J ≤ RingHom.ker (eval (h.pointOf y)))
  by_cases hrel : IsRelevant W
  · right
    have hmem : W ∈ (fundCycle J).support := by
      rw [Finsupp.mem_support_iff]
      unfold fundCycle
      rw [Finsupp.onFinset_apply, if_pos ⟨hWmin, hrel⟩, localMult_eq_one_of_isRadical hJ hWmin]
      exact one_ne_zero
    exact Set.mem_biUnion hmem ⟨hy1, fun q hq => (RingHom.mem_ker).1 (hWle hq)⟩
  · left
    refine eq_zero_of_pointOf_eq_zero h (funext fun j => ?_)
    have hX : X j ∈ W := by
      by_contra hj
      exact hrel ⟨j, hj⟩
    simpa using (RingHom.mem_ker).1 (hWle hX)

theorem hausdorffMeasure_zero (e : ℕ) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  refine hausdorffMeasure_of_dimH_lt ?_
  rw [dimH_singleton, ENNReal.coe_natCast]
  exact_mod_cast (by omega : 0 < 2 * (e + 1))

theorem setIntegral_finset_biUnion_ae {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (t : Finset ι) {s : ι → Set X} (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ (s i ∩ s j) = 0) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn f (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdis : AEDisjoint μ (s a) (⋃ i ∈ t, s i) := by
      change μ (s a ∩ ⋃ i ∈ t, s i) = 0
      rw [Set.inter_iUnion₂]
      refine (measure_biUnion_null_iff t.countable_toSet).2 fun i hi => ?_
      exact hd a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union₀ hdis (Finset.measurableSet_biUnion t hs').nullMeasurableSet
        (hf a (Finset.mem_insert_self a t)) (integrableOn_finset_iUnion.2 hf'),
      ih hs' (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) hf']

theorem exists_chowForm_components (hEx : ChowFormExists.Statement) (hBC : ChowFormBaseChange.Statement)
    {e : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1)) :
    ∃ g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ,
      ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, IsProjPrime W ∧ IsChowForm W (e + 1) (g W) := by
  have hI := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  obtain ⟨f, hf⟩ := hEx ℚ n (e + 1) _ hI (ObjectsChow.GenericFibreDim.proof n (e + 1) P hP)
  obtain ⟨hproj, c, -, g, hg, -⟩ := hBC ℚ n (e + 1) _ f (Rat.castHom ℂ) hI hf
  rw [← ComplexFibreCycle.complexFibreIdeal_eq_map] at hproj hg
  exact ⟨g, fun W hW => ⟨hproj W hW, hg W hW⟩⟩

end ConeIntegralComponents

open ConeIntegralComponents in

theorem ConeIntegralComponents.proof (hEx : ChowFormExists.Statement)
    (hBC : ChowFormBaseChange.Statement) (hDim : ConeDimOfChowForm.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hMeet : ConeMeetNull.Statement) :
    ConeIntegralComponents.Statement := by
  intro n e h P u hP hu
  classical
  set S := (fundCycle (complexFibreIdeal P)).support with hS
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ
  obtain ⟨g, hg⟩ := exists_chowForm_components hEx hBC hP
  have hdimW : ∀ W ∈ S, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
    fun W hW => (hDim ℂ n (e + 1) W (g W) (hg W hW).1 (hg W hW).2).le
  have hJW : ∀ W ∈ S, complexFibreIdeal P ≤ W :=
    fun W hW => (mem_minimalPrimes_of_mem_fundCycle_support hW).1.2
  have hae : coneBall h (complexFibreIdeal P) =ᵐ[μ] ⋃ W ∈ S, coneBall h W := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (hausdorffMeasure_zero e), ?_⟩
    · rcases coneBall_subset h (complexFibreIdeal_isRadical hP) hy.1 with h0 | h1
      · exact h0
      · exact absurd h1 hy.2
    · have hsub : (⋃ W ∈ S, coneBall h W) ⊆ coneBall h (complexFibreIdeal P) :=
        Set.iUnion₂_subset fun W hW y (hy : y ∈ coneBall h W) =>
          (⟨hy.1, fun q hq => hy.2 q (hJW W hW hq)⟩ : y ∈ coneBall h (complexFibreIdeal P))
      rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  have key := setIntegral_finset_biUnion_ae (μ := μ) (f := fun y => fsLog h u (h.pointOf y)) S
    (fun W _ => measurableSet_coneBall h W)
    (fun W hW W' hW' hne => hMeet n e h W W' (hg W hW).1.isPrime (hg W' hW').1.isPrime hne
      (hdimW W hW) (hdimW W' hW'))
    (fun W hW => hInt n e h W (g W) u (hg W hW).1 (hg W hW).2 (hu W hW))
  unfold coneIntegral
  rw [← Finset.sum_div]
  congr 1
  change ∑ W ∈ S, ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂μ =
    ∫ y in coneBall h (complexFibreIdeal P), fsLog h u (h.pointOf y) ∂μ
  rw [setIntegral_congr_set hae, key]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecDegreeGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecDegreeGe

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}

theorem eval_specRest (ψ : k →+* R) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) (v : Fin n → R) :
    eval v (Vertical.specRest ψ f y) =
      eval₂ ψ (fun ij => Fin.cases (motive := fun _ => R) (v ij.2)
        (fun i => y (.inl (i, ij.2))) ij.1) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Vertical.specRest]
  | add p q hp hq => simp only [Vertical.specRest] at hp hq ⊢; simp [hp, hq]
  | mul_X p ij hp =>
    simp only [Vertical.specRest] at hp ⊢
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [hp]
    | succ i => simp [hp]

theorem map_eval_specRest (ψ : k →+* R) (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) :
    φ (eval (fun j => y (.inr j)) (Vertical.specRest ψ f y)) =
      eval (fun j => φ (y (.inr j))) (Vertical.specRest (φ.comp ψ) f (φ ∘ y)) := by
  rw [eval_specRest, eval_specRest, MvPolynomial.eval₂_comp_left]
  congr 1
  funext ⟨i, j⟩
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SecDegreeGe

open SecDegreeGe in

theorem SecDegreeGe.proof (hFin : SecFiniteUnit.Statement) (hSpec : SecRankSpecialize.Statement) :
    SecDegreeGe.Statement := by
  intro k E _ _ _ _ n e δ Q g y hQ hg hδ hne
  refine ⟨hFin k E n e δ Q g y hg hδ (isUnit_iff_ne_zero.2 hne), ?_⟩

  let 𝔭 : Ideal (MvPolynomial (Vertical.Par e n) E) := RingHom.ker (eval y)
  have : 𝔭.IsPrime := RingHom.ker_isPrime _
  let R := Localization.AtPrime 𝔭
  have : IsDomain R :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  let K := FractionRing (MvPolynomial (Vertical.Par e n) E)
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Vertical.Par e n) E) R K,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) K]
  let π : R →+* E := IsLocalization.lift (M := 𝔭.primeCompl) (g := eval y)
    (fun s => isUnit_iff_ne_zero.2 fun h => s.2 (RingHom.mem_ker.2 h))
  have hπ : ∀ p, π (algebraMap (MvPolynomial (Vertical.Par e n) E) R p) = eval y p := fun p => IsLocalization.lift_eq _ _
  let _ : Algebra R E := π.toAlgebra
  let Y : Vertical.Par e n → R := fun p => algebraMap (MvPolynomial (Vertical.Par e n) E) R (X p)
  have hπY : algebraMap R E ∘ Y = y := funext fun p => by
    simp [RingHom.algebraMap_toAlgebra, Y, hπ]
  have hπk : (algebraMap R E).comp (algebraMap k R) = algebraMap k E := by
    ext a
    show π (algebraMap k R a) = algebraMap k E a
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Vertical.Par e n) E) R, hπ,
      MvPolynomial.algebraMap_apply, eval_C]
  have hsurj : Function.Surjective (algebraMap R E) := fun a =>
    ⟨algebraMap (MvPolynomial (Vertical.Par e n) E) R (C a), by simp [RingHom.algebraMap_toAlgebra, hπ]⟩

  have hunit : IsUnit (eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y)) := by
    have h1 := map_eval_specRest (algebraMap k R) (algebraMap R E) g Y
    rw [hπk, hπY] at h1
    have hker : RingHom.ker (algebraMap R E) = IsLocalRing.maximalIdeal R := by
      haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
      exact IsLocalRing.eq_maximalIdeal this
    by_contra hu
    have hm : eval (fun j => Y (.inr j)) (Vertical.specRest (algebraMap k R) g Y) ∈
        RingHom.ker (algebraMap R E) := by
      rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    have hv : (fun j => algebraMap R E (Y (.inr j))) = fun j => y (.inr j) :=
      funext fun j => congrFun hπY (.inr j)
    rw [RingHom.mem_ker, h1, hv] at hm
    exact hne hm
  have hB := hFin k R n e δ Q g Y hg hδ hunit
  have hle := hSpec R K E n e (Q.map (MvPolynomial.map (algebraMap k R))) Y hsurj hB
  have hmapK : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R K)) =
      Q.map (MvPolynomial.map (algebraMap k K)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_) <;>
      simp [← IsScalarTower.algebraMap_apply]
  have hmapE : (Q.map (MvPolynomial.map (algebraMap k R))).map (MvPolynomial.map (algebraMap R E)) =
      Q.map (MvPolynomial.map (algebraMap k E)) := by
    rw [Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, map_C]
      exact congrArg C (RingHom.congr_fun hπk a)
    · simp
  rw [hmapK, hmapE, hπY] at hle

  have hind : AlgebraicIndependent k (algebraMap R K ∘ Y) := by
    have h0 : AlgebraicIndependent k (X : Vertical.Par e n → MvPolynomial (Vertical.Par e n) E) :=
      (MvPolynomial.algebraicIndependent_X _ _).restrictScalars
        (FaithfulSMul.algebraMap_injective k E)
    let f : MvPolynomial (Vertical.Par e n) E →ₐ[k] K :=
      (IsScalarTower.toAlgHom k R K).comp
        (IsScalarTower.toAlgHom k (MvPolynomial (Vertical.Par e n) E) R)
    have hinj : Function.Injective f :=
      (IsFractionRing.injective R K).comp
        (IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors 𝔭))
    have h1 : AlgebraicIndependent k (f ∘ X) := h0.map' hinj
    have heq : f ∘ X = algebraMap R K ∘ Y := funext fun p => rfl
    rwa [heq] at h1
  have hgen := Vertical.ChowSecDegree.proof
    (Vertical.ChowNormForm.proof
      (Vertical.ChowNormFormGeneric.proof Vertical.SecAlgFinite.full Vertical.GenSecDomain.full
        Vertical.GenSecSeparable.full Vertical.ChowSecDvd.full Vertical.NormFormIrreducible.full
        Vertical.GenChowIrreducible.full Vertical.NormFormDvd.full)
      Vertical.SecAlgFieldChange.full)
    Vertical.ChowFormHomog.full Vertical.NormFormEval.full k K n e Q g (algebraMap R K ∘ Y) hind hQ hg
  have hdeg : δ = chowDegree Q (e + 1) :=
    Vertical.chowForm_degree_unique (Nat.succ_pos e) hg hg hδ
      (Vertical.ChowFormHomog.full k n (e + 1) Q g hg)
  rw [hgen] at hle
  exact hdeg ▸ hle

end

end GroundTheory.Heights₂.Heights
end

