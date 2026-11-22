import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeClosedPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial Vertical Vertical.NormFormIrreducible

theorem aeval_smul_of_isHomogeneous {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hg (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  rw [aeval_monomial, aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ChowDegreeClosedPoint.proof (hField : ClosedPointChartField.Statement)
    (hCone : ClosedPointConeCoord.Statement) : ChowDegreeClosedPoint.Statement := by
  classical
  intro F _ _ n I i hI hdim hXi
  obtain ⟨hfield, hfin⟩ := hField F n I i hI hdim hXi
  set J : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {X i - 1} with hJ
  let _ : Field (MvPolynomial (Fin n) F ⧸ J) := hfield.toField
  let L := MvPolynomial (Fin n) F ⧸ J
  have _ : FiniteDimensional F L := hfin
  have _ : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  let K := AlgebraicClosure F
  let ξ : Fin n → L := fun j => Ideal.Quotient.mk J (X j)
  have hξ : ∀ g : MvPolynomial (Fin n) F, aeval ξ g = Ideal.Quotient.mk J g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp; rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X]
  have hξi : ξ i = 1 := by
    have : X i - 1 ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  set t : Fin n → F := Pi.single i 1 with ht_def
  have ht : ∑ j, algebraMap F L (t j) * ξ j = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [ht_def, hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [ht_def, hξi]
  have hgen : Algebra.adjoin F (Set.range ξ) = ⊤ := by
    have hr : Set.range ξ = Ideal.Quotient.mkₐ F J '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [hr, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective F J

  obtain ⟨f, hf⟩ := chowFormExists F n 1 I hI hdim
  have hhom : IsMultiHomog (chowDegree I 1) f := chowFormHomog F n 1 I f hf
  have hfH : f.IsHomogeneous (chowDegree I 1) := by
    intro m hm
    have h := congrFun (hhom hm) 0
    rw [← h, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq0 : q.1 = 0 := Subsingleton.elim _ _
    simp [groupWeight, hq0]
  let ι : Fin n → Fin 1 × Fin n := fun j => (0, j)
  have hsnd : ∀ p : MvPolynomial (Fin 1 × Fin n) F, rename ι (rename Prod.snd p) = p := by
    intro p
    rw [rename_rename]
    convert rename_id_apply p
    funext q
    exact Prod.ext (Subsingleton.elim _ _) rfl
  set f₀ := rename Prod.snd f with hf₀
  set N : MvPolynomial (Fin n) F := normForm (R := F) L ξ with hN
  have hprod : N.map (algebraMap F K) = ∏ σ : L →ₐ[F] K, embForm σ ξ := normForm_map_eq_prod ξ

  have hdvd1 : f ∣ rename ι N := by
    refine (hf.2 _).1 fun u hu => ?_
    obtain ⟨y, hy0, hyI, hyu⟩ := hu
    have hyi : y i ≠ 0 := hCone F n I i hI hdim hXi K y hy0 hyI
    let ys : Fin n → K := fun j => (y i)⁻¹ * y j
    have hker : J ≤ RingHom.ker (aeval (R := F) ys).toRingHom := by
      refine sup_le (fun g hg => ?_) ((Ideal.span_le).mpr ?_)
      · rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          ← sum_homogeneousComponent g, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g),
          hyI _ (hI.isHomog g hg d), mul_zero]
      · rintro _ rfl
        simp [ys, hyi]
    let σ : L →ₐ[F] K := Ideal.Quotient.liftₐ J (aeval ys) fun g hg => hker hg
    have hσ : ∀ j, σ (ξ j) = ys j := fun j =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp [ys])
    rw [aeval_rename, aeval_def, ← eval_map, hprod, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
    rw [eval_embForm]
    simp only [hσ, ys, Function.comp_apply, ι]
    have := hyu 0
    calc ∑ j, u (0, j) * ((y i)⁻¹ * y j) = (y i)⁻¹ * ∑ j, u (0, j) * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]

  have hdvd2 : ∀ σ : L →ₐ[F] K, embForm σ ξ ∣ f₀.map (algebraMap F K) := by
    intro σ
    have hprime : Prime (embForm σ ξ) := (irreducible_embForm σ ht).prime
    have hspan : (Ideal.span {embForm σ ξ}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    rw [← Ideal.mem_span_singleton, ← hspan.radical,
      ← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
    intro u hu
    have hu0 : ∑ j, u j * σ (ξ j) = 0 := by
      have := hu _ (Ideal.mem_span_singleton_self _)
      rwa [aeval_eq_eval, eval_embForm] at this
    rw [aeval_eq_eval, eval_map, ← aeval_def, hf₀, aeval_rename]
    refine (hf.2 f).2 dvd_rfl _ ⟨fun j => σ (ξ j), fun h => ?_, fun g hg => ?_, fun k => ?_⟩
    · have := congrFun h i
      simp [hξi] at this
    · rw [← comp_aeval_apply, hξ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg),
        map_zero]
    · rw [Subsingleton.elim k 0]
      simpa using hu0
  have hdvd3 : N.map (algebraMap F K) ∣ f₀.map (algebraMap F K) := by
    rw [hprod]; exact prod_embForm_dvd hgen ht hdvd2
  have hdvd4 : f₀ ∣ N := by
    have := map_dvd (rename Prod.snd) hdvd1
    rwa [rename_rename, show Prod.snd ∘ ι = id from rfl, rename_id_apply] at this

  have hf0 : f₀ ≠ 0 := fun h => hf.1 (by rw [← hsnd f, ← hf₀, h, map_zero])
  have hmap0 : f₀.map (algebraMap F K) ≠ 0 :=
    fun h => hf0 (map_injective _ (algebraMap F K).injective (by rw [h, map_zero]))
  obtain ⟨h, hh⟩ := hdvd4
  obtain ⟨q, hq⟩ := hdvd3
  have hq1 : q * h.map (algebraMap F K) = 1 := by
    apply mul_left_cancel₀ hmap0
    calc f₀.map (algebraMap F K) * (q * h.map (algebraMap F K))
        = (f₀.map (algebraMap F K) * h.map (algebraMap F K)) * q := by ring
      _ = N.map (algebraMap F K) * q := by rw [hh, map_mul]
      _ = f₀.map (algebraMap F K) * 1 := by rw [← hq, mul_one]
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp (isUnit_iff_exists_inv.mpr ⟨_, hq1⟩)
  have hlin : ∀ σ : L →ₐ[F] K, (embForm σ ξ).IsHomogeneous 1 := fun σ =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X K j).mul (isHomogeneous_C _ (σ (ξ j)))
  have h1 : (f₀.map (algebraMap F K)).IsHomogeneous (∑ _σ : L →ₐ[F] K, 1 + 0) := by
    rw [hq, hprod, hc]
    exact (IsHomogeneous.prod _ _ _ fun σ _ => hlin σ).mul (isHomogeneous_C _ c)
  have h2 : (f₀.map (algebraMap F K)).IsHomogeneous (chowDegree I 1) :=
    hfH.rename_isHomogeneous.map _
  rw [h2.inj_right h1 hmap0]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, add_zero]
  exact AlgHom.card F L K

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous' {R : Type*} [CommSemiring R] {k n : ℕ} (u : Fin n → R)
    (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X R (groupWeight k n) (i', j)

theorem isMultiHomog_specFirst {R : Type*} [CommSemiring R] {k n δ : ℕ}
    {f : MvPolynomial (Fin (k + 1) × Fin n) R} (u : Fin n → R) (hf : IsMultiHomog δ f) :
    IsMultiHomog δ (specFirst f u) := by
  unfold IsMultiHomog specFirst
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous' u ij).pow _

theorem ChowDegreeSection.proof (h : ChowFormSectionPerfect.Statement) : ChowDegreeSection.Statement := by
  intro F _ _ n e I u hI hdim hu
  obtain ⟨f, hf⟩ := chowFormExists F n (e + 2) I hI hdim
  have hfδ : IsMultiHomog (chowDegree I (e + 2)) f := Vertical.ChowFormHomog.proof F n (e + 2) I f hf
  obtain ⟨c, hc, g, hg, hfu⟩ := h F n (e + 1) I f u hI hf hu
  have hsδ : IsMultiHomog (chowDegree I (e + 2)) (specFirst f u) := isMultiHomog_specFirst u hfδ
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => ?_)
    exact pow_ne_zero _ (hg W hW).1
  rw [hfu] at hsδ
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hsδ hne
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  congr 1
  exact Vertical.chowForm_degree_unique (Nat.succ_pos e) (hg W hW) (hg W hW) (hδW W hW)
    (Vertical.ChowFormHomog.proof F n (e + 1) W (g W) (hg W hW))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExistsRat
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem ChowFormExistsRat.proof (hA : ObjectsChow.ChowFormToComplexChowForm.Statement)
    (hD : ObjectsChow.GenericFibreDim.Statement) : ChowFormExistsRat.Statement := by
  intro n e P hP
  have hQ := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  obtain ⟨g, hg⟩ := ObjectsChow.chowFormExists ℚ n (e + 1) (ObjectsChow.genericIdeal P) hQ
    (hD n (e + 1) P hP)
  obtain ⟨δ, -, hδ⟩ := ChowFormMultiHomog.full ℚ n (e + 1) (ObjectsChow.genericIdeal P) g hQ hg
  exact ⟨δ, g, hA n e δ P g hP hg hδ⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointChartField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem ClosedPointChartField.proof : ClosedPointChartField.Statement := by
  intro F _ n I i hI hdim hXi
  have := hI.isPrime
  set ξ := genPt I
  have hξ : ξ i ≠ 0 := fun h =>
    hXi ((ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I (X i)).1 (by simpa using h))
  set g : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I) :=
    aeval fun m => ξ m * (ξ i)⁻¹ with hg

  have hhom : ∀ (h : MvPolynomial (Fin n) F) (d : ℕ), h.IsHomogeneous d →
      ChartZeroTrdeg.homogAt h i d = h := by
    intro h d hh
    conv_rhs => rw [h.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : (α.sum fun _ e => e) = d := by
      have := hh (mem_support_iff.mp hα)
      simpa [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using this
    rw [hα', Nat.sub_self, pow_zero, mul_one]

  have hker : RingHom.ker g = I ⊔ Ideal.span {X i - 1} := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      have hH : ChartZeroTrdeg.homogAt p i p.totalDegree ∈ I := by
        rw [← ChartZeroTrdeg.aeval_genPt_eq_zero_iff',
          ChartZeroTrdeg.aeval_homogAt p i _ le_rfl ξ hξ]
        rw [← hg, hp, mul_zero]
      have hd : p - ChartZeroTrdeg.homogAt p i p.totalDegree ∈ Ideal.span {X i - 1} := by
        rw [← Ideal.Quotient.eq]
        have h1 : Ideal.Quotient.mk (Ideal.span {X i - 1}) (X i : MvPolynomial (Fin n) F) = 1 := by
          rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
          exact Ideal.subset_span rfl
        conv_lhs => rw [p.as_sum]
        simp only [ChartZeroTrdeg.homogAt, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      have := (I ⊔ Ideal.span {X i - 1}).add_mem (Ideal.mem_sup_left hH) (Ideal.mem_sup_right hd)
      simpa using this
    · refine sup_le ?_ ?_
      · intro f hf
        rw [RingHom.mem_ker, ← sum_homogeneousComponent f, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hh : (homogeneousComponent d f).IsHomogeneous d :=
          homogeneousComponent_isHomogeneous d f
        have h0 : aeval ξ (homogeneousComponent d f) = 0 :=
          (ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I _).2 (hI.isHomog f hf d)
        by_cases hz : homogeneousComponent d f = 0
        · rw [hz, map_zero]
        have := ChartZeroTrdeg.aeval_homogAt (homogeneousComponent d f) i d
          (hh.totalDegree hz).le ξ hξ
        rw [hhom _ d hh, h0] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hξ)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        change g (X i - 1) = 0
        simp [hg, hξ]

  let e : (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ≃ₐ[F] g.range :=
    (Ideal.quotientEquivAlgOfEq F (hker.symm.trans (AlgHom.ker_rangeRestrict g).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective g.rangeRestrict_surjective)
  have htr := GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof F n 0 I i hI (by simpa using hdim) hXi
  rw [Algebra.adjoin_range_eq_range_aeval] at htr
  have halg : Algebra.IsAlgebraic F g.range := trdeg_eq_zero_iff.1 (by simpa using htr)
  have hfield : IsField g.range := isField_of_isIntegral_of_isField' (Field.toIsField F)
  have : Algebra.FiniteType F g.range :=
    Algebra.FiniteType.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have : Module.Finite F g.range := Algebra.IsIntegral.finite
  exact ⟨MulEquiv.isField hfield e.toMulEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

def ConeProjHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {z : EuclideanSpace ℂ (Fin n) |
          (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
          Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetAreaLintegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal

def ConeSheetAreaLintegral.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → Measurable F →
      AEMeasurable (fun x : Fin e → ℂ => ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
          F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) *
              gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)) ∧
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x : Fin e → ℂ, ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
            F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
              ENNReal.ofReal (‖t‖ ^ (2 * e) *
                gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetCover
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

def ConeSheetCover.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ x ∈ U k, fibre P Ψ x = Set.range (fun j => segre (s k j x)) ∧
          Function.Injective (fun j => segre (s k j x)) ∧
          ∀ j, IsSheet P Ψ x (segre (s k j x)) (s k j) ∧
            ∀ γ, IsSheet P Ψ x (segre (s k j x)) γ → γ =ᶠ[𝓝 x] s k j) ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {z : EuclideanSpace ℂ (Fin n) |
            (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
            Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧
            (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
                Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetParam
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

def ConeSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → (Σ k, PBlk n k) → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ x ∈ U k, fibre P Ψ x = Set.range (fun j => segre (s k j x)) ∧
          Function.Injective (fun j => segre (s k j x)) ∧
          ∀ j, IsSheet P Ψ x (segre (s k j x)) (s k j) ∧
            ∀ γ, IsSheet P Ψ x (segre (s k j x)) γ → γ =ᶠ[𝓝 x] s k j) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          (coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0

end GroundTheory.Heights₂.Heights
end
end

