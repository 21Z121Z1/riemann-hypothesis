import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0045
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0032
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecQOfRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ArchOfPlacesEmbedding
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeHypersurfaceDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

namespace ConeHypersurfaceDim

theorem finite_of_rel {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    RingHom.Finite ((Ideal.Quotient.mk I).comp (aeval (R := ℂ) L).toRingHom) := by
  classical
  let φ : MvPolynomial (Fin m) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (Ideal.Quotient.mk I).comp (aeval L).toRingHom
  let instA : Algebra (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := φ.toAlgebra
  let instM : Module (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := instA.toModule
  have hsmul : ∀ (s : MvPolynomial (Fin m) ℂ) (p : MvPolynomial (Fin n) ℂ),
      s • Ideal.Quotient.mk I p = Ideal.Quotient.mk I (aeval L s * p) := by
    intro s p
    rw [Algebra.smul_def]
    rfl
  set M := Submodule.span (MvPolynomial (Fin m) ℂ)
    (((Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1))) :
        Set (MvPolynomial (Fin n) ℂ ⧸ I)) with hM
  have hdeg : ∀ N, ∀ β : Fin n →₀ ℕ, (β.sum fun _ e => e) = N →
      Ideal.Quotient.mk I (monomial β 1) ∈ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro β hβ
      have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, q.totalDegree < N →
          Ideal.Quotient.mk I q ∈ M := by
        intro q hq
        rw [q.as_sum, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        have hd' : (d.sum fun _ e => e) < N := lt_of_le_of_lt (le_totalDegree hd) hq
        have h1 := ih _ hd' d rfl
        have : Ideal.Quotient.mk I (monomial d (coeff d q)) =
            (C (coeff d q) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
          rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ h1
      by_cases hsmall : ∀ i, β i < r i
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite β, ?_, ?_⟩)
        · exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (hsmall i)
        · simp
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        set β' := β - Finsupp.single i (r i) with hβ'
        have hβeq : β = β' + Finsupp.single i (r i) := by
          ext i'
          simp only [hβ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases h : i' = i
          · subst h; simp; omega
          · simp [Ne.symm h]
        have hmk : Ideal.Quotient.mk I (monomial β 1) =
            ∑ j, (X j : MvPolynomial (Fin m) ℂ) •
              Ideal.Quotient.mk I (monomial β' 1 * H i j) := by
          have h1 : monomial β (1 : ℂ) = monomial β' 1 * X i ^ r i := by
            rw [hβeq, X_pow_eq_monomial, monomial_mul, one_mul]
          have h2 : Ideal.Quotient.mk I (X i ^ r i) =
              Ideal.Quotient.mk I (∑ j, L j * H i j) :=
            Ideal.Quotient.eq.mpr (hrel i)
          rw [h1, map_mul, h2, ← map_mul, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmul, aeval_X]
          congr 1
          ring
        rw [hmk]
        refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpoly _ ?_)
        have hβsum : (β.sum fun _ e => e) = (β'.sum fun _ e => e) + r i := by
          rw [hβeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        calc (monomial β' 1 * H i j).totalDegree
            ≤ (monomial β' (1 : ℂ)).totalDegree + (H i j).totalDegree := totalDegree_mul _ _
          _ ≤ (β'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hH i j) _
          _ < N := by have := hr i; omega
  have hfin : Module.Finite (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := by
    refine ⟨⟨(Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1)), ?_⟩⟩
    rw [← hM, eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have : Ideal.Quotient.mk I (monomial d (coeff d p)) =
        (C (coeff d p) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
      rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hdeg _ d rfl)
  exact hfin

theorem le_of_add_one_le {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ ((d : ℕ) : WithBot ℕ∞) := by
  induction x with
  | bot => exact bot_le
  | coe x =>
    have h' : x + 1 ≤ ((d : ℕ∞) + 1) := by exact_mod_cast h
    have : x ≤ (d : ℕ∞) := (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    exact_mod_cast this

theorem proof : ConeHypersurfaceDim.Statement := by
  intro n e P Ψ c hP hΨ hc
  classical
  set J := complexFibreIdeal P ⊔ Ideal.span {conePullback Ψ c}
  have hrad : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  rw [hrad]
  choose r hr H hH hrelP using fun i => ConeProjHyperplaneDim.cone_rel hP hΨ i
  have hfin := finite_of_rel J.radical (ConeProjHyperplaneDim.coneForm Ψ) r hr H hH
    (fun i => Ideal.radical_mono le_sup_left (hrelP i))
  set φ : MvPolynomial (Fin (e + 1)) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ J.radical) :=
    (Ideal.Quotient.mk J.radical).comp (aeval (ConeProjHyperplaneDim.coneForm Ψ)).toRingHom with hφ
  have hφc : φ c = 0 := by
    show Ideal.Quotient.mk J.radical (conePullback Ψ c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.le_radical (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hker : ∀ a ∈ Ideal.span {c}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hφc, mul_zero]
  let ψ := Ideal.Quotient.lift (Ideal.span {c}) φ hker
  have hcomp : ψ.comp (Ideal.Quotient.mk (Ideal.span {c})) = φ :=
    RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.lift_mk _ _ _
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (Ideal.span {c}))
    (hcomp ▸ hfin)
  let := ψ.toAlgebra
  have : Module.Finite (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c})
      (MvPolynomial (Fin n) ℂ ⧸ J.radical) := hψ
  have : Algebra.IsIntegral (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c})
      (MvPolynomial (Fin n) ℂ ⧸ J.radical) := Algebra.IsIntegral.of_finite _ _
  have hS : ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hc)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical)
      ≤ ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ ⧸ Ideal.span {c}) :=
        GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
    _ ≤ ((e : ℕ) : WithBot ℕ∞) := le_of_add_one_le (hquot.trans_eq hS)

end ConeHypersurfaceDim

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreDim

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨⟨⟩, i⟩; rfl

def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv

theorem finIdeal_eq_comap {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.comap (blkRingEquiv n) := by
  ext x
  rfl

theorem ringKrullDim_quot_finIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) =
      ringKrullDim (MRing (PBlk n) ⧸ P) := by
  rw [finIdeal_eq_comap]
  refine ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv (P.comap (blkRingEquiv n)) P (blkRingEquiv n) ?_)
  exact (Ideal.map_comap_of_surjective _ (blkRingEquiv n).surjective P).symm

theorem eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hform (by simp; rw [← Nat.cast_succ]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact_mod_cast hform
      have h2 : ((⊤ : ℕ∞) + 1 : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h1
      rw [top_add] at h2
      exact ENat.top_ne_natCast _ h2
    | coe y =>
      have h1 : ((y + 1 : ℕ) : WithBot ℕ∞) = ((d + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hform
      have : y = d := by exact_mod_cast (by exact_mod_cast h1 : y + 1 = d + 1) |> Nat.succ_injective
      subst this; rfl

end GenericFibreDim

open GenericFibreDim in

theorem GenericFibreDim.proof : GenericFibreDim.Statement := by
  intro n d P hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  set P' := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hP'
  have hP'p : P'.IsPrime := by
    rw [hP', finIdeal_eq_comap]
    exact Ideal.comap_isPrime _ _
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Fin n) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP', finIdeal_eq_comap, Ideal.mem_comap] at hm
    have hm' : (blkRingEquiv n) (C m) = C m := by
      simp [blkRingEquiv]
    rw [hm'] at hm
    have : m ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := hm
    rw [show P.comap (C : ℤ →+* MRing (PBlk n)) = ⊥ from hhor, Ideal.mem_bot] at this
    exact this
  obtain ⟨-, -, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P' hchar
  have hgen : genericIdeal P = ReciprocityTheory.AnForm.R.extQ P' := rfl
  rw [hP', ringKrullDim_quot_finIdeal, hdim] at hform
  rw [hgen]
  simp only [Fintype.card_unit] at hform
  exact eq_natCast_of_add_one_eq d _ hform

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionChowHeight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

namespace SectionChowHeight

variable {n : ℕ}

theorem logMean_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (k : ℕ) (z : ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (k + 1))
      (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ) = Real.log ‖z‖ := by
  have h := ObjectsHeight.mahler_eq_chowMean S hS (ObjectsHeight.ofPointMatrix S hS)
    (ObjectsHeight.ofPointMatrix_norm S hS) (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
  rw [mahler_C] at h
  exact h.symm

theorem chowHeight_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (e : ℕ) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0 = 0 := by
  have hsub := ChowHeightCycleEq.chowHt_sub (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1))
    (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0
  simp only [map_C, logMean_C S hS, logMean_C 1 isUnit_one, sub_self, mul_zero,
    Finset.sum_const_zero, zero_div] at hsub
  have hstd : ∀ (σ : ℚ →+* ℂ) (v : Fin n → ℂ),
      ((ArchData.std ℚ n).normAt σ).norm v = IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 v := fun σ v => by
    simp only [ArchData.std]
    rw [ObjectsHeight.std_eq_ofPointMatrix_one, ObjectsHeight.ofPointMatrix_norm]
  have h1 := ObjectsHeight.chowHt_eq_chowHeight (ArchData.std ℚ n) 1 isUnit_one hstd
    (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (δ := 0)
  rw [chowHeightConst ℚ n (e + 1) _ a ha] at h1
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h1 ⊢
  linarith

theorem chowHeight_C_mul_cycle (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e : ℕ} {ι : Type}
    (Z : ι →₀ ℕ) (g : ι → MvPolynomial (Fin (e + 1) × Fin n) ℚ) (d : ι → ℕ)
    (hg : ∀ i ∈ Z.support, g i ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a * ∏ i ∈ Z.support, g i ^ Z i) (∑ i ∈ Z.support, Z i * d i) =
      ∑ i ∈ Z.support, (Z i : ℝ) * IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g i) (d i) := by
  have hMul : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul
  have hne : ∏ i ∈ Z.support, g i ^ Z i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i hi)
  have hadd := ChowHeightCycleEq.additive hMul (fun _ : InfinitePlace ℚ => S) (fun _ => hS)
    (C a) (∏ i ∈ Z.support, g i ^ Z i) 0 (∑ i ∈ Z.support, Z i * d i) (C_ne_zero.mpr ha) hne
  have hcyc := ChowHeightCycleEq.cycle_of_A hMul ℚ n e (fun _ => S) (fun _ => hS) ι Z g d hg
  rw [zero_add] at hadd
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight
  rw [hadd]
  have h0 := chowHeight_C S hS e ha
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h0
  rw [h0, zero_add]
  exact hcyc

end SectionChowHeight

open Classical in

theorem SectionChowHeight.proof (hSec : ChowFormSection.Statement) : SectionChowHeight.Statement := by
  intro n e δ S P f u g d hS hP hf hu hg
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  have hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ)) :=
    hSec ℚ n (e + 1) (ObjectsChow.genericIdeal P) f _
      (VerticalPartGauss.isProjPrime_genericIdeal hP) (VerticalPartGauss.isChowForm_genericIdeal hP hf)
      (VerticalPartGauss.linForm_not_mem_genericIdeal hP hu)
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff,
      RecQOfRecursion.divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => RecQOfRecursion.exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [← ObjectsChow.specFirst_eq, hsf', hδ,
    SectionChowHeight.chowHeight_C_mul_cycle S hS Zh g d hgne hc']
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, RecQOfRecursion.divCycle_apply, if_pos hWd]
    split_ifs <;> simp

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartParAlgebraic.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.IsAlgebraic
        (Algebra.adjoin (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1)))) L

def ChartFreeParAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1))) ∧
        Algebra.IsAlgebraic K L

def ChartPointSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F)
    (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    (∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable K L

section Inhabitants

namespace ChartPointLine

abbrev KL : Type := FractionRing (MvPolynomial (Fin 1 × Fin 2) ℚ)

def uL : Fin 1 × Fin 2 → KL := fun q => algebraMap (MvPolynomial (Fin 1 × Fin 2) ℚ) KL (X q)

def tL : Fin 2 → ℚ := ![0, 1]

def ηL : Fin 2 → KL := ![-(uL (0, 1)) / uL (0, 0), 1]

theorem uL_ne_zero (q : Fin 1 × Fin 2) : uL q ≠ 0 := by
  intro h
  have hinj := IsFractionRing.injective (MvPolynomial (Fin 1 × Fin 2) ℚ) KL
  exact X_ne_zero (R := ℚ) q (hinj (by rw [map_zero]; exact h))

theorem adjoin_ηL : IntermediateField.adjoin KL (Set.range ηL) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  simpa using IntermediateField.algebraMap_mem (IntermediateField.adjoin KL (Set.range ηL)) x

theorem rel_ηL : ∀ i : Fin 1, ∑ m, algebraMap KL KL (uL (i, m)) * ηL m = 0 := by
  intro i
  fin_cases i
  simp only [Fin.sum_univ_two, Algebra.algebraMap_self, RingHom.id_apply, ηL]
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one]
  field_simp [uL_ne_zero (0, 0)]
  ring

theorem chart_ηL : ∑ m, algebraMap ℚ KL (tL m) * ηL m = 1 := by
  simp [Fin.sum_univ_two, tL, ηL]

theorem ηL_one_ne_zero : ηL 1 ≠ 0 := by simp [ηL]

theorem trdeg_ηL (j₀ : Fin 2) (hj₀ : ηL j₀ ≠ 0) :
    Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun m => ηL m * (ηL j₀)⁻¹)) ≤ ((1 : ℕ) : Cardinal) :=
  Vertical.ChartPointTrdeg.full ℚ KL 2 1 ⊥ LineChowForm.D2 LineChowForm.isProjPrime_line
    LineChowForm.isChowForm_line ηL j₀ (fun f hf => by rw [Ideal.mem_bot.1 hf, map_zero]) hj₀

end ChartPointLine

open ChartPointLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

