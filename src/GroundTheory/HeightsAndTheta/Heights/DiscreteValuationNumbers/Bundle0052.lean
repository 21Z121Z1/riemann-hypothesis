import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)

namespace JoinPointModel

section Split

variable {K : Type} {ι : K → Type}

def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

variable (K) (Ω : Type*) [CommRing Ω]

def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)

variable {K} (O : Type*) [CommRing O]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)

end Split

section Cone

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem tgtEquiv_mcMap (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem mem_pointIdeal_join_iff (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]

theorem ringKrullDim_join [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]

end Cone

end JoinPointModel

open JoinPointModel in

theorem JoinPointModel.proof : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace JoinPointNumbers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fieldNum_spec (F : Type) [Field F] {K' : Type} [Fintype K'] (κ : K' → Type) [∀ k, Fintype (κ k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) ⟨_, IntNumIsFieldIntersection.full F K' κ⟩

theorem redIdeal_map_liftVar {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (W.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).map
        (rename (R := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal
  change Ideal.map (MvPolynomial.map (IsLocalRing.residue O))
      (Ideal.map (rename (R := O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom W) =
    Ideal.map (rename (R := IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom
      (Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp [MvPolynomial.map_rename]

theorem monoList_pullDeg {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).map (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit)) := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]

theorem polyNum_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) (F : Type) [Field F]
    (V : Ideal (MRing ι F)) (d : ℕ) (hVd : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V d) {r : ℕ}
    (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F (Sum.elim ι ptIdx))
                              (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum F V bs) V d deg H := by
  have hV' := hV F K ι V d hVd
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have hl := monoList_pullDeg deg μ
  by_cases h : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d
  · have h' : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rw [hl, List.length_map, h]
    rw [dif_pos h', dif_pos h, Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full _ (fieldNum_spec F _) _ d _ hV']
    beta_reduce
    rw [← hN F K ι V d]
    congr 1
    funext j
    simp only [hl, List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  · have h' : ¬ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rwa [hl, List.length_map]
    rw [dif_neg h', dif_neg h]

theorem vEval_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (d : ℕ) {r : ℕ} (deg : Fin r → K → ℤ)
    (H : MvPolynomial (Fin r) ℤ) (Z : Ideal (MRing ι O) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
      (Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) Z) =
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H) Z := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun W hW => ?_
  rw [redIdeal_map_liftVar]
  beta_reduce
  rw [polyNum_join hV hN _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d (hZ W (Finsupp.mem_support_iff.mp hW))
    deg H]

theorem mem_divSupp_of_ne {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (s : MRing ι R) (W : Ideal (MRing ι R)) (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) :
    W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  classical
  by_contra hW
  apply h
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg hW]

theorem intCycle_join (hD : JoinDivCycle.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
        (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) s)) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s)) := by
  rw [hD R K ι P s, Finsupp.mapDomain_mapRange _ _ _ _ fun x y => Nat.cast_add x y]

theorem proof (hI : JoinPointIdeal.Statement) (hD : JoinDivCycle.Statement)
    (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement)
    (hF : VerticalComponentFibre.Statement) : JoinPointNumbers.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hM r deg H
  rw [hI O Ω K ι y]
  refine ⟨fun b f g hdiv => ?_, fun a ha => ?_⟩
  · have hc : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
        ((pointIdeal O y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g) =
        Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g) := by
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc
      rw [intCycle_join hD, intCycle_join hD, Finsupp.mapDomain_sub]
    rw [hc]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have hvert : (C ϖ : MRing ι O) ∈ W :=
      hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
    obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) f W ≠ 0 ∨
        ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) g W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM f bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM g bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  · have hC : (C a : MRing (Sum.elim ι ptIdx) O) =
        rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) (C a) := (rename_C _ _).symm
    rw [hC, intCycle_join hD]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a) W ≠ 0 := by
      intro h0
      apply hW
      simp [h0]
    have hs := mem_divSupp_of_ne _ _ _ h
    have hWp : W.IsPrime := hs.1.1.1
    have hCa : (C a : MRing ι O) ∈ W := hs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnP : (C a : MRing ι O) ∉ pointIdeal O y := by
      intro hmem
      have hmem' : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
      rw [hM.noTorsion, Ideal.mem_bot] at hmem'
      exact ha hmem'
    have hvert : (C ϖ : MRing ι O) ∈ W := by
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      rw [hu, C_mul, C_pow] at hCa
      rcases hWp.mem_or_mem hCa with h1 | h1
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 ((Units.isUnit u).map C)) hWp.ne_top
      · exact hWp.mem_of_pow_mem n h1
    obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM (C a) 0 (isWeightedHomogeneous_C _ _) hnP W
      hs.1 hs.2 hvert
    exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩

end JoinPointNumbers

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorSupportFibre.fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.proof (GenericDimBound.proof MaximalIdealHeightFG.proof)
    GenericDimGe.proof SpecialIdealCorresp.proof SpecialIdealMultiHomog.proof SupSpanMultiHomog.proof
    MinimalPrimeMultiHomog.proof SpecialQuotDim.proof ComponentDim.proof

theorem VerticalDivisorSupportFibre.proof : VerticalDivisorSupportFibre.Statement := by
  classical
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hP1⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  have hV1 := (VerticalDivisorCharacterisation.proof O K ι P ϖ b f g hϖ hP1.multiProj).mp hV
  rw [BundleExamples.ratCyc_eq] at hW
  have hϖW := hV1.vertical W hW
  rw [BundleExamples.redIdeal_eq]

  have key : ∀ (h : MRing ι O) (bh : K → ℕ), IsMultiHomog h bh → h ∉ P → divCycle P h W ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
    intro h bh hh hhP hne
    unfold divCycle at hne
    split_ifs at hne with hc
    · obtain ⟨hmp, hdim⟩ := VerticalComponentFibre.proof VerticalDivisorSupportFibre.fibreVarieties O ϖ hϖ
        K ι P d hP1 h bh hh hhP W hc.1 hc.2 hϖW
      obtain ⟨hpr, hho, hre⟩ := hmp
      exact ⟨⟨hpr, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 hho, hre⟩, hdim⟩
    · exact absurd rfl hne
  obtain ⟨bf, bg, hf, hg, -⟩ := hV1.degrees
  by_cases hfW : divCycle P f W = 0
  · refine key g bg hg hV1.den_not_mem fun hgW => hW ?_
    simp [ratDiv, hfW, hgW]
  · exact key f bf hf hV1.num_not_mem hfW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ResidualNewVarMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem residual_newVar_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof R (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfP hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hres; omega
  rintro (_ | _ | i) hj
  · exact absurd rfl hj
  · exact hY₁G'
  by_contra hYi
  have hrel : liftForm (powMonomial e i) * newVar (some none) -
      liftForm m * newVar (some (some i)) ∈ P' := by
    rw [hP'def, blowUpOf, RingHom.mem_ker]
    simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
    ring
  have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => hYi (hP'G' h)
  by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι R) ∈ P'
  · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
    rw [sub_sub_cancel] at h
    exact (hP'prime.mem_or_mem h).elim hlm hYiP'
  · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
    rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
    simp only [Pi.add_apply] at h1
    have h2 : divCycle P' (newVar (some (some i))) G' = 0 := by
      by_contra h; exact hYi (form_mem_of_divCycle_ne_zero h)
    have h3 := hnonneg (liftForm (powMonomial e i)) G'
    unfold ratDiv at hres; omega

theorem ResidualContractionComponent.proof (hpieces : BlowUpDecomposition.Statement.{u}) :
    ResidualContractionComponent.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', hsc', hsP', -⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have : P.IsPrime := hP.multiProj.isPrime
  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    by_contra h; unfold divCycle at hsG'; rw [dif_neg h] at hsG'; exact lt_irrefl _ hsG'
  have : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hY := residual_newVar_mem e hD.1.num_not_mem hmP hP'G' hresG'
  have hdim' := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) _ (d + 1) hP'
    (liftMDeg c) (liftForm s) hsc' hsP' G' hsG'.ne' hϖG'
  have hdim := ringKrullDim_quotient_le_comap_add_one G' none hY
  refine mem_minimalPrimes_of_ringKrullDim P _ s hsP (d + 1 + 1 + Fintype.card K) hP.dim ?_ ?_
  · refine sup_le (fun p hp => hP'G' ?_) ?_
    · rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hG'supp.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  · rw [Fintype.card_option, show d + 1 + (Fintype.card K + 1) = d + 1 + 1 + Fintype.card K by omega]
      at hdim'
    exact hdim' ▸ hdim

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChart.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      W.IsPrime → IsRelevant W → pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
      ∃ (cl cm : Option (Option K) → ℕ) (l μ u : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog l cl ∧ IsMultiHomog μ cm ∧
        (fun o => (cl o : ℤ) - cm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        μ ∉ W ∧ u ∉ W ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        (k = 0 → l ∉ W) ∧
        (0 < k → ∀ q ∈ pointIdeal O (flagClosurePt y w e φ φ' t k), ∃ n : ℕ,
          u ^ n * q ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

