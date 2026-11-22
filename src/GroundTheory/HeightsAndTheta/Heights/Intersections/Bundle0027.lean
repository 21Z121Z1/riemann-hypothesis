import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjBundleDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → LinearIndependent (FnField P) B →
    ringKrullDim (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) = ringKrullDim (MRing ι ⧸ P) + (n : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjBundleFibreLine.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin 2) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m 2 → IsKerBasis P c B →
    ∃ G : GenFibre (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B),
      ∃ S : Set (MRingOver G.Φ (fibreIdx (PBlk ι N1) (Sum.inl : K → K ⊕ Unit))),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal Sum.inl G = Ideal.span S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjBundleMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m n → IsKerBasis P c B →
    IsMultiHomogIdeal (projBundleIdeal P B)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsAbsMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    AEStronglyMeasurable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w|)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsMonoSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E D : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → (∀ j, IsSemiPosHerm (M j)) →
    IsSmoothHerm E → IsSectionOn Q E t → IsSmoothHerm D → D.a = 0 →
    (∀ z ∈ mcPts Q, eval z (map (Int.castRingHom ℂ) t) ≠ 0 → logNorm E t z ≤ Real.log (D.h z)) →
    ptsIntegral Q (pot M) (logNorm E t) ≤ ptsIntegral Q (pot M) (fun z => Real.log (D.h z))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsRegLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsRegLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm E → t ∉ Q →
    Filter.Tendsto (fun ε => ptsIntegral Q (pot M) (fun z => Real.log ((regLine E t ht ε).h z)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ptsIntegral Q (pot M) (logNorm E t)))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StRegCurvBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def RegCurvBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsSmoothHerm E → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      IsSemiPosHerm ((E.tensor (regLine E t ht ε)).tensor
        (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (C : ℤ))))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    I K' ι' P' (d + r) (Fin.append L' N) =
      (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFStep.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFAt I r → PFAt I (r + 1)

section Inhabitants

abbrev PointLineBlocks : Unit ⊕ Unit → Type := Sum.elim (PBlk 1) (PBlk 2)

theorem imageZ_inlV_bot :
    imageZ (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) (⊥ : Ideal (MRing PointLineBlocks)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ isBlockMap_inl.2.1)

theorem aeval_algebraMap_X_eq {σ : Type} {Φ : Type} [CommRing Φ] [Algebra (MvPolynomial σ ℤ) Φ]
    (f : MvPolynomial σ ℤ) :
    aeval (R := ℤ) (fun p => algebraMap (MvPolynomial σ ℤ) Φ (X p)) f = algebraMap (MvPolynomial σ ℤ) Φ f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ Φ) a]
    exact (eq_intCast ((algebraMap (MvPolynomial σ ℤ) Φ).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, hp, aeval_X]

abbrev lineAlgBase : Algebra (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
  ((algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))).comp
    (rename (inlV (ι := PBlk 1) (ι₂ := PBlk 2))).toRingHom).toAlgebra

theorem lineAlgBase_injective :
    Function.Injective (@algebraMap (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) _ _ lineAlgBase) :=
  (IsFractionRing.injective (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))).comp
    (rename_injective _ isBlockMap_inl.2.1)

abbrev lineAlg : Algebra (FractionRing (MRing (PBlk 1))) (FractionRing (MRing PointLineBlocks)) :=
  letI := lineAlgBase
  haveI : FaithfulSMul (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr lineAlgBase_injective
  FractionRing.liftAlgebra _ _

theorem lineAlg_algebraMap (f : MRing (PBlk 1)) :
    @algebraMap _ _ _ _ lineAlg (algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) f) =
      algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))
        (rename (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) f) := by
  let := lineAlgBase
  have : FaithfulSMul (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr lineAlgBase_injective
  exact IsFractionRing.lift_algebraMap lineAlgBase_injective f

def genFibreLine : GenFibre (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) (⊥ : Ideal (MRing PointLineBlocks)) where
  Φ := FractionRing (MRing (PBlk 1))
  Φ' := FractionRing (MRing PointLineBlocks)
  alg := lineAlg
  x p := algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) (X p)
  x' q := algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks)) (X q)
  ker_x := by
    rw [imageZ_inlV_bot]
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X_eq f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing (PBlk 1)) c
    refine ⟨a, b, ?_, ?_⟩
    · convert IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (K := FractionRing (MRing (PBlk 1))) hb using 2
      exact aeval_algebraMap_X_eq b
    · exact (congrArg₂ (· / ·) (aeval_algebraMap_X_eq a) (aeval_algebraMap_X_eq b)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks)))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X_eq f
  compat p := by
    rw [lineAlg_algebraMap, rename_X]

def fibreLine : HermLine PointLineBlocks := HermLine.sqMetric (Sum.elim (fun _ => 0) fun _ => 1)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (funField P) where
  carrier := {x | ∀ W, IsClosedPt W → P ≤ W → (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P W}
  mul_mem' ha hb W h1 h2 := mul_mem (ha W h1 h2) (hb W h1 h2)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb W h1 h2 := add_mem (ha W h1 h2) (hb W h1 h2)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha W h1 h2 := neg_mem (ha W h1 h2)

def RegularityOrder.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → Module.Free ℤ (regRing P) ∧ Module.Finite ℤ (regRing P) ∧
      ∀ hF : IsField (funField P), letI := hF.toField; ∀ [NumberField (funField P)],
        Module.finrank ℤ (regRing P) = Module.finrank ℚ (funField P)

end

end GroundTheory.Heights₂.Heights.Inter
end

