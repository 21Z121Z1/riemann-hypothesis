import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
theorem CechFlat.full : CechFlat.Statement.{u, v} := CechFlat.proof
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
theorem FiniteTwists.full : FiniteTwists.Statement.{u, w} := FiniteTwists.proof TwistFinite.full
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
theorem HilbertPoint.full : HilbertPoint.Statement.{u, w} := HilbertPoint.proof
theorem PrimeFiltration.Exists.full : PrimeFiltration.Exists.Statement.{u, v, w} :=
  PrimeFiltration.Exists.proof
theorem PrimeFiltration.full : PrimeFiltration.Statement.{u, v, w} :=
  PrimeFiltration.proof PrimeFiltration.Exists.full
theorem PrimeFiltration.Irrelevant.full : PrimeFiltration.Irrelevant.Statement.{u} :=
  PrimeFiltration.Irrelevant.proof
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof
theorem Restriction.full : Restriction.Statement.{u, w} := Restriction.proof

theorem VeryAmpleTwistGenerated.full : VeryAmpleTwistGenerated.Statement.{u, w} :=
  VeryAmpleTwistGenerated.proof
theorem AmpleCover.full : AmpleCover.Statement.{u, w} := AmpleCover.proof
theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

theorem AmpleTwistLocal.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    AmpleTwistLocal.Statement.{u, w} :=
  AmpleTwistLocal.proof hA

theorem GeneratedAmple.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    GeneratedAmple.Statement.{u, w} :=
  GeneratedAmple.proof AmpleCover.full (AmpleTwistLocal.assembled hA)

theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

theorem FiniteSections.assembled (hT : TildeTail.Statement.{u, w}) : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.full hT

theorem Domination.assembled (hT : TildeTail.Statement.{w, w}) : Domination.Statement.{u, w} :=
  Domination.proof (FiniteSections.assembled hT)

theorem SurjectiveClosed.assembled (hFam : IdealTwistFamily.Statement.{u, w})
    (hVan : TildeVanish.Statement.{u, w, w}) : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.full hFam hVan

theorem ConservationOfDegree.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} :=
  ConservationOfDegree.proof hA hB

theorem NefGeneric.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : NefGeneric.Statement.{u, w} :=
  NefGeneric.proof (ConservationOfDegree.assembled hA hB)

theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMulMemAdjoinOfIsLocalization
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

theorem exists_mul_mem_adjoin_of_isLocalization {S : Type*} [CommRing S] {S' : Type*} [CommRing S'] [Algebra S S']
    {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra S' Ω] [IsScalarTower S S' Ω] (M : Submonoid S)
    [IsLocalization M S'] (s : Set Ω) {w : Ω} (hw : w ∈ Algebra.adjoin S' s) :
    ∃ m ∈ M, algebraMap S Ω m * w ∈ Algebra.adjoin S s := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, M.one_mem, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M r
    refine ⟨m, m.2, ?_⟩
    have e : algebraMap S Ω m * algebraMap S' Ω (IsLocalization.mk' S' a m) = algebraMap S Ω a := by
      rw [IsScalarTower.algebraMap_apply S S' Ω, IsScalarTower.algebraMap_apply S S' Ω a, ← map_mul,
        IsLocalization.mk'_spec']
    rw [e]
    exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
    have e : algebraMap S Ω (m₁ * m₂) * (x + y) =
        algebraMap S Ω m₂ * (algebraMap S Ω m₁ * x) + algebraMap S Ω m₁ * (algebraMap S Ω m₂ * y) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) h₁) (mul_mem (Subalgebra.algebraMap_mem _ _) h₂)
  | mul x y _ _ hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
    have e : algebraMap S Ω (m₁ * m₂) * (x * y) = (algebraMap S Ω m₁ * x) * (algebraMap S Ω m₂ * y) := by
      rw [map_mul]; ring
    rw [e]
    exact mul_mem h₁ h₂

theorem SecOverLocalization.proof : SecOverLocalization.Statement := by
  intro S _ K _ ι _ Ω _ _ y β S' _ _ _ _ M _
  classical
  apply le_antisymm
  · intro z hz
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule] at hz

    have key : ∀ c : ∀ k, ι k, ∃ m ∈ M, ∀ _ : ∀ k, y ⟨k, c k⟩ ≠ 0,
        algebraMap S Ω m * (z * ∏ k, y ⟨k, c k⟩ ^ (-β k)) ∈ chartRingOver S y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      · obtain ⟨m, hm, h⟩ := exists_mul_mem_adjoin_of_isLocalization (S' := S') M _ (hz c hc)
        exact ⟨m, hm, fun _ => h⟩
      · exact ⟨1, M.one_mem, fun h => absurd h hc⟩
    choose m hm hmz using key
    set m₀ := ∏ c, m c with hm₀
    have hm₀M : m₀ ∈ M := prod_mem fun c _ => hm c

    have hmem : algebraMap S Ω m₀ * z ∈ secOver S y β := by
      simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
        Subalgebra.mem_toSubmodule]
      intro c hc
      have e : algebraMap S Ω m₀ * z * ∏ k, y ⟨k, c k⟩ ^ (-β k) =
          algebraMap S Ω (∏ c' ∈ Finset.univ.erase c, m c') *
            (algebraMap S Ω (m c) * (z * ∏ k, y ⟨k, c k⟩ ^ (-β k))) := by
        rw [hm₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), map_mul]; ring
      rw [e]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hmz c hc)

    obtain ⟨u, hu⟩ := IsLocalization.map_units S' (⟨m₀, hm₀M⟩ : M)
    have hz' : z = (↑u⁻¹ : S') • (algebraMap S Ω m₀ * z) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S S' Ω, ← mul_assoc, ← map_mul]
      have : (↑u⁻¹ : S') * algebraMap S S' m₀ = 1 := by
        rw [show algebraMap S S' m₀ = (u : S') from hu.symm, Units.inv_mul]
      rw [this, map_one, one_mul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · refine Submodule.span_le.mpr fun z hz => ?_
    simp only [SetLike.mem_coe, secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule] at hz ⊢
    intro c hc
    have hle : chartRingOver S y c ≤ (chartRingOver S' y c).restrictScalars S :=
      Algebra.adjoin_le fun x hx => (Algebra.subset_adjoin hx : x ∈ Algebra.adjoin S' _)
    exact hle (hz c hc)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Hyps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

def QuotSecsBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (J : Ideal (MRingOver S ι))
    (hJ : mIdealOver S y ≤ J),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → IsMultiHomogIdeal J → ∀ β : K → ℤ,
    ∃ (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (J' : Ideal (Kleiman.Poly S N)),
      (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') ∧
      ∀ (c : ℕ), ∀ z'' ∈ cechZc ι (quotPart S J) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
        ∃ s : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) → Ω,
          (∀ I, s I ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).sub I) ∧
          (∀ (I₁ I₂ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)), I₁.1 ⊆ I₂.1 →
            s I₁ - s I₂ ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I₂) ∧
          ∀ t ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).secs,
            (∀ I, t - s I ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I) →
            ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
              cechMap S ι (Submodule.factor hJ) 0 z = z''

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.HypsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts modVec resImage)

def RestrictionPointsAll.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      modelPts S (modVec S y c p) =
        {z' | ∃ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p ∧
          z' = Subring.closure (resImage S y c p z)}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ClaimVanishDimZero.proof (h₁ : PointChartField.Statement) (h₂ : CechPointVanish.Statement) :
    ClaimVanishDimZero.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ μ r a m c₁ σ hd
  exact ⟨0, fun b c _ => h₂ F K ι Ω y (h₁ F K ι Ω y hd.2.1) _⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def BundlePair.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ γ β : K → ℤ,
      ∃ G B : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
        (∀ b : ℕ, (G.twist (B.pow b)).secs = secOver S y (γ + b • β)) ∧
        ∀ (n : ℕ) (η : Fin n → Ω),
          ((∀ j, η j ∈ secOver S y β) ∧ GeneratesOver S y β η) ↔
            ((∀ j, η j ∈ B.secs) ∧
              ∀ I, Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) =
                B.sub I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver cellMon locPart quotPart)

def CechPointEval.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)) →
    ∀ β : K → ℤ, ∃ (V : Submodule F Ω)
      (φ : ∀ I : ∀ k, Finset (ι k),
        LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y) →ₗ[F] Ω),
      ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0) →
        (∀ (g : MRingOver F ι) (t : cellMon F I),
          φ I (LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver F y) g) t) =
            aeval y g / aeval y (t : MRingOver F ι)) ∧
        Set.InjOn (φ I) (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β) ∧
        (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β).map (φ I) = V

example (F : Type) [Field F] (h : CechPointEval.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (fun c _ => isField_chartRingOver_pnPt_zero F c) 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def BaseTwistSecs.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm →
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ c : ℤ,
      secOver S y (c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = (Kleiman.twistSys S x c).secs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NefEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s → (Kleiman.Nef Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef k (graphVec x s) (graphDeg n))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def GraphModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (graphVec x s) baseBlock

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurvesDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W →
        relDim (baseComap F k₀ e W) = relDim W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelCurveNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      ∀ (W : Ideal (NumbersDVR.MRing ι F)) (W' : Ideal (NumbersDVR.MRing ι' F)),
        NumbersDVR.IsMultiProjPrime W → mIdealOver F y ≤ W → relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        NumbersDVR.IsMultiProjPrime W' → mIdealOver F y' ≤ W' → relDim W' = ((1 : ℕ) : WithBot (WithTop ℤ)) →
        baseComap F k₀ e W = baseComap F k₀' e' W' →
        NumbersDVR.intNum F W ![β] = NumbersDVR.intNum F W' ![β']

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

