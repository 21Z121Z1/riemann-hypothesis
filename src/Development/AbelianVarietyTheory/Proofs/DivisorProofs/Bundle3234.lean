import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
import Formalism.LocalToGlobal.Divisibility.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGenericSemiAb

theorem isAmpleLB_of_generic_of_symm (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R]
    (hc : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (hA : IsAbelianScheme ((Over.pullback (jK R)).obj G)) (L : LB G.left) (hL : L.IsLB)
    (hLK : RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))))
    (hs : LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L) : IsAmpleLB L := by
  obtain ⟨M, hMa, hMs⟩ := GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian R G hG hA
  have hMK : RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) := by
    have : IsProper ((Over.pullback (jK R)).obj G).hom := hA.proper
    have h1 : IsAffineHom (jK R) := by unfold jK; infer_instance
    have : IsAffineHom (pullback.fst G.hom (jK R)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback G.hom (jK R)).flip h1
    exact (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_linComb hMa.isLB _ _)).2
      (hMa.pull_of_isAffineHom _)
  obtain ⟨R', _, _, _, _, _, ρ, G', _, π, hinj, hfin, hpb, N, a₀, r, a, β, hN, ha₀, -, hiso⟩ :=
    GlobalTheory.T.exists_finiteNormalCover_symmBundle_power_decomposition R hc G hG hA L M hL hMa.isLB hLK hMK hs hMs
  have : IsFinite π := by
    have : IsFinite (spMap ρ) := by
      unfold spMap
      rw [IsFinite.SpecMap_iff]; exact hfin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.1.flip this
  have hamp := GlobalTheory.AmplePowLinComb.isAmpleLB_of_lbPow_lbIso_linComb _ (L.pull π) (M.pull π)
    (hMa.pull_of_isFinite π) (LB.isLB_linComb hL _ _) N a₀ r a (fun i => (β i).left) hN ha₀ hiso
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  exact GlobalTheory.AmpleFiniteBase.isAmpleLB_of_pull R R' ρ hinj hfin G G' π hG hpb L hL hamp

theorem isAmpleLB_of_generic : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R],
    IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB →
    RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) →
    LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L :=
  fun R _ _ _ _ hc G _ hG hA L hL hLK hs => isAmpleLB_of_generic_of_symm R hc G hG hA L hL hLK hs

end GlobalTheory.AmpleGenericSemiAb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePrincipalPolarisationEveryFibreOfGenerat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PolFibre

theorem generic_fibre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) :
    IsProper (pullback.snd G.hom (jK R)) ∧
      RelAmple ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) ∧
      KTriv ((Over.pullback (jK R)).obj G) (U.LG.L.pull (pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  have hiso := isGrpPullback_of_iso U.gen
  have hLG : U.LG.L.IsLB := U.LG.isLB
  obtain ⟨w, hw⟩ : LBIso (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left) := by
    obtain ⟨w, hw⟩ := U.ext
    exact LBIso.symm ⟨w, hw⟩
  have hpw := (isGen_iff w).1 hw
  have : IsIso U.gen.hom.left := ((Over.forget _).mapIso U.gen).isIso_hom
  have := A.isAb.proper
  refine ⟨?_, relAmple_pull hiso.1 A.isLB (pull_isLB hLG _) hpw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hiso A.isLB (pull_isLB hLG _) hpw A.ktriv⟩
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  rw [← e]
  infer_instance

theorem eq_generic {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] (x : Sp K ⟶ Sp R)
    (h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥) : x (closedPoint K) = jK R (closedPoint (FractionRing R)) := by
  refine PrimeSpectrum.ext ?_
  rw [h0]
  show ⊥ = Ideal.comap (algebraMap R (FractionRing R)) (maximalIdeal (FractionRing R))
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]

theorem relAmple_kTriv_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R), Set.range x ⊆ (W : Set (Sp R)) → RelAmple ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (U.LG.L.pull (pullback.fst G.hom x)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW K _ x hx
  obtain ⟨-, hp⟩ := GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate R hR D A G hG U W hW
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hy : x (closedPoint K) ∈ W := hx ⟨_, rfl⟩
  by_cases h0 : (x (closedPoint K) : PrimeSpectrum R).asIdeal = ⊥
  · obtain ⟨h1, h2, h3⟩ := generic_fibre U
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG (FractionRing R) (jK R) h1 h2 h3 K x
      (eq_generic x h0)
  · obtain ⟨K₁, _, z, hz, h1, h2, h3⟩ := GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised R hR D A G hG U W hp (x (closedPoint K)) hy h0
    exact GlobalTheory.T.relAmple_kernelTrivial_of_same_image_point (Sp R) G hG.quasiCompact hG.separated U.smooth U.LG.L hLG K₁ z h1 h2 h3 K x hz.symm

end GlobalTheory.Mum.PolFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinsetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidSymmetricBundle_descends_to_subring_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  first | exact @GlobalTheory.rigSym_descends_to_subring_containing_finset | exact GlobalTheory.rigSym_descends_to_subring_containing_finset | (intros; apply GlobalTheory.rigSym_descends_to_subring_containing_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.FourBoundsAtBundles

theorem tupAllUsed_part {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2

theorem pDiv_of {D : D7} {O : Obj D} {c : ℝ} (b : Ind.Part D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : Ind.PDiv D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (tupAllUsed_part b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩

end GlobalTheory.Fc.FourBoundsAtBundles

namespace GlobalTheory.Fc.FourBoundsAtBundles

open GlobalTheory.Fc.R1

theorem evW_of_atAll {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.FourBoundsAtBundles
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFlagIndependentStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondChern_flag_independent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c2F hX σ h fl = c2F hX σ h fl' := by
  first | exact @GlobalTheory.LineForm.c2F_flag_indep | exact GlobalTheory.LineForm.c2F_flag_indep | (intros; apply GlobalTheory.LineForm.c2F_flag_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondChern_real_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧ (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 := by
  first | exact @GlobalTheory.ChernReal.c2F_isRealForm_closed | exact GlobalTheory.ChernReal.c2F_isRealForm_closed | (intros; apply GlobalTheory.ChernReal.c2F_isRealForm_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

def conjPt {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts p σ) :
    CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have e : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    rw [Category.assoc, y.2, e]⟩

theorem ratVal_conj {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}
    {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) :
    ratVal f y' = starRingEnd ℂ (ratVal f y) := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]

theorem val_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  intro k _ X _ p P a b σ y
  have h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  obtain ⟨θ₁, h₁, e₁⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y _ _ hi hj
  obtain ⟨θ₂, h₂, e₂⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ (conjPt y) _ _
    (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)
  refine ⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]
  have hθ : θ₁ * starRingEnd ℂ θ₁ = 1 := by
    rw [Complex.mul_conj', h₁]
    simp
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) *
    ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_spMap_subtype_comp_eq_of_isSeparated : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0}) (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p → spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  first | exact @GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | exact GlobalTheory.sections_eq_of_spMap_subtype_comp_eq | (intros; apply GlobalTheory.sections_eq_of_spMap_subtype_comp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescendsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_separate_quotient_generic_fibre_descends : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [NumberField F] (σ : F →+* ℂ) (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → 1 ≤ n → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → letI := algebraΓOfHom sX; ∀ (K : CanonLB sX n) (δ N' B : LB X) (hδ : δ.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (N : LB W) (hN : N.IsLB) (m : ℕ), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → IsNef F δ → IsBig F δ → IsNef F N' → (n + 1).choose 2 < m → cls B hB = m • cls δ hδ + cls N' hN' → ∀ (J : Type) [Fintype J] (v : J → (Sp ℂ ⟶ V)), Function.Injective v → (∀ j, v j ≫ i ≫ sX = spMap σ) → (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 sX (tens K.bundle B) ⊤, ∑ j, a j * H0.val (v j ≫ i) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.QuotSep.sections_separate_quotient_fibre | exact GlobalTheory.QuotSep.sections_separate_quotient_fibre | (intros; apply GlobalTheory.QuotSep.sections_separate_quotient_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianLieSeminegativeBis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := GlobalTheory.T.semiNegative_descends_fieldExtension_curve k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLieLatticeAgree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.ModZero

theorem repr_isIntAf {p : ℕ} [Fact p.Prime] (D : Datum p) {κ : Type} (b : Module.Basis κ ℤ D.La)
    (u : AfP p ⊗[ℚ] VQ D) (hu : u ∈ LaHat D) (i : κ) :
    IsIntAf ((Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)).repr u i) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    intro v
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, one_smul,
      eq_intCast (algebraMap ℤ ℚ), map_intCast, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => intro v; rw [map_zero, Finsupp.zero_apply, map_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => intro v; rw [map_add, Finsupp.add_apply, map_add]; exact add_mem (hu v) (hu' v)
  | neg u _ hu => intro v; rw [map_neg, Finsupp.neg_apply, map_neg]; exact neg_mem (hu v)

end GlobalTheory.LKGeo.ModZero

open GlobalTheory.LKGeo.ModZero in

theorem GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  intro p _ D z hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bA := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  refine bA.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime p (bA.repr z i) fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := hz n hn hc
  exact ⟨bA.repr w i, repr_isIntAf D b w hw i, by rw [map_nsmul, Finsupp.smul_apply]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesTraceTermAtEvaluationVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.OneTermEval

set_option maxHeartbeats 4000000 in

theorem series_term_at_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct U hdet χ ξR ω φ hK Λ h hSp hLa N x₀ P x f y h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨y₀, c, hr, hc, hmain⟩ := GlobalTheory.T.shortSeries_baseDatum_adelicForm_multiple D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h hSp hLa N x₀ P y h1 h2 h3 h4 h5 h6 h8
  refine ⟨y₀, c, hr, hc, fun φ' hφ' w hw u => ?_⟩
  obtain ⟨F₀, hF₀, he⟩ := GlobalTheory.LevelMoveShort.short_translate D G Pl0 T0 A T R F κ v₀ fw hT hC i hU ℓ hLev hAct v (ownAt D v) hRun hMb U hdet Λ N x₀ P x f h1 h2 h3 h4 h5 h6 h7 u
  have e := (hU i (sg0 D A)).2.2 ((u : G)⁻¹) (cuspTo hT.p fw i F₀)
  have hc1 : (R.FW i).chi ((u : G)⁻¹) = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hC.grp.chiW, Units.val_one, map_one]
    refine Finset.prod_eq_one fun PP _ => ?_
    have hd : Matrix.GeneralLinearGroup.det (R.eG ((u : G)⁻¹) PP) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet u⁻¹ PP
    rw [hd, map_one, Units.val_one]
  rw [hc1, Units.val_one, map_one, one_smul] at e
  have e2 : adForm R i ((R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀)) (fun ρ => w ρ) =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ)) :=
    congrArg (fun T => T (fun ρ => w ρ)) e
  rw [he, e2, hmain φ' hφ' w hw F₀ hF₀, map_smul]

end GlobalTheory.OneTermEval
end
end

