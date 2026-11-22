import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatTwistOfIsRatScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3157
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftInj_and_properties_of_rallis_of_nonVan : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.RawLift.RallisConv D → (∀ i t, NonVan R i t) → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, TypeNZ R i t ∧ GoodMem R i t ∧ DownEig R i t ∧ UnrCorr R i t (fun _ => True) ∧ Saturated R i t := by
  first | exact @GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing | exact GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing | (intros; apply GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_compatible_rows : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.EigTie.ResTied (w.D Z) Rw := by
  first | exact @GlobalTheory.ResLoc.resTied_atMem | exact GlobalTheory.ResLoc.resTied_atMem | (intros; apply GlobalTheory.ResLoc.resTied_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowestStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_pair_theta_lowest : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  first | exact @GlobalTheory.RefPair.split_pair_theta_mu0 | exact GlobalTheory.RefPair.split_pair_theta_mu0 | (intros; apply GlobalTheory.RefPair.split_pair_theta_mu0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRational
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.RatAll

section Zero

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_eq_zero (fw : FWTie T Rl.toRealDat κ v₀) {j : Fin D.R.m}
    (h : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (f : NX.FmK S ((j : ℕ) + 1)) :
    evW YS v₀ j (Subtype.val f) = 0 := by
  have hm : (YS.fi j).e (Subtype.val f) ∈ (Rl.FW j).WK := ((YS.fi j).wk _).1 f.2
  obtain ⟨c, hc⟩ := (fw.e j).surjective ⟨_, hm⟩
  have hc0 : c = 0 := Subtype.ext (by
    have h2 := c.2
    simp only [h, Submodule.mem_bot] at h2
    exact h2)
  rw [hc0, map_zero] at hc
  have h3 : (YS.fi j).e (Subtype.val f) = 0 := (congrArg Subtype.val hc).symm
  have h4 : Subtype.val f = 0 := (YS.fi j).e.injective (h3.trans (map_zero _).symm)
  rw [h4, map_zero]

theorem realRd_eq_zero (fw : FWTie T Rl.toRealDat κ v₀) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool)
    (h : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (ν : ℂ) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    realRd YS v₀ hρ i j b ν f = 0 := by
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) = 0
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1), evK YS v₀ hρ i j b x = 0 := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul a g => rw [evK_tmul, evW_eq_zero YS fw h, smul_zero]
  exact (congrArg (fun x => ν⁻¹ • x) (key _)).trans (smul_zero _)

end Zero

theorem ratRow : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK → RatHyp T Rl F κ v₀ O i j hV → RatRow YS v₀ hρ i j b := by
  intro hA hRF row D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H
  have hrat : ∀ ν, IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν → Rat hρ (realRd YS v₀ hρ i j b ν) := fun ν hν => by
    refine ⟨?_, GlobalTheory.SeriesTie.TwistRat.ratTwist hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H ν hν,
      GlobalTheory.SeriesTie.UnivRat.ratUniv_of_ratHyp hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H ν hν⟩
    apply GlobalTheory.SeriesTie.BaseRat.ratBase_of_ratHyp hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV <;> assumption
  by_cases hc : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · obtain ⟨fw⟩ := H.fw
    have hcore := H.core
    have hti := H.tieIn
    have hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j :=
      GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.chartIndependence_unconditional D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀
        hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti H.io O j H.pins
    have hph1 : ‖cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)‖ = 1 := (H.phase hrow0).2.1.2.2.2.2.1
    have hph0 : cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) ≠ 0 := fun e => by
      rw [e, norm_zero] at hph1; exact zero_ne_one hph1
    obtain ⟨c, hc0, hsc⟩ := exists_isScale Rl cG v₀ hρ hpin hcore.lev hcore.fam.tie hcore.models.cV hcore.thP H.io i j b
      (hti.hv₀ j _)
    have hsc' := hsc
    obtain ⟨gramR, c0R, c0L, hft, u, hu, hs⟩ := hsc'
    obtain ⟨ph, h1, h2⟩ := row D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ H.laws hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti
      j hV H.frame H.std gramR c0R c0L hft u hu
    have hR := hrat _ (IsRatScalar.intro (B := ρ.B i j b) hft hu hc0 h1 hs fun C hC _ => h2 C hC)
    have e : realRd YS v₀ hρ i j b (ph * c) = realRd YS v₀ hρ i j b (cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) :=
      LinearMap.ext fun f => (realRd_eq_zero YS fw hρ i b hc _ f).trans (realRd_eq_zero YS fw hρ i b hc _ f).symm
    exact ⟨_, ⟨mul_ne_zero hph0 hc0, c, hsc, 1, one_ne_zero, rfl⟩, e ▸ hR⟩
  · obtain ⟨ν, hn, hν⟩ := GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hc
    exact ⟨ν, hn, hrat ν hν⟩

end GlobalTheory.SeriesTie.RatAll

end
end

