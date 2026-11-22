import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0987
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0859
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0768
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0992
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0994
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0930
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0988
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0877
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.TateThesis.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFormAtEvaluationVectorEqRealisationLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceLift

theorem eMt_fix (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.MtL μ j) (hx : x ∈ Idx.TjV D μ j) :
    D.what₂.eMt μ j (D.what₂.jMt μ j x) = D.what₂.jMt μ j x := by
  have hL : ∀ y ∈ Idx.TjL D μ j, D.what₂.eMt μ j (D.what₂.jMt μ j y) = D.what₂.jMt μ j y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, hv⟩ := hz
      rw [← hv]
      exact LinearMap.congr_fun (D.what₂.eMt_idem μ j) _
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, map_smul, ha]
  induction hx using Submodule.span_induction with
  | mem z hz => exact hL z hz
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, map_smul, ha]

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

theorem extV_formOf_eMt (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c) :
    X.R.toRealDat.extV j (Y.tupT (Y.tup t)) (formOf Y hμ j (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c))) =
      X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) :=
  (extV_formOf Y hμ j _).trans (Y.mtRead j t hμ c)

theorem idem_fix (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c)
    (hc : D.what₂.eMt (Y.tup t) (j.1 + 1) (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) :
    X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c) =
      X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) := by
  have e2 := GlobalTheory.CenTranslate.liftForm_lvlOp (A3 := X.A3) (F := X.F.lv2) hH.ok.ok2 j t (idemOf X.A3.A.X)
    (fun b => idemOf_central X.A3.A.X hH.ok.ok2.irr b) c
  have e1 := (Y.formsL j t).op_eq c
  have e3 : D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t ((lE D X.A3.A X.F.P0 X.F.ψ0 j t).mulVec c)) := hc.symm.trans e1
  refine Y.hinj j t ?_
  refine (Y.mtRead j t hμ c).symm.trans ?_
  refine (congrArg (fun y => (Y.IL.jMt (Y.tup t) hμ j y).1) e3).trans ?_
  refine (Y.mtRead j t hμ _).trans ?_
  exact congrArg (fun v => X.R.toRealDat.extV j t (X.R.jV j t v)) e2

theorem isAlgV_self (j : Fin D.R.m) (t : X.T) (u : (X.A3.A.fam.L j t).S.Forms)
    (hu : X.R.jV j t u = X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u))
    (κ : X.Γ → (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).Q) (hκ : ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsLiftV X.R.toRealDat j t g (κ g)) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsAlgV X.R.toRealDat j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ (X.R.jV j t u) (X.R.jV j t u) := by
  have hs : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0
  refine (congrArg (X.R.HV j t).e hu).trans ?_
  have e3 := map_sum (X.R.jV j t) (fun g => (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u) Finset.univ
  have e4 := map_sum (X.R.HV j t).e (fun g => (X.R.jV j t) ((idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u)) Finset.univ
  refine ((congrArg (X.R.HV j t).e e3).trans e4).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (X.R.jV j t) ((idemOf X.A3.A.X).coeff g) ((X.A3.A.fam.L j t).r g u)
  have e6 := LinearMap.map_smul (X.R.HV j t).e (D.what₂.embLL ((idemOf X.A3.A.X).coeff g)) (X.R.jV j t ((X.A3.A.fam.L j t).r g u))
  refine ((congrArg (X.R.HV j t).e e5).trans e6).trans ?_
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V X.R.toRealDat X.char.grp.red_L X.char.models.jV j t g u
  have e7 : (X.R.HV j t).e (X.R.jV j t ((X.A3.A.fam.L j t).r g u)) =
      Bridge.g0Act (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).ch (κ g) ((X.R.HV j t).e (X.R.jV j t u)) :=
    funext fun h => hT.2 (κ g) (hκ g) h
  have e8 : D.what₂.embLL ((idemOf X.A3.A.X).coeff g) = RealDat.eC (A := X.A3.A) (sg0 D X.A3.A) g := by
    rw [RealDat.eC, hs]
  rw [e7, e8]

theorem lift_read (hP : GlobalTheory.Mem.R3.Pins X.R X.F X.cG) (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (μ : D.what₂.Tup) (hμ : Used0 D μ)
    (x : D.what₂.MtL μ (j.1 + 1)) (hx : x ∈ Idx.TjV D μ (j.1 + 1)) (v : (X.R.MW j (sg0 D X.A3.A)).Vec) :
    (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP μ (j.1 + 1) (D.what₂.jMt μ (j.1 + 1) x))) v =
      X.R.thF j (Y.tupT μ) (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) x)) v := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨c, rfl⟩ := (Y.eMt j t).surjective x
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using GlobalTheory.ProjLiftLaw.liftV_exists_core hC j t
  have h1 := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.F X.cG X0 Y hP hH j t c
  have h2 := GlobalTheory.ProjLiftLaw.thG_apply_eq hC j t κ hκ _ _
    (isAlgV_self j t _ (idem_fix Y hH j t hμ c (eMt_fix D _ _ _ hx)) κ hκ) v
  have h3 := GlobalTheory.Mem.ThetaRead3.thF_congr X.R.toRealDat Y.hinj j t (Y.tupT (Y.tup t)) (Y.tupT_tup t) _ _ (extV_formOf_eMt Y j t hμ c)
  exact ((congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y v) h1).trans h2).trans (congrArg (fun U => U v) h3).symm

theorem lift_read_at : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) :=
  fun _ _ _ Y _ _ _ _ _ j H x hx => lift_read Y H.pins H.intersectionNumber_baseChange j _ (used_of_tw H.tw) x hx _

end GlobalTheory.PlaceLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.PlaceIndep.linearIndependent_complex | exact GlobalTheory.PlaceIndep.linearIndependent_complex | (intros; apply GlobalTheory.PlaceIndep.linearIndependent_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsUnitarisableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_components_unitarisable : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  first | exact @GlobalTheory.RowSplitUnit.finTyp_rows_locS_unitarisable | exact GlobalTheory.RowSplitUnit.finTyp_rows_locS_unitarisable | (intros; apply GlobalTheory.RowSplitUnit.finTyp_rows_locS_unitarisable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDualStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  first | exact @GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | exact GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | (intros; apply GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  first | exact @GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | exact GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | (intros; apply GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuation
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.UnitaryBC
  GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.RSNonvan
open scoped nonZeroDivisors

theorem logNorm_eq_log_ideleModule (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) :=
  GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule E d

theorem natLat_iff (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (z : FiniteAdeleRing (𝓞 E) E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J :=
  GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles E N hN J hJ z

namespace GlobalTheory.RSNonvan

theorem detPow_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (x : ℝ) (g : GA E a) :
    GlobalTheory.RSJ.detPow E a x g = ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem secInv_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (hℓ : (ℓ : ℕ) + 1 = a)
    (u : Fin a → Cinf E) : GlobalTheory.RSJ.secInv u = (GlobalTheory.RSTheta.rowGL ℓ u)⁻¹ := by
  have hrow : GlobalTheory.RSJ.secRow u = GlobalTheory.RSTheta.rowMat ℓ u := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    have : ((i : ℕ) + 1 = a) ↔ i = ℓ := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; subst h; exact hℓ
    by_cases h : i = ℓ
    · simp [h, hℓ]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  unfold GlobalTheory.RSJ.secInv
  by_cases hu : IsUnit (u ℓ)
  · have hd : IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dif_pos hd]
    congr 1
    ext : 1
    rw [GlobalTheory.RSTheta.val_rowGL hu, ← hrow]
    rfl
  · have hd : ¬ IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dif_neg hd, GlobalTheory.RSTheta.rowGL, dif_neg hu, inv_one]

theorem indN_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (v : Fin a → Af E) :
    GlobalTheory.RSJ.indN N v = (GlobalTheory.ThetaPoisson.latt a J).indicator 1 (v - Pi.single ℓ 1) := by
  have key : (∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) ↔
      v - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J := by
    simp only [GlobalTheory.ThetaPoisson.latt, Set.mem_setOf_eq, Pi.sub_apply]
    refine forall_congr' fun i => ?_
    have e : (if (i : ℕ) + 1 = a then (1 : Af E) else 0) = (Pi.single ℓ (1 : Af E) : Fin a → Af E) i := by
      by_cases h : i = ℓ
      · subst h; simp [hℓ]
      · have : ¬ ((i : ℕ) + 1 = a) := fun h' => h (Fin.ext (by omega))
        simp [this, h]
    rw [e, natLat_iff E N hN J hJ]
  unfold GlobalTheory.RSJ.indN
  by_cases h : ∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N
  · rw [if_pos h, Set.indicator_of_mem (key.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]

theorem zint_eq_thetaZ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (x : ℝ) :
    GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ φ' Φ J (Pi.single ℓ 1) x := by
  unfold GlobalTheory.RSJ.Zint GlobalTheory.RSPole.thetaZ
  congr 1
  funext g
  rw [detPow_eq]
  congr 1
  unfold GlobalTheory.RSJ.thetaSum
  refine tsum_congr fun ξ => ?_
  simp only [GlobalTheory.RSJ.Psi, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, GlobalTheory.RSJ.rowAct, secInv_eq ℓ hℓ, map_inv]
  rw [indN_eq N hN ℓ hℓ J hJ]
  rfl

open GlobalTheory.CuspRep.CuspidalL2GL in
theorem haarFD (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

theorem samedeg_continuation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hT hu hu'
  obtain ⟨N, Φ, π, π', φ, φ', hπ, hπ', hφ, hφ', -, -, hN, hΦc, hΦs, hΦr, hZ'⟩ := GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL E a σ σ' ha hσ hσ' T hT.1 hT.2 hu hu'
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := haarFD E a
  obtain ⟨H, hHd, hHpos, hZH⟩ := hZ' μ 𝓕 h𝓕
  obtain ⟨ω, hωu, hω⟩ := id hσ
  obtain ⟨ω', hωu', hω'⟩ := id hσ'
  rw [← hπ] at hω
  rw [← hπ'] at hω'
  rw [CG.hasCentChar_mk] at hω hω'
  set ℓ : Fin a := ⟨a - 1, by omega⟩ with hℓdef
  have hℓ : (ℓ : ℕ) + 1 = a := by simp [ℓ]; omega
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  set J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hN0) with hJdef
  have hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := rfl
  have hπu : π.IsUnitary := ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩
  have hπu' : π'.IsUnitary := ⟨ω', hωu', CuspSub.hasCentral_iff.2 hω'⟩
  obtain ⟨φs, -, hφs⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu hφ
  obtain ⟨φs', -, hφs'⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu' hφ'
  have hφs1 : φs.1 = φ := hφs
  have hφs1' : φs'.1 = φ' := hφs'
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne E a ℓ Φ hΦc hΦs (hΦr ℓ hℓ) J (Pi.single ℓ 1) μ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨Fz, hFa, hFx, hF1, hF1'⟩ := hc π π' ω ω' hωu hωu' hω hω' φs φs'
    (Or.inr (hφs1 ▸ hφ)) (Or.inr (hφs1' ▸ hφ'))
  have hH0 : ∀ x : ℝ, H x ≠ 0 := fun x h => by
    have := (hHpos x).1
    rw [h] at this
    simp at this
  refine ⟨fun s => Fz s / H s, fun x hx => (hFa x hx).div (hHd.analyticAt _) (hH0 x), fun hne => ?_, fun x hx => ?_⟩
  · have h1 : Fz 1 = 0 := by
      by_cases hωω : ω = ω'
      · subst hωω
        rw [hF1 rfl]
        have hne' : CG.mk π ≠ CG.mk π' := by rw [hπ, hπ']; exact hne
        have h0 := fun φ hφ φ'' hφ'' =>
          GlobalTheory.CuspOrth.pet_eq_zero_of_ne_of_hasCentChar E a μ π π' ω hωu hω hω' hne' φ hφ φ'' hφ''
        rw [GlobalTheory.MspanROrth.setIntegral_mspanR_eq_zero E a ha π π' ω hωu hω hω' μ h0 𝓕' h𝓕' φs.1
          (hφs1 ▸ hφ) φs'.1 (hφs1' ▸ hφ'), mul_zero]
      · exact hF1' hωω
    simp [h1]
  · obtain ⟨-, hprod⟩ := (GlobalTheory.T.localRankinSelberg_logarithm_formula).2 E a a σ σ' hσ hσ' T hu hu' x hx
    have hx1 : (x : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hx.ne'
    have e : Fz x / H x / ((x : ℂ) - 1) = ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 := by
      rw [hFx x hx]
      have h2 := (hZH x hx).1
      rw [zint_eq_thetaZ μ 𝓕 φ φ' Φ N hN ℓ hℓ J hJ x] at h2
      simp only [GlobalTheory.RSPole.thetaZ] at h2
      rw [hφs1, hφs1', h2]
      simp only [lfac]
      have := hH0 x
      push_cast
      field_simp
    change HasProd _ (Fz x / H x / ((x : ℂ) - 1))
    rw [e]
    exact hprod.tprod_eq ▸ hprod

end GlobalTheory.RSNonvan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLatticeTwistedTuple_span_top : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  first | exact @GlobalTheory.PlaceRead.span_latS | exact GlobalTheory.PlaceRead.span_latS | (intros; apply GlobalTheory.PlaceRead.span_latS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

namespace GlobalTheory.RefTupleChars

theorem ref_chars : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx i
  have hlev := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1.lev
  have ht : GlobalTheory.RefTheta.t0 Y = A3.A.μ0 := by
    show Y.tupT D.what₂.mu0 = A3.A.μ0
    rw [← Y.tup0, Y.tupT_tup]
  rw [ht]
  have hxC := hlev.xi A3.A.μ0
  rw [hlev.xi_base] at hxC
  have hxi : R.toLevCh.xi A3.A.μ0 = 1 := MonoidHom.ext fun x =>
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one hxC x
  have e : Formalism.IndefR.Lift.chrTh (R.toLevCh.mu A3.A.μ0) R.eta (i.1 + 1) =
      (R.toLevCh.mu0 (i.1 + 1), R.toLevCh.mu0 (i.1 + 1) * R.eta⁻¹) := by
    simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, hxi, mul_one]
  rw [e]
  have hm := hlev.mu0 i
  have h2 := GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxC hlev.eta
  rw [hxi, mul_one, mul_one] at h2
  exact ⟨hm, h2⟩

end GlobalTheory.RefTupleChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualFrameConjugatePlaceIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualFrame_conjugate_place_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b)) ≤ 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b)) ≤ 1 := by
  first | exact @GlobalTheory.ConjInt.frame_mat_le_one | exact GlobalTheory.ConjInt.frame_mat_le_one | (intros; apply GlobalTheory.ConjInt.frame_mat_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_character_inverse : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ _ w _ x => ∀ l : StrictHenselianAcyclic hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  first | exact @GlobalTheory.StateLevel.level_char_allSt | exact GlobalTheory.StateLevel.level_char_allSt | (intros; apply GlobalTheory.StateLevel.level_char_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInfStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_unramified_inf : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  first | exact @GlobalTheory.LiftChar.main | exact GlobalTheory.LiftChar.main | (intros; apply GlobalTheory.LiftChar.main <;> assumption)
end

