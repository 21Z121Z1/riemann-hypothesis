import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1017

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideOfTwisted
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.ChoiceRead.exists_stC : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∃ c : StC l.mt l.b T.k T.psi, c.ch.twI = ch.twI := by
  intro hCo hCW hHM hPr hSer hL
  refine (GlobalTheory.T.choice_side_twisted_consistent hCo hCW hHM hPr hSer hL).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok
  have hc := H P x l ch tp hxi hpsi hQ hk hside hok
  choose e u hb hl hth using hc
  let G : ∀ v, (Dof x).what₂.muAt v ≠ (Dof x).what₂.mu0 → ∀ i : Fin (Dof x).R.m,
      (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1) :=
    fun v hv i => (((u v hv i)⁻¹ : (FractionRing (ch.Oe v))ˣ) : FractionRing (ch.Oe v)) • e v hv i
  have HB := GlobalTheory.ChoiceRead.pick_prop ch G (fun v j E => GlobalTheory.ChoiceRead.BasisAt ch v j E)
    (fun v hv i => (hb v hv i).smul _)
  have HL := GlobalTheory.ChoiceRead.pick_prop ch G
    (fun v j E => Submodule.span (ch.Oe v) (E '' GlobalTheory.ChoiceRead.latS v j) = GlobalTheory.ChoiceRead.latT ch v j)
    (fun v hv i => GlobalTheory.ChoiceRead.LatAt.smul_inv _ (hl v hv i))
  refine ⟨⟨GlobalTheory.ChoiceRead.withE ch (GlobalTheory.ChoiceRead.pick ch G) HB HL, GlobalTheory.ChoiceRead.tupWithE tp _ HB HL, hxi, hpsi, hQ, hk,
    GlobalTheory.ChoiceRead.choiceSide_withE hside _ HB HL, hok, ?_⟩, rfl⟩
  refine GlobalTheory.ChoiceRead.emtTheta_withE _ HB HL fun v i hv => ?_
  rw [GlobalTheory.ChoiceRead.pick_eq ch G v hv i]
  exact (hth v hv i).smul_inv _

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRealizationOfPublished
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose0

theorem exportAt_bundles : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : GalSide D), FieldOk X → GlobalTheory.TripleLocal.GalHodge D G.wd → LocalSituation.Conclusion5 D → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor hSR hSI hHI hHT hHRT
  intro D nch xd X Y G hF hGH hconds hTie hBase
  exact GlobalTheory.T.realization_of_published hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor D nch xd X Y G
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).1
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).2
    (GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hCusp hHI hHT hHRT D X)
    hGH hconds hF.galois hF.roots hTie hBase

end GlobalTheory.ExportClose0
end

