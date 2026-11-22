import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0402
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0383
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriplesGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0772
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LefschetzFixedPointFiniteEtaleCorrespondence
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FactsAtMembership
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NFacts.AtMemFacts

theorem oneField_of_nAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : Formalism.L2.Host.CharFrame D} {C : NChoice D} {tp : Formalism.L2.Host.TupTied D cf C}
    (a : NAt hL D cf C tp) : GlobalTheory.HeightCounting.SameTw.OneField D C := by
  have key : ∀ X : Σ (D₁ : D7) (c₁ : Formalism.L2.Host.CharFrame D₁) (C₁ : NChoice D₁), Formalism.L2.Host.TupTied D₁ c₁ C₁,
      X = ⟨withLoc a.nt.L, cfL a.nt.L a.nt.cf, chL a.nt.L a.nt.C, tpL a.nt.L a.nt.tp⟩ →
        GlobalTheory.HeightCounting.SameTw.OneField X.1 X.2.2.1 := by
    rintro _ rfl
    exact (GlobalTheory.HeightCounting.SameTw.oneField_withLoc a.nt.L a.nt.C).2 a.nt.Sp.tw_reads
  exact key _ a.nt.pack

theorem facts_atMem : PrN → GlobalTheory.NRows.HypothesesX → SerN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => Facts (w.D Z) nch := by
  intro prn prx ser dzw dzs lf ltd lec hL
  have hA := GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.NRows.AtLayer.inputs_jumps_atMem prn prx hL)
    (GlobalTheory.HeightCounting.Up.TripFin.triplesGood prn ser hL)) (GlobalTheory.T.good_finite_types_all prn hL)
  refine EvG.imp hA fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne hrx cp => ?_
  obtain ⟨⟨⟨I, -, jumps⟩, trip⟩, good⟩ := H kp w Z Wt p0 t nch n xd c hne hrx cp
  obtain ⟨ne⟩ := hne
  have core : Core (w.D Z) := GlobalTheory.T.full_conclusion_of_inputs prn.what₂ prn.hc prn.decay dzw dzs lf ltd lec hL (w.D Z) I jumps
  have large : GlobalTheory.CoefDuty.Large (w.D Z) := ne.large
  exact { core with
    c2 := GlobalTheory.LocCoincide.main hL (w.D Z) I.P.M c.a.nt.toNBuilt I.P.H.hecke
    large := large
    duties := GlobalTheory.CoefDuty.duties_of_large prn.cheb (w.D Z) large core.Conclusion1.1 core.rhoBar
    nct := n.tie
    trip := trip
    same := GlobalTheory.HeightCounting.SameTw.sameTwist_at hL (w.D Z) _ nch _ c.a (oneField_of_nAt c.a)
    good := good }

end GlobalTheory.NFacts.AtMemFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocityStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_service_global_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Lk : LkT Bundle), (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c), Lk K β c b → LinkR p K β c b.R) → R1.SerreConditionAtBundlePoints (IsGoodE p.s) Lk := by
  first | exact @GlobalTheory.row_hServ_of_link | exact GlobalTheory.row_hServ_of_link | (intros; apply GlobalTheory.row_hServ_of_link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LefschetzFixedPointFiniteEtaleCorrespondence
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem _root_.GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
  ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
  ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
  ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
  ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
    ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
      ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  first | exact @UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence | exact UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence
end

