import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0521
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInva
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0529
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterCongruenceInvarianceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_volume : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → ∀ (i : Fin a.n) g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.FamTraceChiCol.colLam (F0 W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) = ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * ∑ p : Fin (I.rec7 l Z).R.k, ∑ q : Fin (I.rec7 l Z).R.k, if q.val = p.val + 1 then g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q)) else 0) : ℂ) := by
  first | exact @GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum | exact GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum | (intros; apply GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_true_family_geometry : GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, ∃ (a : XGeo (I.rec7 l Z)) (c₀ : ℕ → ℂ), (∀ j, j ≤ B.R.m → (a.x j).Is) ∧ GlobalTheory.AdForm.PinX I l Z (pk W).ψ (pk W).θ a.x a.vac c₀ ∧ a.bT = 1 ∧ (∀ r s, (a.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ a.LT = (pk W).ΛX ∧ IsLineVec a.Lz a.ζ₀ ∧ star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) ∧ GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) ∧ (∀ r, vecB (a.oT B.R.m rfl) a.ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) ∧ (∀ n (h : n = B.R.m) x, ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) ∧ ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → ∃ s : LocX a (pk W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  first | exact @GlobalTheory.XGeoStd.exists_xgeo | exact GlobalTheory.XGeoStd.exists_xgeo | (intros; apply GlobalTheory.XGeoStd.exists_xgeo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneBF_red_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have h1 : InK B.V LV (· = v) 1 := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y _
    simp
  have hfix : s.om (1, κ) f = f :=
    GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (fun w hw => hw ▸ ⟨hG.tame, hU.1, hU.2⟩) f hf 1 κ h1 hκ
  have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ f hf.1
  have hsplit : s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f =
      s.om (1, n * J.d.emb0 γ) (s.om (1, J.d.levi t) f) := by
    have : n * J.d.levi t * J.d.emb0 γ * κ = (n * J.d.emb0 γ) * J.d.levi t * κ := by
      rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
      simp only [mul_assoc]
    rw [this]
    have e : ((1 : GA D B.V), (n * J.d.emb0 γ) * J.d.levi t * κ) =
        ((1, n * J.d.emb0 γ) * (1, J.d.levi t)) * (1, κ) := by
      simp
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix]
  intro h0
  apply hne
  rw [hsplit, h𝔉.equiv _ hg n hnN hnG γ hγ, h0]
  have : opA ψ J.d B.o B.ζ s.om₀ n γ 0 = 0 := by
    funext w
    simp [opA, jacT, heisO]
  rw [this, smul_zero]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.FlatEqui

variable {D : D7}

theorem levi_mem_flagN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    d.levi u ∈ flagN d :=
  ((flag_jacobi_structure D S S₀ ρ d).1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩

theorem psiUni_mul (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u v : GL (Fin ρ) (AE D)}
    (hu : u ∈ UX D ρ) (hv : v ∈ UX D ρ) : psiUni ψ (u * v) = psiUni ψ u * psiUni ψ v := by
  have h : ∀ a, psiFlag ψ d (d.levi a) = psiUni ψ a := fun a => by
    have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
    rwa [mul_one] at this
  rw [← h, ← h, ← h, map_mul, psiFlag_mul d ψ (levi_mem_flagN d hu) (levi_mem_flagN d hv)]

theorem flatBF_levi (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (om' : Om B.V₀ J.W) (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') (Ψ : WO B.V J.W → ℂ)
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (γ : UX D ρ) :
    flatBF s (s.om (1, J.d.levi γ.1) Ψ) = star (psiUni ψ γ.1) • flatBF s Ψ := by
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  have he := (GlobalTheory.T.doubleMixedModel_baseValue_equivariant D ψ ρ B J s om' hom Ψ hΨ).2
  simp only [flatBF, flat, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, he]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ γ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [inv_mul_cancel_left]
  rw [Subgroup.coe_mul, psiUni_mul ψ J.d γ.2 u.2, star_mul', mul_assoc]

theorem flatBF_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom Ψ hΨ h₀ n hn h'
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc]
  rw [e, flatBF_levi ψ ρ B J s om' hom _ (s.weil.om_pres _ _ hΨ) ⟨γ, hγ⟩,
    GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h', psiFlag_levi_mul ψ J.d γ (radX_le_stabX J.d hr), opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]

end GlobalTheory.FlatEqui

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInvaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselUnfolding_evaluationIntegrand_continuous_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) ∧ ∀ r ∈ radX J.d ⊔ J.d.emb0.range, ∀ h, J.perAll ψ B s.om₀ φ (rTrans (r * h) G) (evalBF s (s.om (1, (r * h)) Φ)) = J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) := by
  first | exact @GlobalTheory.Unf.evalIntegrand_continuous_invariant | exact GlobalTheory.Unf.evalIntegrand_continuous_invariant | (intros; apply GlobalTheory.Unf.evalIntegrand_continuous_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementPropertyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_property : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → GlobalTheory.LevZero.StabAt f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (GlobalTheory.LevZero.frAt f B a₀ a) (GlobalTheory.LevZero.datZero W) (finE (D.sp.Y 0) κ) ∈ (GlobalTheory.LevZero.datZero W).P.H) := by
  first | exact @GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup | exact GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup | (intros; apply GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_ideal_index_product : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → QLev f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  first | exact @GlobalTheory.StepConst.cI_mul_idx | exact GlobalTheory.StepConst.cI_mul_idx | (intros; apply GlobalTheory.StepConst.cI_mul_idx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelPreservesRamifiedFormsLiveCharts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem kernels_keep_ramL : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j), A.Is → A.Live ι → ∀ i, i < B.R.m → ∀ φ, A.RamL ι i φ → A.RamL ι (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hOk hP l Z u a Ch₀ Ch A ι hIs hLive i hi φ hφ
  refine ⟨GlobalTheory.T.chainStepKernel_preserves_levelRamifiedForms I hOk hP l Z u a i hi φ hφ.1, ?_⟩
  intro c' hc'
  have hSB : IsSBHalf A.e (stdHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))) (0 : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :=
    ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun t h => absurd rfl h⟩
  have key := fun (c : (I.chain l u a).cls i) (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) =>
    (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hOk hP l Z u a Ch₀ A hIs i hi (A.chOf i c) (A.chOf (i+1) c') 0 hSB 1
      (fun z => by simp [hLive.dead i hi _ hc']) ⟨c, rfl⟩ ⟨c', rfl⟩).2.2 z
  have hxi : ∀ c : (I.chain l u a).cls i, xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    funext x
    obtain ⟨γ, rfl⟩ : ∃ γ, toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ = x := by
      refine ⟨(LinearMap.toMatrix' x).submatrix (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))), ?_⟩
      show Matrix.toLin' _ = x
      conv_rhs => rw [← Matrix.toLin'_toMatrix' x]
      rfl
    have h1 := key c γ
    simp only [Pi.zero_apply, one_mul] at h1
    exact (map_eq_zero_iff _ B.embLL.injective).1 h1.symm
  have hth : ∀ c : (I.chain l u a).cls i, I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') = 0 := by
    intro c
    unfold TC.th thAt
    rw [hxi c]
    exact thOf_zero ..
  have hunf : ∀ c : (I.chain l u a).cls i, (I.chain l u a).unf i c c' = 0 := by
    intro c
    show ChainIn.unf _ _ _ _ _ _ = 0
    unfold ChainIn.unf
    show _ ∘ₗ jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 ∘ₗ _ = 0
    rw [hth c]
    have hJ : jetC I.J.cD (0 : VCx B.fields.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) = 0 := by
      funext m
      simp [jetC, derivAt0, iteratedFDeriv_zero_fun]
    rw [hJ]
    have hM : jetMap (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) 0 = 0 := by
      have hL : jetLin (0 : (DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) → ℂ) = 0 := by
        apply (MvPolynomial.basisMonomials _ ℂ).ext
        intro m
        rw [jetLin, Module.Basis.constr_basis]
        simp
      unfold jetMap
      rw [hL]
      simp
    rw [hM]
    simp
  have hK : ∀ c : (I.chain l u a).cls i, (I.chain l u a).Kmap i c c' = 0 := by
    intro c
    unfold ColumnChain.Kmap
    rw [hunf c]
    simp
  funext y
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, hK]
  simp

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistEulerFactorsRestoreProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem restore_holds : ∀ D : D7, Restore D := by
  intro D _ c w hw k hk s s' hs hs' _ _
  obtain ⟨hr, -, hfl⟩ := hs
  obtain ⟨hr', -, hfl'⟩ := hs'
  have h1 : s.V.rank = D.R.rankY k := hfl.rank
  have h2 : s'.V.rank = D.R.rankY k + D.R.t := by
    have h : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h]; simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  have h3 : D.R.rankY k + D.R.t = D.R.r + (k + 1) * D.R.t := by
    simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  obtain ⟨hL, hL₀⟩ := GlobalTheory.T.twistEulerFactors_restore_quotientLValues D c w hw k hk
  obtain ⟨hd0, hd⟩ := GlobalTheory.T.twistEulerFactors_restore_normalizingFactor D c w hw (D.R.rankY k)
  refine ⟨hL, hL₀, ?_, ?_⟩
  · unfold dS; rw [h1, h2]; exact hd0
  · unfold dS; rw [h1, h2, hd, h3]

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.AdForm.CompFix.intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s) ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 :=
          mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.AdForm.comp_fixes_stdPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b κ hκ i g hg

  obtain ⟨e, he⟩ := hS.1
  obtain ⟨hpi, hT⟩ := GlobalTheory.T.generator_mem_split_prime_level_prime_mem_place I hOk l Z u k (p i) (e i) (he i)
  have key : ∀ κ₀ ∈ A.U j b, ∀ r s : Fin ((I.rec7 l Z).sp.X j).rank,
      ((mt _ κ₀).map (p i).pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = ((I.rec7 l Z).sp.X j).rank →
        valuation k (((mt _ κ₀).map (p i).pr) r s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s) < 1) := by
    intro κ₀ hκ₀ r s
    have hn := rankN (I.rec7 l Z) j hj
    have h3 := GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice I hOk hPins l Z u a Ch A hA j hj b κ₀ hκ₀ (p i).v hT (Fin.cast hn s)
    let y : Fin ((I.rec7 l Z).R.N j) → AE (I.rec7 l Z) := fun r' =>
      mt _ κ₀ (Fin.cast hn.symm r') s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) (Fin.cast hn.symm r') s
    have hy : (fun r' => Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (toEAf (I.rec7 l Z) (y r'))) =
        (fun r' => Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (GlobalTheory.AdForm.finM _ hn κ₀ r' (Fin.cast hn s)) -
          (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (p i).v.adicCompletion (I.rec7 l Z).host.F)) r' (Fin.cast hn s)) := by
      funext r'
      simp only [y]
      rw [RingHom.map_sub, RingHom.map_sub]
      congr 1
      by_cases h : r' = Fin.cast hn s
      · subst h
        have : Fin.cast hn.symm (Fin.cast hn s) = s := Fin.ext rfl
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
      · have h' : Fin.cast hn.symm r' ≠ s := fun h2 => h (Fin.ext (by rw [← h2]; rfl))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
    have hLb : ∀ x, x ∈ (A.K j hj b).lev.Lb ↔ ∀ j' : Fin ((I.rec7 l Z).R.N j), ∃ r : 𝓞 (I.rec7 l Z).host.E, x j' = (r : (I.rec7 l Z).host.E) ∧ (j'.1 + 1 = (I.rec7 l Z).R.N j → X.piT u ∣ r) :=
      fun x => (hA.reads j hj).lb b x
    have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime (I.rec7 l Z) k (p i) (e i).1 (he i) _ (X.piT u) hpi _ hLb y (hy ▸ h3) (Fin.cast hn r)
    have hyr : y (Fin.cast hn r) = mt _ κ₀ r s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) r s := rfl
    rw [hyr] at h4
    have h1 : (p i).pr ((1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) r s) =
        (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [map_sub, h1] at h4
    refine ⟨?_, fun hr => ?_⟩
    · have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s ∈ 𝒪[k] by
        simp only [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      rwa [sub_add_cancel] at this
    · exact h4.2 (by rw [Fin.coe_cast, ← hn]; exact hr)

  set M := (mt _ κ).map (p i).pr with hMdef
  set M' := (mt _ κ⁻¹).map (p i).pr with hM'def
  have hmt : ∀ x y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j), mt _ (x * y) = mt _ x * mt _ y := fun x y => by
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, mul_inv_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, inv_mul_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM := GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL (I.rec7 l Z) k (p i) _ _ (β j i) κ g hg
  rw [← hMdef] at hM
  rcases Nat.eq_zero_or_pos ((I.rec7 l Z).sp.X j).rank with h0 | hpos
  · have : g = 1 := by
      exact Units.ext (Matrix.ext fun a _ => absurd a.2 (by omega))
    rw [this, one_smul]
  let r₀ : Fin ((I.rec7 l Z).sp.X j).rank := ⟨((I.rec7 l Z).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank := by simp only [r₀]; omega
  have hK := GlobalTheory.AdForm.CompFix.intMat_keeps M M' hMM (fun r s => (key κ hκ r s).1) (fun r s => (key κ⁻¹ (inv_mem hκ) r s).1) r₀
    (fun s => (key κ⁻¹ (inv_mem hκ) r₀ s).2 hr₀)

  have hbg : ∀ x : Fin ((I.rec7 l Z).sp.X j).rank → k, (β j i).b *ᵥ (g⁻¹ • x) = M' *ᵥ ((β j i).b *ᵥ x) := by
    intro x
    have e1 : (β j i).b * g.val = M * (β j i).b := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, (β j i).b'b, Matrix.mul_one]
    have e2 : (β j i).b *ᵥ x = M *ᵥ ((β j i).b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine Pair.ext fun x a' => ?_
  rw [Pair.smul_hasVal, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK ((β j i).b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.StdUnn

theorem weilSch_apply_zero_continuous : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n, Continuous fun g : G D n => (ω g Φ).1 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  have hc := (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ f hf).2
  have hk := (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  simp_rw [key]
  exact hc.comp hk

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProofStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  first | exact @GlobalTheory.FinPl.liftExact | exact GlobalTheory.FinPl.liftExact | (intros; apply GlobalTheory.FinPl.liftExact <;> assumption)
end

