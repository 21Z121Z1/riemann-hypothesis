import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0108
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0095
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsConstantsIndexBoundHypothesesLiftWeightsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_indexBound_hypotheses_liftWeights : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  first | exact @GlobalTheory.FinalJoin2.hyp_concl_at_run | exact GlobalTheory.FinalJoin2.hyp_concl_at_run | (intros; apply GlobalTheory.FinalJoin2.hyp_concl_at_run <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullRunHoldsOfCore
section
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_full_runHolds_of_core : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (J : CoreJ D) (EX : ErrX D), LawsJ J → LawsCore J.toCore → J.Q.Canon → (∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) → HalfEX J.toCore EX → OKPsi D → ∃ T : Top D, LawsP T ∧ T.toCore = J.toCore ∧ ∀ (p : ℕ) (hK : FieldOK0 D p) (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D) (hF : LawsFull TF), TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ (∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p) ∧ (∀ j, InR D j → ParOK TF.toTop EX p j) ∧ RunHolds x₀ hF.p hK.full.1 EX p := by
  obtain ⟨x₀, hrun⟩ := GlobalTheory.T.exists_threshold_run_holds
  refine ⟨x₀, fun D J EX hJ hJc hcan hpos hH hk => ?_⟩
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D J.toCore hJc hpos hk
  have hTH : HalfEX T.toCore EX := by rw [hTc]; exact hH
  have hTcan : T.toCore.Q.Canon := by rw [hTc]; exact hcan
  refine ⟨T, hT, hTc, fun p hK P hP xi hxi => ?_⟩
  obtain ⟨dd, TF, hF, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_full_data_extension D J T hJ hT hTc hTcan p hK P hP xi hxi
  have hH' : HalfEX TF.toTop.toCore EX := by rw [h1]; exact hTH
  have hpar : ∀ j, InR D j → ParOK TF.toTop EX p j :=
    GlobalTheory.T.parameters_ok_of_laws D TF.J TF.toTop EX p hF.j hF.p hF.sh rfl hF.canon hK hH'
      (fun j hj n => ⟨hF.lvA j hj n, (h5 j hj).2 n⟩)
  exact ⟨dd, TF, hF, h1, h2, h3, h4, h5, hpar, hrun D TF.toTop hF.p hK.full.1 EX p hpar⟩

end GlobalTheory.FinalJoin2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RowETiesB
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rowE_tiesB : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (sAnd Q RayPosition) (linkOf (pinPt ν)) fun _ => TiesB := by
  intro hR hL 𝒮 ν Q hC
  refine RowE.of_all ?_
  intro κ K β c b _ hq hl
  have hray : RayRec β.D β.O.ex.nch := GlobalTheory.T.rayClassFieldsInCoefficientField_constructedPoint K β hq.2
  obtain ⟨p, b', ⟨kap, lam, err, hs⟩, heq⟩ := hl
  let F : (Σ (D : D7) (O : Obj D), BdPt D O c) → Prop := fun x => RayRec x.1 x.2.1.ex.nch → TiesB x.1 x.2.1 c x.2.2
  have hp : F ⟨p.w.D p.Z, p.O, b'⟩ := by
    intro hr
    have hu := GlobalTheory.T.seriesUpdate_preserves_parameterFreeConditions_rayFields _ _ (sideW ν p) p.O.ex.errX p.O.ex.xd kap lam err
    show (sidePt b').Ties p.O.ex.errX p.O.ex.xd ∧ (sidePt b').Rays
    rw [hs]
    exact ⟨hu.1 (GlobalTheory.T.side_weight_compatible_ray_field hR hL 𝒮 ν hC K p), hu.2 (GlobalTheory.T.side_weight_rays_of_ray_rec hL 𝒮 ν K p hr)⟩
  have hb : F ⟨β.D, β.O, b⟩ := (congrArg F heq).mpr hp
  exact hb hray

end GlobalTheory.PlugPt
end

