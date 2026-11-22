import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValue
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthRule

theorem depth_le_scaled_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  intro D T h j hj w hw s hs la y f hf
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA w) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ hw) f hf
  have hsK : ((s : 𝓞 T.Q.c.F) : T.Q.c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  let F : (recB h.toLawsCore).Cusp j w := ⟨f, hc⟩
  have hF : F ∈ (recPJ h j hj).thAll w := Submodule.subset_span hf
  have hsF : s • F ∈ (recPJ h j hj).WWc s w := ⟨F, hF, rfl⟩
  refine (iInf₂_le (s • F) hsF).trans (le_of_eq ?_)
  rw [recPJ_vAt_inc h j hj la y w (s • F)]
  have h1 : (s • F).1 = ((s : 𝓞 T.Q.c.F) : T.Q.c.F) • f := rfl
  rw [h1]
  exact vAtV_smul y _ f hsK

end GlobalTheory.DepthRule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaNormQuotientEllipticUnitSeriesStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNormQuotient_elliptic_unitSeries : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  first | exact @GlobalTheory.MomOne.ThetaQuot.theta_quot | exact GlobalTheory.MomOne.ThetaQuot.theta_quot | (intros; apply GlobalTheory.MomOne.ThetaQuot.theta_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.WeightExponents

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := by
  intro s t h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_eq {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := by
  ext x; simp

theorem not_inPsi_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (t : D.what₂.Tau) :
    ¬ InPsi Q.H (ComplexEmbedding.conjugate (DV.tauEmb D t)) := fun h =>
  ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both Q.H _ ⟨hp.2.2.2 t, h⟩

theorem tauEmb_ne_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (s t : D.what₂.Tau) :
    DV.tauEmb D s ≠ ComplexEmbedding.conjugate (DV.tauEmb D t) := fun h =>
  not_inPsi_conj hp t (h ▸ (hp.2.2.2 s : InPsi Q.H (DV.tauEmb D s)))

open Classical in
theorem wtA_apply {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) (i : ℕ) :
    wtA w (τ, i) = ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ext0 (w.aP t) i else 0) +
      if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then ext0 (w.aM t) i else 0) := by
  unfold wtA
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← conjEmb_eq]
  rfl

theorem wtA_tauEmb {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t), add_zero]
  · intro s _ hs
    rw [if_neg fun h => hs (tauEmb_injective D h).symm, if_neg (tauEmb_ne_conj hp t s), add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem wtA_conj {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t).symm, zero_add]
  · intro s _ hs
    rw [if_neg (tauEmb_ne_conj hp s t).symm, if_neg fun h =>
      hs (tauEmb_injective D ((ComplexEmbedding.involutive_conjugate _).injective h)).symm, add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem DF_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w := by
  classical
  unfold Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem weight_exponents : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  intro D Q hQ j hj w
  have hΨ : ∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t := fun τ =>
    ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hQ.1 τ, by rintro ⟨t, rfl⟩; exact hQ.1.2.2.2 t⟩
  refine ⟨DF_wtA hQ hj w, tauEmb_injective D, hΨ, fun τ => ⟨fun h => ?_, ?_⟩,
    fun t i => ⟨wtA_tauEmb hQ.1 w t i, wtA_conj hQ.1 w t i⟩⟩
  · obtain ⟨t, ht⟩ := (hΨ _).1 ((ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or Q.H τ).resolve_left h)
    exact ⟨t, by rw [← ht, ComplexEmbedding.involutive_conjugate _ τ]⟩
  · rintro ⟨t, rfl⟩
    exact not_inPsi_conj hQ.1 t

end GlobalTheory.WeightExponents
end
end

