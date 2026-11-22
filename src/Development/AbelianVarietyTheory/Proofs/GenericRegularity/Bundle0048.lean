import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagreStatement
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0049
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0047
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0047
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvCEqZeroIffRdUEqZero
section
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.GenericDetect

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdU_eq_zero_iff (hL : GlobalTheory.Reg.EvLaws Xo c) (U : Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp)
    (Z : Comp Xo c) (x : (U.X k).dom) (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hm : FrMap φ (genFr h Z) y') (hb : FrBor t (U.un k x) y') {u : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c u n) : rdU U f k x = 0 ↔ evC h Z f = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have h1 : evR Xo c f y' = φ (evC h Z f) := by
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test (Om Z) (genFr h Z)
    unfold evC
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ _ hy₀,
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (φ.comp χ) y₀ y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ hy₀ hm)]
    rfl
  have h2 : evR Xo c f y' = wchar (ex Dw u n) t * evR Xo c f (U.un k x) :=
    hL.wt u n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) hb
  have h3 : wchar (ex Dw u n) t ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero
  have h4 : rdU U f k x = toC (evR Xo c f (U.un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos x.2]
  have h5 : φ (evC h Z f) = 0 ↔ evC h Z f = 0 := map_eq_zero_iff φ φ.toRingHom.injective
  rw [h4, ← h5, ← h1, h2, mul_eq_zero, or_iff_right h3]
  rfl

theorem eq_zero_of_off_meagre {V : Type} [TopologicalSpace V] [BaireSpace V] {D : Set V} (hD : IsOpen D)
    {S : ℕ → Set V} (hS : ∀ n, IsClosed (S n) ∧ interior (S n) = ∅) {g : V → ℂ} (hg : ContinuousOn g D)
    (h0 : ∀ x ∈ D, (∀ n, x ∉ S n) → g x = 0) : ∀ x ∈ D, g x = 0 := by
  have hd : Dense (⋂ n, (S n)ᶜ) :=
    dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
  intro x hx
  by_contra hne
  have ho : IsOpen (D ∩ g ⁻¹' {0}ᶜ) := hg.isOpen_inter_preimage hD isOpen_compl_singleton
  obtain ⟨y, hy, hy'⟩ := hd.inter_open_nonempty _ ho ⟨x, hx, hne⟩
  exact hy.2 (h0 y hy.1 (Set.mem_iInter.1 hy'))

end GlobalTheory.GenericDetect

open GlobalTheory.GenericDetect in

theorem GlobalTheory.evC_eq_zero_iff_rdU_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp) (Z : Comp Xo c) (x₀ : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x₀) y') → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h k Z x₀ ⟨φ, y', t, hm, hb⟩ u n hd f hf
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  refine ⟨fun h0 => ?_, fun h0 => (rdU_eq_zero_iff hL U h k Z x₀ φ y' t hm hb hf).1 (h0 _ x₀.2)⟩
  obtain ⟨Z', S, hS, hg⟩ := GlobalTheory.T.exists_genericComponentPoints_off_meagre E H Dw l Xo c σ r U hσ hU h k
  have hO : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  have key : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom a m → ∀ g ∈ sec Xo c a m, evC h Z' g = 0 →
      ∀ x ∈ (U.X k).dom, rdU U g k x = 0 := by
    intro a m ha g hgs hg0
    refine eq_zero_of_off_meagre hO hS (hU.2.2.2.2.1 a m ha g hgs k).1.continuousOn fun x hx hxS => ?_
    obtain ⟨ψ, z, s, hm', hb'⟩ := hg ⟨x, hx⟩ hxS
    exact (rdU_eq_zero_iff hL U h k Z' ⟨x, hx⟩ ψ z s hm' hb' hgs).2 hg0
  have hZ : Z' = Z := by
    by_contra hne
    obtain ⟨χ, hχ, -, h1, hz⟩ := GlobalTheory.T.exists_idempotent_weightZero_section_of_component E H Dw l Xo c hL h (hA h) Z
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have := (rdU_eq_zero_iff hL U h k Z x₀ φ y' t hm hb hχ).1 (key 0 0 hD χ hχ (hz Z' hne) _ x₀.2)
    rw [h1] at this
    exact one_ne_zero this
  subst hZ
  exact key u n hd f hf h0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCusp
section
noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lieFac_scalar {D : D7} (T : Top D) (j i : ℕ) : lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) = 1 := by
  have : ∀ x, wtA (wEt D j i) x = 0 := by
    intro x
    simp [wtA, wEt, WeightAlgebra.wscalar, ext0]
  simp [lieFac, this]

theorem weight_add_eq_smul_of_G2 {D : D7} {j : ℕ} {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wadd wF w2 = wsmul (WeightFamilies.dimY D j + 4) wL := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold wadd wsmul
  congr 1
  · funext τ i; rw [add_comm]; exact h2 τ i
  · funext τ i; rw [add_comm]; exact h3 τ i
  · rw [add_comm]; exact h1

theorem thR_pos {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hg : ∀ i, 0 < D.host.g i) (hd : 0 < DF w) : 0 < thR w := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _
  have h0 := hg 0
  have h1 := hg 1
  unfold thR I2.th I2.RR
  positivity

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem curveHyp_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hP
  obtain ⟨hT, hN, hlN, hZ, hLow⟩ := hGen
  have hZb : 0 ≤ Zb D large₂ := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact le_trans (by positivity) hd.2.1
  have hC2 : 0 ≤ C2 := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := hd.1
    rw [hP.tie.1] at this
    linarith
  have hrow := (GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds D _ _ j (recPJ h j hj) large₂ H C2 A2 CT ka wL wF Tn nP nW h0 1 G.N 1 hj hP one_pos hN one_pos hlN
    (by rw [Nat.cast_one, Real.log_one]; positivity)).2.2.2.2.2.2.2.2.1
  have hc0 : 0 ≤ cc D large₂ C2 A2 7 wL := by
    have h1 : 0 ≤ zBase large₂ := hZb
    have h2 : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
    unfold cc WeightFamilies.RRv WeightFamilies.PPv
    positivity
  obtain ⟨hsz, PL, lN, -, -, hI1, w2, hw2, th2, -, hth2, -⟩ :=
    (FamilyHypotheses.fourthHypothesis_iff_sizes_and_index large₂ (recPJ h j hj) H C2 A2 7 ka wL wF Tn nW).1 hC.2.2.2.2.2.2.1
  have hth : 0 < thR wL := thR_pos wL (fun i => lt_of_le_of_lt (Nat.zero_le _) (hsz.2.2.2.2.2 i))
    (lt_of_lt_of_le (by norm_num) hP.df)
  refine ⟨g0, hT.1, ?_, ⟨WeightFamilies.dimY D j + 4, w2, th2, weight_add_eq_smul_of_G2 hw2, (hnz w2 th2 hth2).1⟩, hg0⟩
  refine GlobalTheory.T.set_constants_good_embedding_recursion D T h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj))
    (cc D large₂ C2 A2 7 wL) large₂ H.CK H.C1 H.A1 h0 Tn nP nW hP.hyp.2.1 hZ (fun hjm => ?_) hc0 (by linarith) (fun hjm => ?_)
  · obtain ⟨hi, hcu, -, -, hA, -⟩ := hEta hjm
    refine ⟨hi, hcu.2, T.σ₀, T.toCore.good_σ₀, ?_⟩
    have e : Fin (G.N - 1 + 1) ≃ Fin G.N := finCongr (by omega)
    refine GlobalTheory.BigRec.phRec_of_firstMin D T h j hj T.σ₀ wL G.N (G.N - 1) G.iet G.w e G.et (thR wL) (p14R wL) (DF wL)
      (200000 * zBase large₂ ^ 2) _ T.toCore.good_σ₀ hth (fun σ hσ k x hx => ?_) hZ (fun k x hx => ?_)
    · have h1 := hLow σ hσ k x hx
      rw [← e.sum_comp] at h1
      exact h1
    · have h1 := hA T.σ₀ T.toCore.good_σ₀ k x hx
      rw [lieFac_scalar, one_mul] at h1
      exact h1
  · obtain ⟨w1, hw1, th1, -, hth1, -⟩ := hI1 hjm
    exact ⟨w1, hw1, th1, hth1⟩

end GlobalTheory.RunJoin
end
end

