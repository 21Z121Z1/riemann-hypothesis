import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0069
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0085
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0094
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBoundedStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0078
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0091

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralAuxiliaryCuspFormsSupBound
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaIntegralWeights

theorem auxiliaryWeights_last_entry_pos {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CR CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0) :
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 → w2.LastPos) ∧ ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW → w1.LastPos := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, -, -, h4, -, h6, -, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, hc, -⟩ := hS
  obtain ⟨-, hLP, -⟩ := hL
  obtain ⟨-, hFP, -⟩ := hF

  have key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((Tn : ℤ) + WeightFamilies.dimY D j + 2 ≤ wL.aP τ i) ∧
        (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ i hi
    have hg := hLP τ i
    have hlt : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
    simp only [gapZ, hlt, dif_neg, if_neg, not_false_eq_true] at hg
    have ha : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ) := by
      have := h6 τ i hi
      linarith
    have ha' : 2 * (Tn : ℤ) ^ 2 ≤ (ka.aP τ i : ℤ) := by exact_mod_cast ha
    have k := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities (ka.aP τ i : ℤ) (wL.aP τ i : ℤ) (WeightFamilies.dimY D j : ℤ)
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * (D.R.r : ℤ)) Tn (Tp D j Tn : ℤ)
      (by simp only [Tp]; push_cast; ring) (by positivity) (by exact_mod_cast h40)
      (by exact_mod_cast hc) ha' (by rw [hg])
    simp only [Tp] at k
    push_cast at k
    exact k
  constructor
  · intro w2 hw2 τ i hi
    obtain ⟨-, h2P, -⟩ := hw2
    have e := h2P τ i
    have f := hFP τ i
    obtain ⟨k1, k2⟩ := key τ i hi
    have e' : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i := by exact_mod_cast e
    have : (1 : ℤ) ≤ w2.aP τ i := by nlinarith
    exact_mod_cast this
  · intro w1 hw1 τ i hi
    obtain ⟨-, h1P, -⟩ := hw1
    obtain ⟨k1, -⟩ := key τ i hi
    have : (1 : ℤ) ≤ w1.aP τ i := by rw [h1P τ i]; push_cast; omega
    exact_mod_cast this

theorem familyHypothesesI4_recPJ_of_supBound_thInt : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 16 ≤ D.R.f → (∀ w2, IsG2 wL wF w2 → ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → ThInt (recPJ h j hj) hinj EX w1) → FamilyHypotheses.I4 large₂ (recPJ h j hj) wL wF nW := by
  intro hCI D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR hf hT2 hT1
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, -, hlam, hdim, -⟩ :=
    GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  have hdimR : (1 : ℝ) ≤ WeightFamilies.dimY D j := by exact_mod_cast hdim hj1
  obtain ⟨-, -, hw2, hw1⟩ :=
    GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hP
  obtain ⟨hW2, hW1⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.theta_weight_bounds D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP
  have hLast := auxiliaryWeights_last_entry_pos hP
  obtain ⟨⟨w2, hg2⟩, -⟩ :=
    GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hr2, -, hq2⟩ := hW2 w2 hg2
  obtain ⟨hdf2, hn2, hsz2⟩ := hw2 w2 hg2
  have hpr2 := GlobalTheory.pageRows_of_le D large₂ j ka w2 (by linarith) hdf2 hn2 hR

  set lN := Real.log (Fintype.card (T.U j T.σ₀).Comp) with hlN
  have hN0 : 0 ≤ lN := Real.log_natCast_nonneg _
  have hN : lN ≤ 41 * Zb D large₂ ^ 2 :=
    GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w2 hpr2 hL2 hr2 hf T.σ₀ (Formalism.L2.Pj.Core.good_σ₀ _)
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)
  have hA : 0 ≤ 400 * Zb D large₂ + lamStar D := by linarith
  have hs : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  have hPI : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) =
      5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN := by
    have : (WeightFamilies.dimY D j : ℝ) ≠ 0 := by linarith
    unfold WeightAlgebra.PI4
    field_simp
  have hAs : 0 ≤ (400 * Zb D large₂ + lamStar D) * wL.size := mul_nonneg hA (by linarith)
  refine ⟨400 * Zb D large₂, lN, by nlinarith, by nlinarith, ?_, ?_⟩
  · intro hjm
    obtain ⟨⟨w1, hg1⟩⟩ := (⟨(GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF
      Tn nP nW h0 hP).2⟩ : Nonempty _)
    obtain ⟨hr1, -, hq1⟩ := hW1 hjm w1 hg1
    obtain ⟨hdf1, hn1, hsz1⟩ := hw1 w1 hg1
    have hpr1 := GlobalTheory.pageRows_of_le D large₂ j ka w1 (by linarith) hdf1 hn1 hR
    obtain ⟨th, hth, hnz, hb⟩ :=
      GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w1 hpr1 hL2 hr1 (hLast.2 w1 hg1) hq1 hinj EX (hT1 hjm w1 hg1)
    refine ⟨w1, hg1, th, hth, hnz, fun σ => ?_⟩
    have e : 2 * WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        2 * (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]; ring
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz1 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]
  · obtain ⟨th, hth, hnz, hb⟩ :=
      GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w2 hpr2 hL2 hr2 (hLast.1 w2 hg2) hq2 hinj EX (hT2 w2 hg2)
    refine ⟨w2, hg2, th, hth, hnz, fun σ => ?_⟩
    have e : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz2 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]

end GlobalTheory.ThetaIntegralWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem scalB_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  intro hCI D T h hGam hSh hA hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hHP hRows hSpF hSpF0 hSpK
  obtain ⟨-, hSet, -, -, -⟩ := id hHP
  obtain ⟨hkaN, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hIsL, hIsF, -, -, -, -, -, h40, -, -, -, -⟩ := hSet
  have hLn : wL.n = nW := hIsL.1
  have hkn : ka.n = nP + Tn * nW := hkaN.trans hnV
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    · exact D.host.pde_prime.pos
    · exact D.host.pde'_prime.pos
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hHP
  have hsz := GlobalTheory.T.runScalars_ne_zero_and_log_bounded D (recB h.toLawsCore) hinj EX j p ka wL wF Tn nP nW hp0 (by omega) hLn hIsF hkn
  have hsW := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hWeq := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)

  have hW : ∀ w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w ∧ D.R.r ≤ w.n ∧ w.LastPos := by
    intro w hw
    obtain ⟨hdf, hn, hr, hlast⟩ := hwb.1 w hw
    exact ⟨GlobalTheory.pageRows_of_le D large₂ j ka w (by linarith) hdf hn hRows, hr, hlast⟩

  have hShort : ∀ (w : WeightFamilies.Wt D j) (s : 𝓞 (recB h.toLawsCore).KO) (c : ℝ),
      w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → s ≠ 0 → 0 ≤ c →
      c ≤ 2 * (lamStar D + 2 * Real.log p) * w.size →
      (∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ (s : (recB h.toLawsCore).KO)‖ ≤ c) →
      ShortG (recPJ h j hj) w ((recPJ h j hj).Thc s w) (Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) p * w.size) := by
    intro w s c hw hsp hs hc0 hc hsc
    obtain ⟨hRw, hrw, hlw⟩ := hW w hw
    have hn8 : 0 < w.n := by omega
    obtain ⟨Sh, hSh1, hSh2⟩ := GlobalTheory.T.exists_finite_spanning_short_generators_small_supNorm hCI D T h hGam large₂ j hj w hRw hL2 hrw hlw hSh (hA j hj w.n) hsp
    have hsize : 1 ≤ w.size := WeightFamilies.Wt.one_le_size w
    have key := GlobalTheory.T.shortGenerators_scaled_thetaLattice D _ _ j (recPJ h j hj) w s Sh c (400 * Zb D large₂ * w.size) hs hc0
      (mul_nonneg (by linarith) (by linarith)) hsc hSh1 hSh2
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w p hL2 hn8).2.1
    unfold ShortG at key ⊢
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := key
    exact ⟨S', hS'1, hS'2, fun g hg => (hS'3 g hg).trans (by nlinarith)⟩
  unfold ScalB
  refine ⟨hWeq ▸ hsW.1, hsz.1, hsz.2.1, hsz.2.2.1, fun σ => ?_, p, (Formalism.MainNotions.Gaps.FamilyHypotheses.ownPr_iff D p).1 hp,
    fun σ => hsz.2.2.2 σ, 1009 * Zb D large₂, le_rfl, ?_⟩
  · rw [hWeq]
    exact ⟨(hsW.2 σ).1, (hsW.2 σ).2.1⟩
  unfold S4
  have hsizeL : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hRL, hrL, hlL⟩ := hW wL (by simp)
    have hnL : 0 < wL.n := by omega
    obtain ⟨N, w0, hspan, -, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hCI D T h hGam large₂ j hj wL hRL hL2 hrL hlL
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL p hL2 hnL).2.2
    have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
      rw [Real.log_abs]
      exact Real.log_intCast_nonneg _
    have hb : 0 ≤ 400 * Zb D large₂ * wL.size + 3 * D.R.f * D.R.r * wL.n * large₂.sc.L +
        5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) +
        Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
      have h1 : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ (3 * D.R.f * D.R.r * wL.n : ℝ) * large₂.sc.L := mul_nonneg (by positivity) (by linarith)
      have h3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO :=
        div_nonneg hdisc (by positivity)
      have h4 : 0 ≤ 400 * Zb D large₂ * wL.size := mul_nonneg (by linarith) (by linarith)
      linarith
    exact (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF _ N w0 _ _ _ 0
      (mul_nonneg (by linarith) (by linarith)) hb (fun σ => (hsz.2.2.2 σ).1) hspan hsup hG).1
  · have hsF : ∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sF : (recB h.toLawsCore).KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size :=
      fun σ => (hsz.2.2.2 σ).2.1
    exact hShort wF _ _ (by simp) hSpF hsz.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size wF])) (by nlinarith [WeightFamilies.Wt.one_le_size wF]) hsF
  · exact hShort _ _ _ (by simp) hSpF0 hsz.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ((recPJ h j hj).wF0 wL wF)])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.1)
  · exact hShort ka _ _ (by simp) hSpK hsz.2.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ka])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.2)

end GlobalTheory.RunIn
end

