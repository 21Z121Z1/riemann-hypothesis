import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0057
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0052
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
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0072
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.PageSupportRows
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  first | exact @GlobalTheory.AvgFam.avg_closed | exact GlobalTheory.AvgFam.avg_closed | (intros; apply GlobalTheory.AvgFam.avg_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperatorStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ → (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) → (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) → ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  first | exact @GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | exact GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | (intros; apply GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IInfLeOfCombBound
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem iInf_le_of_combBound {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hjm : D.R.m ≤ j)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨y, hy⟩ := pt_realise h j hj la y0
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hy]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  have h1 := (hX la y).2 hjm
  rw [hd] at h1
  exact h1

theorem combAlg_of_tiedW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (c Gc Prw : ℝ), G.TiedW S Gc Prw → CombBound G S c nus → (j < D.R.m → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ)))) ∧ (j = D.R.m → ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) := by
  intro D T h j hj ka wL wF S nus G c Gc Prw hW hX
  exact ⟨fun hjm => combAlg_of_combBound h j hj hjm G S c nus hW.1 hX,
    fun hjm => iInf_le_of_combBound h j hj hjm.ge G S c nus hW.1 hX⟩

end GlobalTheory.RunJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem three_le_dimY_of_rank (D : D7) (j : ℕ) (hj : InR D j) (hr : 8 ≤ D.R.r) : 3 ≤ WeightFamilies.dimY D j := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  unfold WeightFamilies.dimY
  generalize (D.R.sigW j).1 = a at hs ⊢
  generalize (D.R.sigW j).2 = b at hs ⊢
  have key : ∀ c : ℕ, 3 ≤ c → 3 ≤ c * (c - 1) / 2 := fun c hc => by
    have : 3 * 2 ≤ c * (c - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have h3 : 3 ≤ a * b + a * (a - 1) / 2 + b * (b - 1) / 2 := by
    rcases le_or_gt 3 a with h | h
    · have := key a h; omega
    · have := key b (by omega); omega
  calc 3 = 1 * 3 := rfl
    _ ≤ _ := Nat.mul_le_mul hf h3

theorem DF_add_one_le_size {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) + 1 ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  push_cast at h2 ⊢
  linarith

theorem lamConst_lamR_rows : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 CL N del hj hP hCL hN hdel hlN hld
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    exact Nat.succ_le_of_lt (by positivity)
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hPO : 1 ≤ PO D large₂ := by
    unfold PO
    have h1 : 0 ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * large₂.sc.L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hL
    nlinarith
  obtain ⟨-, hS, h3, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIL, -, -, -, -, h40, -, h22, -⟩ := hS
  obtain ⟨-, -, -, hc, -⟩ := h3
  obtain ⟨-, -, t1, t2, t3, -⟩ := hP.tie
  rw [t1, t2, t3] at hc
  have hdf : (3 : ℝ) ≤ DF wL := by exact_mod_cast hP.df
  have hsz := DF_add_one_le_size wL
  have hn : wL.n = nW := hIL.1
  refine ⟨?_, three_le_dimY_of_rank D j hj hP.r8, hn, by omega, by linarith, by linarith, hPO,
    WeightFamilies.one_le_zBase large₂, ?_, le_max_right _ _⟩
  · set n : ℕ := 8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊) with hndef
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (by rw [hndef]; positivity)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs1 : (wsmul n wL).size ≤ (n : ℝ) * wL.size :=
      GlobalTheory.RunWeights.size_le_mul _ _ n hn1 (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl
    have hs0 : 1 ≤ (wsmul n wL).size := by
      have := DF_add_one_le_size (wsmul n wL)
      have h0 : (0 : ℝ) ≤ DF (wsmul n wL) := Nat.cast_nonneg _
      linarith
    have hP0 : 0 ≤ WeightFamilies.PP0v D large₂ CL 2 := by
      unfold WeightFamilies.PP0v
      rw [Real.rpow_two]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdel' : (0 : ℝ) < del := by exact_mod_cast hdel
    have hceil : (1 : ℝ) + (⌈PO D large₂⌉₊ : ℝ) ≤ 2 + PO D large₂ := by
      have := Nat.ceil_lt_add_one (a := PO D large₂) (by linarith)
      linarith
    have hd0 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) * (N : ℝ) ^ 2 * del := by
      rw [hndef]
      push_cast
      calc 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 1) * del * (1 + (⌈PO D large₂⌉₊ : ℝ))
          ≤ 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 2) * del * (2 + PO D large₂) := by
            gcongr; norm_num
        _ = _ := by ring
    have hA : (0 : ℝ) < 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) := by positivity
    have hlogn := Real.log_le_log (by linarith) hnle
    rw [Real.log_mul (by positivity) hdel'.ne', Real.log_mul hA.ne' (by positivity), Real.log_pow] at hlogn
    push_cast at hlogn
    have hlogs := Real.log_le_log (by linarith) hs1
    rw [Real.log_mul (by linarith) (by linarith)] at hlogs
    have hl0 : 0 ≤ Real.log (wsmul n wL).size := Real.log_nonneg hs0
    have hmain : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (wsmul n wL).size) ≤ lamR large₂ CL wL := by
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hP0
    have hlam : 0 ≤ lamR large₂ CL wL := le_trans zero_le_one (le_max_left _ _)
    unfold LamConst
    rw [mul_assoc (lamR large₂ CL wL)]
    exact mul_le_mul hmain hs1 (by linarith) hlam
  · have hT : (2 : ℝ) ≤ Tn := by
      have : 2 ≤ Tn := by omega
      exact_mod_cast this
    rw [mul_assoc] at hc
    by_contra hcon
    push Not at hcon
    nlinarith

end GlobalTheory.RunJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PageOKRun
section
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.Inh
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin GlobalTheory.Survey.NumericBoundConstants

theorem nums {A k b s PP TO rd r d q fm : ℝ} (h : Bs A k b s PP TO rd) (hr0 : 0 ≤ r) (hr : r ≤ A) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ q ∧ TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 ≤ q ∧
      2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ q := by
  have hs : (10 : ℝ) ^ 100 ≤ s := h.sb_ge
  have hs1 : (40000 : ℝ) ≤ s := le_trans (by norm_num) hs
  have hk : (1 : ℝ) ≤ k := by linarith [h.k8]
  have hR : rd ^ 7 ≤ s := h.rd_pow_le (by norm_num)
  have hR0 : 0 ≤ rd ^ 7 := by have := h.rd1; positivity
  have hP0 : 0 ≤ PP := le_trans (by positivity) h.PP_ge
  have hP := h.PP_le_sb
  have hP3 := h.param_cube_le_bound
  have hTP := h.hTP
  have hT0 : 0 ≤ TO := by linarith [h.one_le_order_alt]
  have hb : b = s ^ 2 := by rw [← h.sb_sq]; ring
  have hd' : d ≤ 4 * k ^ 2 * s ^ 2 := by
    have := h.Ak
    rw [hb] at hd
    have : A * s ^ 2 ≤ 2 * k ^ 2 * s ^ 2 := by gcongr
    linarith
  have hq' : k ^ 8 * s ^ 16 ≤ q := by rw [hb] at hq; calc k ^ 8 * s ^ 16 = (k * s ^ 2) ^ 8 := by ring
    _ ≤ q := hq
  have hr' : r ≤ 2 * k ^ 2 := hr.trans h.Ak
  have key : ∀ (a c : ℕ) (C : ℝ), a ≤ 8 → c ≤ 15 → 0 ≤ C → C ≤ 40000 → C * (k ^ a * s ^ c) ≤ q := by
    intro a c C ha hc hC0 hC
    have e1 : k ^ a ≤ k ^ 8 := pow_le_pow_right₀ hk ha
    have e2 : s ^ c ≤ s ^ 15 := pow_le_pow_right₀ (by linarith) hc
    calc C * (k ^ a * s ^ c) ≤ s * (k ^ 8 * s ^ 15) := by gcongr; linarith
      _ = k ^ 8 * s ^ 16 := by ring
      _ ≤ q := hq'
  refine ⟨?_, ?_, ?_⟩
  · calc (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ s ^ 4 * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 16 * (k ^ 4 * s ^ 9) := by ring
      _ ≤ q := key 4 9 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 = (TO * PP) * (1250 * r) * rd ^ 7 * d ^ 2 := by ring
      _ ≤ s * (1250 * (2 * k ^ 2)) * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 40000 * (k ^ 6 * s ^ 6) := by ring
      _ ≤ q := key 6 6 40000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc 2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ 2 * (k ^ 4 * s ^ 2 * (s * s * (4 * k ^ 2 * s ^ 2) ^ 2)) := by gcongr
      _ = 32 * (k ^ 8 * s ^ 8) := by ring
      _ ≤ q := key 8 8 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem eRR7 : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
  unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7

end GlobalTheory.RunJoin.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonSectionsOfNoLeadingTerm
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
end

