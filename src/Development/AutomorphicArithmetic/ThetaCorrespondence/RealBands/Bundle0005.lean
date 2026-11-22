import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0097
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FibreIntegralEqZero

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchSmooth
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

open GlobalTheory.SepReal.ProjSm in
theorem UpperTheory.Lit.Branch.mapSmooth :
    MapSmooth := by
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ T hT v hv
  obtain ⟨-, -, -, -, -, -, hlie, hexp, -⟩ := GlobalTheory.T.unitary_stabiliser_embedding_norm_laws n e ε ε' hpar.signs
  intro k Xs hXs
  have key : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (T v)) =
      fun t => T (π ((List.ofFn fun i => NormedSpace.exp (t i • embL e (Xs i))).prod) v) := by
    funext t
    rw [← hT _ (list_mem _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact exp_mem (hXs i) (t i))), embH_list, List.map_ofFn]
    simp only [Function.comp_def, hexp]
  rw [key]
  exact (T.restrictScalars ℝ).contDiff.comp (hv k (fun i => embL e (Xs i)) fun i => hlie _ (hXs i))
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchVol
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

private theorem hsn_le_of_near {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : GlobalTheory.SepReal.hsn (g - 1) ≤ 1 / 4) :
    GlobalTheory.SepReal.hsn g ≤ (n : ℝ) + 1 := by
  have hS : Real.sqrt (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) ≤ 1 / 4 := hg
  have hS0 : 0 ≤ ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2 := by positivity
  have hS2 : ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2 ≤ 1 / 16 := by
    have h := Real.sq_sqrt hS0
    have h0 := Real.sqrt_nonneg (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2)
    nlinarith
  have hent : ∀ a b, ‖g a b‖ ^ 2 ≤ 2 * ‖(g - 1) a b‖ ^ 2 + 2 * (if a = b then (1 : ℝ) else 0) := by
    intro a b
    have hsplit : g a b = (g - 1) a b + (1 : Matrix (Fin n) (Fin n) ℂ) a b := by simp
    have hone : ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖ ^ 2 = if a = b then (1 : ℝ) else 0 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    have htri := norm_add_le ((g - 1) a b) ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
    rw [← hsplit] at htri
    have hp := norm_nonneg (g a b)
    have hq := norm_nonneg ((g - 1) a b)
    have hr := norm_nonneg ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
    rw [← hone]
    nlinarith [sq_nonneg (‖(g - 1) a b‖ - ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖)]
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 ≤ 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n := by
    calc ∑ a, ∑ b, ‖g a b‖ ^ 2
        ≤ ∑ a, ∑ b, (2 * ‖(g - 1) a b‖ ^ 2 + 2 * (if a = b then (1 : ℝ) else 0)) := by
          gcongr with a _ b _
          exact hent a b
      _ = 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
          ring
  show Real.sqrt (∑ a, ∑ b, ‖g a b‖ ^ 2) ≤ (n : ℝ) + 1
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith

private theorem vol_arith (n : ℕ) (B : ℝ) (hn : 3 ≤ n) (hB : 1 ≤ B) :
    (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4 ≤ big 11 n B := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hB1 : 1 ≤ B ^ 2 := by nlinarith
  have hp1 : 1 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := one_le_mul_of_one_le_of_one_le hm1 hB1
  have hmP : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := le_mul_of_one_le_right (by positivity) hB1
  have hqp : (n : ℝ) ^ 2 * B ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := by
    have hB2 : 0 ≤ B ^ 2 := by positivity
    have : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hB2
  have hq0 : 0 ≤ (n : ℝ) ^ 2 * B ^ 2 := by positivity
  have e1 : 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))
      = 512 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) ^ 2 * B ^ 2) := by
    rw [one_div, div_inv_eq_mul]
    ring
  have e2 : (8 * ((n : ℝ) + 1) * B) ^ 4 = 4096 * (((n : ℝ) + 1) ^ 2 * B ^ 2) ^ 2 := by ring
  have hX0 : 0 ≤ 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) := by
    rw [e1]
    positivity
  have hX : 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ≤ (8 * ((n : ℝ) + 1) * B) ^ 4 := by
    rw [e1, e2]
    have := mul_le_mul hmP hqp hq0 (by linarith)
    nlinarith
  have hL4 : (4 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  have hL0 : 0 < 8 * ((n : ℝ) + 1) * B := by linarith
  have hstep : (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4
      ≤ (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1) := by
    calc (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4
        ≤ ((8 * ((n : ℝ) + 1) * B) ^ 4) ^ (2 * n ^ 2) * (8 * ((n : ℝ) + 1) * B) := by
          gcongr
      _ = (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1) := by
          rw [← pow_mul, pow_succ]
          ring_nf
  have hexp : (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1)
      = Real.exp (((8 * n ^ 2 + 1 : ℕ) : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B)) := by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  have hN : ((8 * n ^ 2 + 1 : ℕ) : ℝ) ≤ 11 * ((n : ℝ) + 1) ^ 4 := by
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg (n : ℝ)]
  have hlog : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by linarith)
  unfold big
  calc _ ≤ _ := hstep
    _ = _ := hexp
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hN hlog
      push_cast at this ⊢
      linarith

theorem UpperTheory.Lit.Branch.volDeg :
    VolDeg := by
  have hVol : VolBall := GlobalTheory.T.volume_of_ball_bound
  have hDegU : DegUpper := GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume GlobalTheory.T.unitary_near_identity_eq_exp_log_bound GlobalTheory.T.lowestKType_lieWord_normBound hVol
  refine ⟨11, by norm_num, ?_⟩
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd
  have hn := hP.three_le
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hB1 : 1 ≤ B := RealAsm.one_le_B hP
  have hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3) :=
    RealAsm.gap_mono (by
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith [pow_le_pow_left₀ this (by linarith : (n : ℝ) ≤ n + 1) 3]) hP.gap'
  have hdu := hDegU n ε' mu B hn hP.hmu hgap' hP.bound.2 H' σ hσ d hd
  obtain ⟨-, htop, hvb⟩ := hVol n ε' (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ((n : ℝ) + 1) (by positivity) (by positivity)
  have hsub : nbh ε' (1 / 4) ⊆ {g | GlobalTheory.SepReal.hsn (umat g) ≤ (n : ℝ) + 1} := fun g hg => hsn_le_of_near _ hg
  have h1 := (measure_mono hsub).trans hvb
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hd0 : 0 < d := hd.1
  refine h2.trans ((mul_le_mul_of_nonneg_left hdu (by positivity)).trans ?_)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (vol_arith n B hn hB1) hd0.le
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsMultTEqPoin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

theorem poin_isCuspFun : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := fibre_integral_eq_zero D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).2 _ (hv τ).1) (fun τ => (hv τ).2 _ (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

open Classical in

theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := poin_isCuspFun D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end UpperTheory.Lit.Cusp

end
end

