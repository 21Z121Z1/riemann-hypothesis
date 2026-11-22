import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0220
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevPointwiseBound
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.SupG

theorem norm_cls_sq_eq {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {K : Mat n → V}
    (h : MemLp (fun y : G n => K y.val) 2 μ) :
    ‖cls μ K‖ ^ 2 = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
  have hc : cls μ K = h.toLp _ := dif_pos h
  rw [hc, Lp.norm_toLp, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_unit {n : ℕ} {x : Mat n} (hx : x ∈ GLs n) : ∃ g : G n, g.val = x :=
  ⟨((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit, rfl⟩

theorem sup_sq_bound : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ (S : Finset (List (Bool × Fin n × Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (h : Mat n → V), ContDiffOn ℝ ∞ h (GLs n) → (∀ w, MemLp (fun y : G n => Rw w h y.val) 2 μ) → ∀ x ∈ GLs n, ‖h x‖ ^ 2 ≤ C * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 := by
  intro hS n _ _ μ _
  obtain ⟨S, r, C, hC⟩ := hS n μ
  refine ⟨S, max C 0, le_max_right _ _, fun V _ _ _ h hsm hL x hx => ?_⟩
  obtain ⟨g, rfl⟩ := exists_unit hx
  have h0 := hC V h hsm g.val hx
  have hw : ∀ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ ≤
      ‖cls μ (Rw w h)‖ ^ 2 := by
    intro w _
    set K := Rw w h with hK
    have hm : MemLp (fun y : G n => K y.val) 2 μ := hL w
    have hφ : Integrable (fun y : G n => ‖K y.val‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hm.1).1 hm
    have hψ : Integrable (fun y : G n => ‖K (g.val * y.val)‖ ^ 2) μ := by
      simpa only [Units.val_mul] using hφ.comp_mul_left g
    have e1 : ∫ y : G n, ‖K (g.val * y.val)‖ ^ 2 ∂μ = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
      simpa only [Units.val_mul] using
        integral_mul_left_eq_self (μ := μ) (fun y : G n => ‖K y.val‖ ^ 2) g
    rw [norm_cls_sq_eq hm, ← e1]
    exact setIntegral_le_integral hψ (Filter.Eventually.of_forall fun y => by positivity)
  have hI : 0 ≤ ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
    Finset.sum_nonneg fun w _ => integral_nonneg fun y => by positivity
  calc ‖h g.val‖ ^ 2
      ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ := h0
    _ ≤ max C 0 * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hI
    _ ≤ max C 0 * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_max_right _ _)

end GlobalTheory.CompanionTheory.PresSobA.SupG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem secondCountable_G (n : ℕ) : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

theorem continuous_lg (hL : LgFacts) {n : ℕ} : Continuous (fun y : G n => lg y.val) := by
  have h1 : ContinuousOn (lg (n := n)) (GLs n) := ((hL n).2.2.2.1).continuousOn
  exact h1.comp_continuous Units.continuous_val val_mem_GLs

theorem locallyCompact_G (hL : LgFacts) (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : WeaklyLocallyCompactSpace (G n) := ⟨fun x => ⟨{y : G n | lg y.val ≤ lg x.val + 1},
    (hL n).2.2.2.2.1 _, by
      have : {y : G n | lg y.val < lg x.val + 1} ∈ 𝓝 x :=
        (isOpen_lt (continuous_lg hL) continuous_const).mem_nhds (by simp)
      exact Filter.mem_of_superset this (fun y (hy : lg y.val < _) => show lg y.val ≤ _ from le_of_lt hy)⟩⟩
  infer_instance

theorem sigmaCompact_G (hL : LgFacts) (n : ℕ) : SigmaCompactSpace (G n) := by
  refine ⟨⟨fun k : ℕ => {y : G n | lg y.val ≤ k}, fun k => (hL n).2.2.2.2.1 _, ?_⟩⟩
  ext y
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨k, hk⟩ := exists_nat_ge (lg y.val)
  exact ⟨k, hk⟩

theorem cls_inner {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) :
    ⟪cls μ f, cls μ f'⟫_ℂ = ∫ y : G n, ⟪f y.val, f' y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := by
    unfold cls; exact dif_pos hf
  have e2 : cls μ f' = hf'.toLp _ := by
    unfold cls; exact dif_pos hf'
  rw [e1, e2, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hf'.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem bump_complex {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀) :
    Continuous (fun t => (g t : ℂ)) ∧ HasCompactSupport (fun t => (g t : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp hg.1.continuous, ?_⟩
  refine HasCompactSupport.intro (isCompact_Icc (a := -|T₀|) (b := |T₀|)) (fun t ht => ?_)
  have h1 : |T₀| < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have h2 : g t = 0 := hg.2.2 t (lt_of_le_of_lt (le_abs_self _) h1)
  simp [h2]

theorem phi_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : C₀(ℝ, ℂ) →L[ℂ] (H →L[ℂ] H)) (b : H) (hFc : Fcurve) {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀)
    (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ v : H, ⟪v, Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b⟫_ℂ =
      ∫ t, (g t : ℂ) * ⟪v, Φ (toC0 (wv c N 0 t)) b⟫_ℂ := by
  have hcurve : Continuous (fun t => toC0 (wv c N 0 t)) :=
    continuous_iff_continuousAt.2 fun t =>
      (hFc c N 0 (by omega) t).2.continuousAt
  have hi : Integrable (fun t => (g t : ℂ) • toC0 (wv c N 0 t)) :=
    ((bump_complex hg).1.smul hcurve).integrable_of_hasCompactSupport
      ((bump_complex hg).2.smul_right)
  let L : C₀(ℝ, ℂ) →L[ℂ] H := (ContinuousLinearMap.apply ℂ H b).comp Φ
  have hL : ∀ t, L ((g t : ℂ) • toC0 (wv c N 0 t)) = (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    intro t
    simp [L]
  have hi' : Integrable (fun t => (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b) := by
    simpa only [hL] using L.integrable_comp hi
  have e : Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b = ∫ t, (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    have := L.integral_comp_comm hi
    simp only [hL] at this
    rw [this]
    rfl
  intro v
  rw [e, ← integral_inner hi' v]
  simp only [inner_smul_right]

theorem test_fubini {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hLg : LgFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : ℝ → G n → V} (hW : Continuous (Function.uncurry W)) {Ψ : G n → V} (hΨ : Continuous Ψ)
    (hΨc : HasCompactSupport Ψ) {γ : ℝ → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    ∫ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ ∂μ = ∫ t, γ t * ∫ y, ⟪Ψ y, W t y⟫_ℂ ∂μ := by
  haveI := secondCountable_G n
  haveI := sigmaCompact_G hLg n
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  have h1 : ∀ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ = ∫ t, γ t * ⟪Ψ y, W t y⟫_ℂ := by
    intro y
    have hc : Continuous (fun t => W t y) := hW.comp (by fun_prop : Continuous fun t : ℝ => (t, y))
    have hi : Integrable (fun t => γ t • W t y) :=
      (hγ.smul hc).integrable_of_hasCompactSupport hγc.smul_right
    rw [← integral_inner hi]
    simp only [inner_smul_right]
  simp only [h1]
  have hcont : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) := by
    have h2 : Continuous (fun p : G n × ℝ => W p.2 p.1) :=
      hW.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
    have h3 : Continuous (fun p : G n × ℝ => Ψ p.1) := hΨ.comp continuous_fst
    exact (hγ.comp continuous_snd).mul (h3.inner h2)
  have hint : Integrable (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) (μ.prod volume) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hΨc.isCompact.prod hγc.isCompact) (fun p hp => ?_)
    rcases p with ⟨y, t⟩
    by_cases hy : y ∈ tsupport Ψ
    · have ht : t ∉ tsupport γ := fun ht => hp ⟨hy, ht⟩
      simp [Function.uncurry, image_eq_zero_of_notMem_tsupport ht]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul]

theorem waveInt : WaveInt := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hg N b U hN hW hU f' hf' hcls x hx
  obtain ⟨hLg, -, -, -, -, -, -, hCS, -, hPW, -⟩ := hS
  have hFc : Fcurve := hCS.2.2.1
  haveI := secondCountable_G n
  haveI := locallyCompact_G hLg n
  obtain ⟨hγ, hγc⟩ := bump_complex hg
  set γ : ℝ → ℂ := fun t => (g t : ℂ) with hγdef

  have hUc : Continuous (Function.uncurry fun (t : ℝ) (y : G n) => U t y.val) := by
    have h1 : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hW.1.continuousOn
    exact h1.comp_continuous (f := fun p : ℝ × G n => (p.1, p.2.val))
      (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd))
      (fun p => ⟨trivial, val_mem_GLs _⟩)
  have hfc : Continuous (fun y : G n => f' y.val) :=
    hf'.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hF₁ : Continuous (fun y : G n => ∫ t, γ t • U t y.val) := by
    have hc : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t • U t y.val) := by
      have h2 : Continuous (fun p : G n × ℝ => U p.2 p.1.val) :=
        hUc.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
      exact (hγ.comp continuous_snd).smul h2
    have h3 := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ)) hc hγc.isCompact
    refine h3.congr (fun y => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)
    simp [image_eq_zero_of_notMem_tsupport ht]

  have hMemU : ∀ t, MemLp (fun y : G n => U t y.val) 2 μ := fun t => (hU t).1.2 []
  have hMemf : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  have hcalc := phi_integral F.Φ b hFc hg c hN
  have hpw := (hPW c g T₀ hg).2 N hN
  have test : ∀ ψ : Mat n → E.V, Continuous (fun y : G n => ψ y.val) →
      HasCompactSupport (fun y : G n => ψ y.val) →
      ∫ y : G n, ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪ψ y.val, f' y.val⟫_ℂ ∂μ := by
    intro ψ hψ hψc
    have hMemψ : MemLp (fun y : G n => ψ y.val) 2 μ := hψ.memLp_of_hasCompactSupport hψc
    rw [test_fubini μ hLg hUc hψ hψc hγ hγc, ← cls_inner μ hMemψ hMemf, hcls, ← hpw, hcalc (cls μ ψ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [← (hU t).2, cls_inner μ hMemψ (hMemU t), hγdef]

  have hxu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  obtain ⟨xg, rfl⟩ := hxu
  set Dm : Mat n → E.V := fun y => (∫ t, γ t • U t y) - f' y with hDm
  have hD : Continuous (fun y : G n => Dm y.val) := hF₁.sub hfc
  set bc : G n → ℝ := fun y => max 0 (lg (1 : Mat n) + 1 - lg (xg⁻¹ * y).val) with hbc
  have hbcc : Continuous bc := by
    have h1 : Continuous (fun y : G n => lg (xg⁻¹ * y).val) :=
      (continuous_lg hLg).comp (continuous_const.mul continuous_id)
    exact continuous_const.max (continuous_const.sub h1)
  have hK : IsCompact ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) :=
    ((hLg n).2.2.2.2.1 _).image (continuous_const.mul continuous_id)
  have hbz : ∀ y, y ∉ ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) → bc y = 0 := by
    intro y hy
    have h1 : ¬ lg (xg⁻¹ * y).val ≤ lg (1 : Mat n) + 1 := fun h => hy ⟨xg⁻¹ * y, h, by simp⟩
    simp only [hbc]
    exact max_eq_left (by linarith [not_le.1 h1])
  set ψ : Mat n → E.V := fun y => ((max 0 (lg (1 : Mat n) + 1 - lg ((xg⁻¹ : G n).val * y)) : ℝ) : ℂ) • Dm y with hψdef
  have hψv : ∀ y : G n, ψ y.val = ((bc y : ℝ) : ℂ) • Dm y.val := by
    intro y
    simp only [hψdef, hbc, Units.val_mul]
  have hψ : Continuous (fun y : G n => ψ y.val) := by
    simp only [hψv]
    exact (Complex.continuous_ofReal.comp hbcc).smul hD
  have hψc : HasCompactSupport (fun y : G n => ψ y.val) := by
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hcomp : ∀ {f₁ : G n → E.V}, Continuous f₁ → Integrable (fun y : G n => ⟪ψ y.val, f₁ y⟫_ℂ) μ := by
    intro f₁ h₁
    refine (hψ.inner h₁).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hzero : ∫ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ ∂μ = 0 := by
    have h1 : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ =
        ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ - ⟪ψ y.val, f' y.val⟫_ℂ := fun y => inner_sub_right _ _ _
    simp only [h1]
    rw [integral_sub (hcomp hF₁) (hcomp hfc), test ψ hψ hψc, sub_self]

  set hh : G n → ℝ := fun y => bc y * ‖Dm y.val‖ ^ 2 with hhdef
  have hhc : Continuous hh := hbcc.mul (hD.norm.pow 2)
  have hinn : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ = ((hh y : ℝ) : ℂ) := by
    intro y
    rw [hψv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [hhdef]
  have hhz : ∫ y, hh y ∂μ = 0 := by
    simp only [hinn] at hzero
    rw [integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hhi : Integrable hh μ := by
    refine hhc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hhdef, hbz y hy]
  have hh0 : 0 ≤ hh := fun y => mul_nonneg (le_max_left _ _) (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg hh0 hhi).1 hhz
  have hfun : hh = 0 := (Continuous.ae_eq_iff_eq μ hhc continuous_zero).1 hae
  have hat : hh xg = 0 := congrFun hfun xg
  have hb1 : bc xg = 1 := by
    simp [hbc]
  have hnorm : ‖Dm xg.val‖ = 0 := by
    have : ‖Dm xg.val‖ ^ 2 = 0 := by simpa [hhdef, hb1] using hat
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelComposition
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_smul_integral_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {g g' : ℝ → ℝ} {T T' : ℝ} (hg : IsBump g T) (hg' : IsBump g' T')
    {φ : ℝ → V} (hφ : Continuous φ) :
    ∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, (gconv g g' r : ℂ) • φ r := by
  have cg : Continuous g := hg.1.continuous
  have cg' : Continuous g' := hg'.1.continuous
  let F : ℝ → ℝ → V := fun t r => ((g t * g' (r - t) : ℝ) : ℂ) • φ r
  have hFc : Continuous (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => ((g p.1 * g' (p.2 - p.1) : ℝ) : ℂ) • φ p.2 := rfl
    rw [this]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (-|T|) |T| ×ˢ Set.Icc (-(|T| + |T'|)) (|T| + |T'|))
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨t, r⟩ h
    by_cases ht : T < |t|
    · simp [Function.uncurry, F, hg.2.2 t ht]
    · by_cases hr : T' < |r - t|
      · simp [Function.uncurry, F, hg'.2.2 _ hr]
      · exfalso
        apply h
        have h1 : |t| ≤ |T| := (not_lt.mp ht).trans (le_abs_self T)
        have h2 : |r - t| ≤ |T'| := (not_lt.mp hr).trans (le_abs_self T')
        have h3 : |r| ≤ |t| + |r - t| := by simpa using abs_add_le t (r - t)
        exact ⟨abs_le.mp h1, abs_le.mp (by linarith)⟩
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hL : ∀ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, F t r := by
    intro t
    rw [← integral_add_left_eq_self (fun r => F t r) t, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, add_sub_cancel_left, Complex.ofReal_mul, mul_smul]
  have hR : ∀ r, (gconv g g' r : ℂ) • φ r = ∫ t, F t r := by
    intro r
    simp only [F, gconv]
    rw [integral_smul_const, integral_complex_ofReal]
  simp only [hL, hR]
  exact integral_integral_swap hFi

theorem wave_compose : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V)
    (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' →
    ∃ v : ℝ → Mat n → E.V, IsWave E v ∧
      (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧
      ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x =
        zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  intro hR hS n E u w w' g g' T T' hu hg hg'
  have : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hu' : IsWave E (fun t => zOp w' (u t)) := WaveZ.isWave_zOp hR n E u w' hu
  have hv := WaveAvg.isWave_avg hS n E (fun t => zOp w' (u t)) g' T' hu' hg'
  refine ⟨_, hv, ?_, ?_⟩
  · intro x hx
    have h := ZOpAvg.zOp_avg n u g' T' w' hu.1 hg' x hx
    simp only [zero_add]
    exact h.symm
  · intro x hx
    have hb := isBump_gconv g g' T T' hg hg'
    have hφ : ∀ x' ∈ GLs n, Continuous fun r => zOp w' (u r) x' := fun x' hx' =>
      hu'.1.continuousOn.comp_continuous (f := fun r : ℝ => (r, x')) (by fun_prop)
        (fun r => ⟨trivial, hx'⟩)
    have h1 : ∀ x' ∈ GLs n, (∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • zOp w' (u (t + s)) x') =
        ∫ r, (gconv g g' r : ℂ) • zOp w' (u r) x' := fun x' hx' =>
      integral_smul_integral_shift hg hg' (hφ x' hx')
    rw [zOp_agree_GLs n w _ _ h1 x hx,
      ZOpAvg.zOp_avg n (fun t => zOp w' (u t)) (gconv g g') (T + T') w hu'.1 hb x hx,
      ZOpAvg.zOp_avg n u (gconv g g') (T + T') (w ++ w') hu.1 hb x hx]
    simp only [Swap.zOp_append]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelWordOrderSwap
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerSwap

theorem isKer_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  intro hW hR n _ _ μ _ E w w' g T K hg hK
  refine ⟨hK.1, hK.2.1, hK.2.2.1, fun u hu x hx => ?_⟩
  rw [hK.2.2.2 u hu x hx]
  have hs : ContDiffOn ℝ ∞ (fun x' => ∫ t : ℝ, (g t : ℂ) • u t x') (GLs n) := by
    have h1 := ((GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg hW n E u g T hu hg).2.1 0).1
    simpa only [zero_add] using h1
  exact GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_swap hR n w w' _ hs x hx

end GlobalTheory.CompanionTheory.WaveMult.KerSwap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWaveStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_time_average_is_wave : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | exact GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg <;> assumption)
end

