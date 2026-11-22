import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspace
section
open Matrix

namespace GlobalTheory.CompanionTheory.MidConj

theorem mul_single_one_mul_apply {l m o s : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (A : Matrix l m ℂ) (C : Matrix o s ℂ) (x : m) (y : o) (i : l) (k : s) :
    (A * Matrix.single x y (1 : ℂ) * C) i k = A i x * C y k := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_ite, ite_mul]

theorem conj_units_of_mid (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ)
    (hJJ : Jp * J = 1) (hBB : B * Bi = 1)
    (hJ : ∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j)
    (hout : ∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0)
    (p q : Fin n') :
    J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  let Pm : Matrix (Fin n) (Fin n') ℂ := fun i s => P i ⟨a + s.val, by omega⟩
  have hJm : J = Pm * B := by
    ext i j
    rw [hJ i j]
    rfl
  have hmid : Jp * Pm = Bi := by
    calc Jp * Pm = Jp * Pm * (B * Bi) := by rw [hBB, Matrix.mul_one]
      _ = (Jp * J) * Bi := by rw [hJm]; simp only [Matrix.mul_assoc]
      _ = Bi := by rw [hJJ, Matrix.one_mul]
  have hN_mid : ∀ (q : Fin n') (s : Fin n'), (Jp * P) q ⟨a + s.val, by omega⟩ = Bi q s := by
    intro q s
    calc (Jp * P) q ⟨a + s.val, by omega⟩ = (Jp * Pm) q s := rfl
      _ = Bi q s := by rw [hmid]
  have hN_out : ∀ (q : Fin n') (b : Fin n), (b.val < a ∨ n ≤ b.val + a) → (Jp * P) q b = 0 := by
    intro q b hb
    have h := congrFun (hout b hb) q
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  have hJp : ∀ (q : Fin n') (k : Fin n),
      Jp q k = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
    intro q k
    calc Jp q k = ((Jp * P) * P⁻¹) q k := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ∑ b : Fin n, (Jp * P) q b * P⁻¹ b k := by rw [Matrix.mul_apply]
      _ = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
        symm
        refine Fintype.sum_of_injective (fun u : Fin n' => (⟨a + u.val, by omega⟩ : Fin n)) ?_ _ _ ?_ ?_
        · intro u v huv
          simp only [Fin.mk.injEq] at huv
          exact Fin.ext (by omega)
        · intro b hb
          have hb' : b.val < a ∨ n ≤ b.val + a := by
            by_contra hc
            simp only [not_or, not_lt] at hc
            exact hb (Set.mem_range.mpr ⟨⟨b.val - a, by omega⟩, Fin.ext (show a + (b.val - a) = b.val by omega)⟩)
          rw [hN_out q b hb', zero_mul]
        · intro u
          rw [hN_mid q u]
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_single_one_mul_apply]
  rw [hJ i p, hJp q k, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring

end GlobalTheory.CompanionTheory.MidConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaTendstoLogSubHarmonic
section
open Complex Filter Topology Metric Set
open scoped Nat Real

namespace GlobalTheory.CompanionTheory.DigammaLimit

theorem euler_seq_le_Gamma {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) ≤ Real.Gamma x := by
  have hfe : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp]
    rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have h := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma hfe hx hn
  have hf1 : (Real.log ∘ Real.Gamma) 1 = 0 := by simp [Real.Gamma_one]
  rw [hf1, zero_add] at h
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hP : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) < x + j := fun j _ => by positivity
  have hPpos : 0 < ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) := Finset.prod_pos hP
  have hlog : Real.log ((n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ))) =
      Real.BohrMollerup.logGammaSeq x n := by
    rw [Real.log_div (by positivity) hPpos.ne', Real.log_mul (by positivity) hfac.ne',
      Real.log_rpow hn0, Real.log_prod (fun j hj => (hP j hj).ne')]
    rfl
  rw [← hlog] at h
  exact (Real.log_le_log_iff (by positivity) (Real.Gamma_pos_of_pos hx)).1 h

theorem norm_GammaSeq_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq w n‖ ≤ Real.Gamma w.re := by
  refine le_trans ?_ (euler_seq_le_Gamma hw hn)
  rw [GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    norm_prod, Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (Finset.prod_pos fun j _ => by positivity)
  apply Finset.prod_le_prod (fun j _ => by positivity)
  intro j _
  have := Complex.abs_re_le_norm (w + j)
  simp only [add_re, natCast_re] at this
  exact (le_abs_self _).trans this

theorem add_natCast_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) : z + (j : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [add_re, natCast_re, zero_re] at h1
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  exact add_natCast_ne_zero hz m (by rw [h]; ring)

theorem differentiableAt_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  simp only [GammaSeq]
  refine DifferentiableAt.div ?_ ?_ (Finset.prod_ne_zero_iff.2 hP)
  · exact (differentiableAt_id.const_cpow (Or.inl hn')).mul_const _
  · exact DifferentiableAt.fun_finset_prod fun j _ => by fun_prop

theorem logDeriv_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z =
      ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  have hd1 : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w) ((n : ℂ) ^ z * Complex.log n * 1) z :=
    (hasDerivAt_id z).const_cpow (Or.inl hn')
  have hfac : ((n ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hcp : (n : ℂ) ^ z ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hn']
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z :=
    DifferentiableAt.fun_finset_prod fun j _ => by fun_prop
  have e1 : (fun w => GammaSeq w n) =
      fun w => ((n : ℂ) ^ w * (n ! : ℂ)) / ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) := rfl
  have l1 : logDeriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log n := by
    rw [logDeriv_apply, hd1.deriv]
    field_simp
  have l2 : ∀ j : ℕ, logDeriv (fun w : ℂ => w + (j : ℂ)) z = 1 / (z + (j : ℂ)) := by
    intro j
    rw [logDeriv_apply]
    simp
  rw [e1, logDeriv_div (f := fun w : ℂ => (n : ℂ) ^ w * (n ! : ℂ))
      (g := fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z
      (mul_ne_zero hcp hfac) (Finset.prod_ne_zero_iff.2 hP)
      (hd1.differentiableAt.mul_const _) hd2,
    logDeriv_mul (f := fun w : ℂ => (n : ℂ) ^ w) (g := fun _ : ℂ => (n ! : ℂ)) z hcp hfac
      hd1.differentiableAt (differentiableAt_const _),
    logDeriv_prod (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ)) hP (fun j _ => by fun_prop),
    l1, logDeriv_const, Pi.zero_apply, add_zero, Complex.natCast_log]
  simp only [l2]

theorem tendsto_deriv_GammaSeq {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => deriv (fun w => GammaSeq w n) z) atTop (𝓝 (deriv Gamma z)) := by
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = z.re / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  obtain ⟨U, hU_def⟩ : ∃ U : Set ℂ, U = {w : ℂ | 0 < w.re} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU_def]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hre : ∀ w ∈ closedBall z r, z.re / 2 ≤ w.re ∧ w.re ≤ 3 * z.re / 2 := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hw
    have h2 := Complex.abs_re_le_norm (w - z)
    have h3 : |w.re - z.re| ≤ r := by
      have := h2.trans h1
      simpa only [sub_re] using this
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  have hsub : closedBall z r ⊆ U := fun w hw => by
    have := (hre w hw).1
    rw [hU_def]
    show 0 < w.re
    linarith
  have hGd : DifferentiableOn ℂ Gamma U := fun w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_Gamma w (ne_neg_natCast_of_re_pos hw)).differentiableWithinAt
  have hFd : ∀ n : ℕ, n ≠ 0 → DifferentiableOn ℂ (fun w => GammaSeq w n) U := fun n hn w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_GammaSeq hw hn).differentiableWithinAt
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (z.re / 2) (3 * z.re / 2), ‖Real.Gamma x‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt.continuousWithinAt
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbd : ∀ n : ℕ, n ≠ 0 → ∀ w ∈ closedBall z r, ‖GammaSeq w n‖ ≤ M := by
    intro n hn w hw
    have h1 := hre w hw
    have h0 : 0 < w.re := by linarith [h1.1]
    exact (norm_GammaSeq_le h0 hn).trans ((le_abs_self _).trans (hM _ ⟨h1.1, h1.2⟩))
  have hc : ∀ θ, circleMap z r θ ∈ closedBall z r := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ)
  have key : Tendsto (fun n : ℕ => ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • GammaSeq w n) atTop
      (𝓝 (∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • Gamma w)) := by
    simp only [circleIntegral]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => r * ((r ^ 2)⁻¹ * M)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      apply Continuous.aestronglyMeasurable
      have hcont : Continuous fun θ : ℝ => GammaSeq (circleMap z r θ) n :=
        (hFd n hn).continuousOn.comp_continuous (continuous_circleMap z r)
          (fun θ => hsub (hc θ))
      have h0 : ∀ θ, (circleMap z r θ - z) ^ 2 ≠ 0 := fun θ =>
        pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).mul continuous_const).smul
        (((((continuous_circleMap z r).sub continuous_const).pow 2).inv₀ h0).smul hcont)
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine Eventually.of_forall fun θ _ => ?_
      simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
        Complex.norm_I, norm_inv, norm_pow, abs_of_pos hr, mul_one]
      gcongr
      exact hbd n hn _ (hc θ)
    · refine Eventually.of_forall fun θ _ => ?_
      exact ((GammaSeq_tendsto_Gamma _).const_smul _).const_smul _
  have h2 := key.const_smul ((2 * π * I : ℂ)⁻¹)
  have e : cderiv r Gamma z = deriv Gamma z := cderiv_eq_deriv hUo hGd hr hsub
  rw [← e]
  refine Tendsto.congr' ?_ h2
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact cderiv_eq_deriv hUo (hFd n hn) hr hsub

theorem tendsto_log_sub_sum_digamma : ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z)) := by
  intro z hz
  have h1 := (tendsto_deriv_GammaSeq hz).div (GammaSeq_tendsto_Gamma z)
    (Gamma_ne_zero_of_re_pos hz)
  rw [digamma_def, logDeriv_apply]
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [← logDeriv_GammaSeq hz hn, logDeriv_apply]
  rfl

end GlobalTheory.CompanionTheory.DigammaLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DirichletLogDerivReflectionFormula
section
namespace GlobalTheory.CompanionTheory.ExplChi

open Complex DirichletCharacter

theorem hasDerivAt_Gammaℝ_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt Gammaℝ
      (Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)) z := by
  have hΓ : Gamma (z / 2) ≠ 0 := Gamma_ne_zero hz
  have hd : DifferentiableAt ℂ Gamma (z / 2) := differentiableAt_Gamma _ hz
  have h1 : HasDerivAt (fun w : ℂ => Gamma (w / 2)) (deriv Gamma (z / 2) * (1 / 2)) z :=
    hd.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2)) z :=
    ((hasDerivAt_id z).neg.div_const 2).const_cpow (Or.inl hpi)
  have h3 := h2.mul h1
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) := by
    funext w; rw [Gammaℝ_def]
  have hval : Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2) =
      (Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) * (deriv Gamma (z / 2) * (1 / 2)) := by
    rw [Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  rw [hval, hfun]
  exact h3

theorem Gammaℝ_ne_zero_of_ne {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) : Gammaℝ z ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gammaℝ_def]
  exact mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; exact fun h => hpi h.1) (Gamma_ne_zero hz)

theorem completed_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : N ≠ 1)
    (hχ : χ ≠ 1) {a : ℂ} (ha : χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) {z : ℂ}
    (hz : ∀ n : ℕ, (z + a) / 2 ≠ -(n : ℂ)) (hL : LFunction χ z ≠ 0) :
    completedLFunction χ z ≠ 0 ∧
      deriv (completedLFunction χ) z / completedLFunction χ z =
        -(Real.log Real.pi : ℂ) / 2 + digamma ((z + a) / 2) / 2 +
          deriv (LFunction χ) z / LFunction χ z := by
  have hgf : ∀ w, gammaFactor χ w = Gammaℝ (w + a) := by
    intro w
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · rw [he.gammaFactor_def, add_zero]
    · rw [ho.gammaFactor_def]
  have hG : HasDerivAt (fun w : ℂ => Gammaℝ (w + a)) _ z :=
    (hasDerivAt_Gammaℝ_of_ne hz).comp_add_const z a
  have hGne : Gammaℝ (z + a) ≠ 0 := Gammaℝ_ne_zero_of_ne hz
  have hprod : ∀ w, Gammaℝ (w + a) ≠ 0 →
      completedLFunction χ w = Gammaℝ (w + a) * LFunction χ w := by
    intro w hw
    have h := LFunction_eq_completed_div_gammaFactor χ w (Or.inr hN)
    rw [hgf] at h
    rw [h]
    field_simp
  have hev : completedLFunction χ =ᶠ[nhds z] fun w => Gammaℝ (w + a) * LFunction χ w := by
    filter_upwards [hG.continuousAt.eventually_ne hGne] with w hw using hprod w hw
  have hder : HasDerivAt (fun w => Gammaℝ (w + a) * LFunction χ w) _ z :=
    hG.mul (differentiable_LFunction hχ z).hasDerivAt
  have hne : completedLFunction χ z ≠ 0 := by
    rw [hprod z hGne]; exact mul_ne_zero hGne hL
  refine ⟨hne, ?_⟩
  rw [hev.deriv_eq, hder.deriv, hprod z hGne]
  field_simp

theorem logDeriv_LFunction_functional_equation :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive →
      ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ,
        (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) →
        DirichletCharacter.LFunction χ s ≠ 0 →
        DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 →
        deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
          -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 -
            Complex.digamma ((s + a) / 2) / 2 -
            deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) /
              DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  intro N _ χ hN hp a ha s hs1 hs2 hL1 hL2
  have hN1 : N ≠ 1 := hN.ne'
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [isPrimitive_def, conductor_one] at hp
    exact hN1 hp.symm
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have ha' : χ⁻¹.Even ∧ a = 0 ∨ χ⁻¹.Odd ∧ a = 1 := by
    rcases ha with ⟨he, h⟩ | ⟨ho, h⟩
    · refine Or.inl ⟨?_, h⟩
      rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', he, inv_one]
    · refine Or.inr ⟨?_, h⟩
      rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', ho]
      norm_num
  obtain ⟨A0, eA⟩ := completed_logDeriv χ hN1 hχ ha hs1 hL1
  obtain ⟨B0, eB⟩ := completed_logDeriv χ⁻¹ hN1 hχi ha' hs2 hL2
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set W := rootNumber χ with hW
  have hfe : ∀ w, completedLFunction χ w =
      (N : ℂ) ^ ((1 : ℂ) / 2 - w) * W * completedLFunction χ⁻¹ (1 - w) := by
    intro w
    have h := hp.completedLFunction_one_sub (1 - w)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 3
    ring
  have hc : HasDerivAt (fun w : ℂ => (N : ℂ) ^ ((1 : ℂ) / 2 - w))
      ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1)) s :=
    ((hasDerivAt_id s).const_sub ((1 : ℂ) / 2)).const_cpow (Or.inl hN0)
  have hB : HasDerivAt (fun w : ℂ => completedLFunction χ⁻¹ (1 - w))
      (-deriv (completedLFunction χ⁻¹) (1 - s)) s :=
    ((differentiable_completedLFunction hχi (1 - s)).hasDerivAt).comp_const_sub 1 s
  have hT := (hc.mul_const W).mul hB
  have hD : deriv (completedLFunction χ) s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1) * W * completedLFunction χ⁻¹ (1 - s) +
        (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * (-deriv (completedLFunction χ⁻¹) (1 - s)) := by
    rw [funext hfe]
    exact hT.deriv
  have hA : completedLFunction χ s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * completedLFunction χ⁻¹ (1 - s) := hfe s
  have hcW : (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact A0 hA
  have hlog : deriv (completedLFunction χ) s / completedLFunction χ s =
      -Complex.log N -
        deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s) := by
    have hBB : completedLFunction χ⁻¹ (1 - s) *
        (deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)) =
        deriv (completedLFunction χ⁻¹) (1 - s) := mul_div_cancel₀ _ B0
    rw [hD, hA, div_eq_iff (mul_ne_zero hcW B0)]
    linear_combination ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * W) * hBB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have l1 : ((Real.log (N / Real.pi) : ℝ) : ℂ) = Complex.log N - (Real.log Real.pi : ℂ) := by
    rw [Real.log_div hNpos.ne' Real.pi_ne_zero, ofReal_sub, Complex.ofReal_log hNpos.le,
      ofReal_natCast]
  rw [eA, eB] at hlog
  rw [l1]
  linear_combination hlog

end GlobalTheory.CompanionTheory.ExplChi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoercive
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Glob

theorem finiteDimensional_of_compact_coercive :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c →
        (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  intro H _ _ _ A hA S c hc hS
  have hS' : ∀ u ∈ S.topologicalClosure, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
    intro u hu
    have hcl : IsClosed {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} :=
      isClosed_le (continuous_const.mul (continuous_norm.pow 2))
        (Complex.continuous_re.comp (continuous_id.inner A.continuous))
    have hsub : (S : Set H) ⊆ {u : H | c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re} := fun u hu ↦ hS u hu
    have h := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at h
    exact h hu
  have hbd : ∀ u ∈ S.topologicalClosure, ‖u‖ ≤ c⁻¹ * ‖A u‖ := by
    intro u hu
    have h1 := hS' u hu
    have h2 : (⟪u, A u⟫_ℂ).re ≤ ‖u‖ * ‖A u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : c * ‖u‖ ≤ ‖A u‖ := by
      rcases (norm_nonneg u).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]
        exact norm_nonneg _
      · nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  let T : S.topologicalClosure →L[ℂ] H := A.comp S.topologicalClosure.subtypeL
  have hT : IsCompactOperator T := hA.comp_clm S.topologicalClosure.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T fun x ↦ ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    exact hbd x x.2
  have hemb : Topology.IsClosedEmbedding T := hanti.isClosedEmbedding T.uniformContinuous
  have hK := IsCompactOperator.isCompact_closure_image_closedBall
    (f := (T : S.topologicalClosure →ₗ[ℂ] H)) hT 1
  have hball : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hball
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def LocPrincipal {A : Type} [CommRing A] (I p : Ideal A) : Prop :=
  ∃ t f : A, t ∉ p ∧ f ∈ I ∧ f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}

theorem locPrincipal_span {A : Type} [CommRing A] {f : A} (hf : f ≠ 0) {p : Ideal A} (hp : p ≠ ⊤) :
    LocPrincipal (Ideal.span {f}) p :=
  ⟨1, f, fun h => hp ((Ideal.eq_top_iff_one p).2 h), Ideal.mem_span_singleton_self f, hf,
    fun g hg => ⟨0, by simpa using hg⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminant
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hdvd : P ∣ differentIdeal ℤ (𝓞 E)) :
    (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  by_contra ht
  have hv0 : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
  have hvp : (P.under (𝓞 F)).IsPrime := inferInstance
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hvp, hv0⟩
  have hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P := fun n hn => by
    have : algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P := hn
    simpa [map_natCast] using this
  have hvS : v ∉ S := by
    intro hvS
    apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_left
    have hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm := Finset.dvd_prod_of_mem _ hvS
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))
  have hlies : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := hS v hvS P hP hlies
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hdvd
  rcases (Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h
  · exact not_dvd_differentIdeal_iff.2 hun h
  · apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    apply hcast
    have hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hmap
    rw [← absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _

end GlobalTheory.CompanionTheory.GlobalFiniteness
end

