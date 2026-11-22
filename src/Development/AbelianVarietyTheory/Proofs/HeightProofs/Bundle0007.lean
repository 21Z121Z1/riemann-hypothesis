import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracket
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.Bracket

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

private theorem isLieData_map_pow (H : IsLieData σ j s) (x : 𝔸) (n : ℕ) : σ (x ^ n) = σ x ^ n := by
  induction n with
  | zero => simpa using H.one
  | succ n ih => rw [pow_succ, H.anti, ih, pow_succ']

private theorem isLieData_map_exp (H : IsLieData σ j s) (x : 𝔸) :
    σ (NormedSpace.exp x) = NormedSpace.exp (σ x) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  have := (LinearMap.toContinuousLinearMap σ).map_tsum hs
  simpa [LinearMap.coe_toContinuousLinearMap', map_smul, isLieData_map_pow H] using this

theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hb : ∀ y : 𝔸, y ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := fun y =>
    (NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  rw [isLieData_map_exp H, (H.skew (j X)).2 ⟨X, rfl⟩,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_left (Commute.refl _)) (hb _) (hb _),
    neg_add_cancel, NormedSpace.exp_zero]

omit [FiniteDimensional ℝ 𝔸] in
theorem unitary_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) :
    σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem hasDerivAt_exp (A : 𝔸) : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)

theorem der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ} {a : 𝔸} (ha : σ a * a = 1)
    (hF : DifferentiableAt ℝ F a) (he : ∀ᶠ h in 𝓝 a, σ h * h = 1 → φ (g * s h) = F h) (Y : L) :
    Der (expMap j s) Y φ (g * s a) = fderiv ℝ F a (a * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (a * j Y) 0 :=
    (hasDerivAt_exp (j Y)).const_mul a
  have hc0 : a * NormedSpace.exp ((0 : ℝ) • j Y) = a := by
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j Y)) * NormedSpace.exp (t • j Y) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • Y)
  have hFd : HasFDerivAt F (fderiv ℝ F a) (a * NormedSpace.exp ((0 : ℝ) • j Y)) := by
    rw [hc0]; exact hF.hasFDerivAt
  have hFc := hFd.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have hlim : Filter.Tendsto (fun t : ℝ => a * NormedSpace.exp (t • j Y)) (𝓝 0) (𝓝 a) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have heq : (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (a * NormedSpace.exp (t • j Y))) := by
    filter_upwards [hlim.eventually he] with t ht
    have hm : g * s a * s (NormedSpace.exp (j (t • Y))) = g * s (a * NormedSpace.exp (t • j Y)) := by
      rw [j.map_smul t Y, mul_assoc, ← H.mul a _ ha (hu t)]
    show φ (g * s a * s (NormedSpace.exp (j (t • Y)))) = _
    rw [hm]
    exact ht (unitary_mul H ha (hu t))
  show deriv (fun t : ℝ => φ (g * s a * expMap j s (t • Y))) 0 = _
  exact (hFc.congr_of_eventuallyEq heq).deriv

theorem der_der_eq (H : IsLieData σ j s) {φ : G → ℂ} {g : G} {F : 𝔸 → ℂ}
    (hF : ContDiffAt ℝ 2 F 1) (he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = F h) (X Y : L) :
    Der (expMap j s) X (Der (expMap j s) Y φ) g =
      fderiv ℝ (fderiv ℝ F) 1 (j X) (j Y) + fderiv ℝ F 1 (j X * j Y) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hcd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • j X)) (j X) 0 := hasDerivAt_exp (j X)
  have hc0 : NormedSpace.exp ((0 : ℝ) • j X) = 1 := by rw [zero_smul, NormedSpace.exp_zero]
  have hlim : Filter.Tendsto (fun t : ℝ => NormedSpace.exp (t • j X)) (𝓝 0) (𝓝 1) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hu : ∀ t : ℝ, σ (NormedSpace.exp (t • j X)) * NormedSpace.exp (t • j X) = 1 := fun t => by
    simpa [map_smul] using exp_unitary H (t • X)
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ F) 1 := hF.fderiv_right (by norm_num)
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) 1) (NormedSpace.exp ((0 : ℝ) • j X)) := by
    rw [hc0]; exact (hF1.differentiableAt one_ne_zero).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)))
      (fderiv ℝ (fderiv ℝ F) 1 (j X)) 0 := hA.comp_hasDerivAt (x := (0 : ℝ)) hcd
  have h3 := h1.clm_apply (hcd.mul_const (j Y))
  have hd : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hev : ∀ᶠ y in 𝓝 (1 : 𝔸), DifferentiableAt ℝ F y ∧
      ∀ᶠ h in 𝓝 y, σ h * h = 1 → φ (g * s h) = F h := hd.and he.eventually_nhds
  have heq : (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ F (NormedSpace.exp (t • j X)) (NormedSpace.exp (t • j X) * j Y)) := by
    filter_upwards [hlim.eventually hev] with t ht
    show Der (expMap j s) Y φ (g * s (NormedSpace.exp (j (t • X)))) = _
    rw [j.map_smul t X]
    exact der_eq H (hu t) ht.1 ht.2 Y
  show deriv (fun t : ℝ => Der (expMap j s) Y φ (g * expMap j s (t • X))) 0 = _
  rw [(h3.congr_of_eventuallyEq heq).deriv, hc0, one_mul]

theorem der_bracket : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G),
    IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L,
    j Z = j X * j Y - j Y * j X →
    Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) =
      Der (expMap j s) Z φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ X Y Z hZ
  funext g
  obtain ⟨Λ, hΛ, hΛ1, -⟩ := hl
  have hFs : ContDiffAt ℝ ∞ (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    (hφ g).contDiffAt.comp (1 : 𝔸) hΛ
  have hF2 : ContDiffAt ℝ 2 (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    hFs.of_le (WithTop.coe_le_coe.2 le_top)
  have he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = φ (g * expMap j s (Λ h)) := by
    filter_upwards [hΛ1] with h hh hu
    show φ (g * s h) = φ (g * s (NormedSpace.exp (j (Λ h))))
    rw [hh hu]
  have hs1 : s 1 = 1 := by
    have h11 := H.mul 1 1 (by rw [H.one, one_mul]) (by rw [H.one, one_mul])
    rw [one_mul] at h11
    simpa using h11
  have hZd := der_eq H (a := 1) (g := g) (by rw [H.one, one_mul]) (hF2.differentiableAt two_ne_zero) he Z
  rw [hs1, mul_one, one_mul] at hZd
  have hsym := hF2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [Pi.sub_apply, der_der_eq H hF2 he X Y, der_der_eq H hF2 he Y X, hZd, hZ, map_sub, hsym (j X) (j Y)]
  abel

end GlobalTheory.SmoothForms.Bracket
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.DerLinear

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem anti_exp (H : IsLieData σ j s) (a : 𝔸) : σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let f : 𝔸 →+* 𝔸ᵐᵒᵖ :=
    { toFun := fun b => MulOpposite.op (σ b)
      map_one' := by simp [H.one]
      map_mul' := fun b c => by simp [H.anti]
      map_zero' := by simp
      map_add' := fun b c => by simp }
  have hf : Continuous f := MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)
  have h := NormedSpace.map_exp f hf a
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact h

theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hs : σ (j X) = -j X := (H.skew (j X)).2 ⟨X, rfl⟩
  rw [anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel,
    NormedSpace.exp_zero]

theorem contDiff_exp (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by
  have : FiniteDimensional ℝ L := Module.Finite.of_injective j H.inj
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact hexp.comp (LinearMap.toContinuousLinearMap j).contDiff

omit [FiniteDimensional ℝ 𝔸] in
theorem der_eq_fderiv {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by
  have hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0 :=
    ((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0
  have hd : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X) := by
    rw [zero_smul]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hd).deriv

theorem sm_der (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    Sm (expMap j s) (Der (expMap j s) X φ) := by
  intro g
  have hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1 := exp_unitary H
  let c : L × ℝ → 𝔸 := fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))
  have hcd : ContDiff ℝ ∞ c :=
    ((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hcu : ∀ p, σ (c p) * c p = 1 := by
    intro p
    simp only [c]
    rw [H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]
  have hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0 := fun g => (hφ g).contDiffAt
  have hF := contDiff_family H hl hφ0 hcd hcu g
  have key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) =
      fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ)) := by
    intro Y
    have h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t))) := by
      funext t
      simp only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]
    have hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)
    have hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p)))
        (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0) :=
      ((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt
    show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _
    rw [h1]
    exact (hFd.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp_rw [key]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

end GlobalTheory.SmoothForms.DerLinear

namespace GlobalTheory.SmoothForms

theorem der_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ
  refine ⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩
  · funext g
    rw [Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add]
  · funext g
    rw [Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul,
      smul_eq_mul]

end GlobalTheory.SmoothForms
end

