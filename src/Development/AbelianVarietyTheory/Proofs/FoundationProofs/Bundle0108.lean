import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_one' (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  simp

theorem minor_one' {n : ℕ} (m : Fin n) : minor (1 : GL (Fin n) k) m = 1 := by
  unfold minor
  simp [Matrix.toSquareBlockProp]

theorem continuous_minor' {n : ℕ} (m : Fin n) : Continuous fun g : GL (Fin n) k => minor g m := by
  unfold minor
  exact (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem ev_eventually_one (χ : kˣ →* ℂˣ) (S : Set k) (hS : S ∈ nhds (0 : k)) (hT : ∀ x ∈ S, Triv χ x) :
    ∀ᶠ x in nhds (1 : k), ev χ x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := triv_ev_props k
  have hball : {x : k | valuation k (x - 1) < 1} ∈ nhds (1 : k) :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_of_mem one_ne_zero
  have hpre : (fun x : k => x - 1) ⁻¹' S ∈ nhds (1 : k) :=
    (continuous_sub_right (1 : k)).continuousAt.preimage_mem_nhds (by simpa using hS)
  filter_upwards [hball, hpre] with x hx hxS
  have hv : valuation k x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hx
  rw [h8 χ x 1 hv (by simp) (hT _ hxS), ev_one']

theorem theta_one_and_near : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) →
    theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  intro k _ _ _ _ n ψ hψ
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := triv_ev_props k
  have hset : ∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → {x : k | Triv χ x} ∈ nhds (0 : k) := fun χ hχ =>
    (h6 χ hχ).1.mem_nhds (h3 χ)
  have hnxt : ∀ m, {x : k | Triv (nxt ψ m) x} ∈ nhds (0 : k) := by
    intro m
    unfold nxt
    split_ifs with h
    · exact hset _ (hψ _)
    · refine Filter.univ_mem' fun x => ?_
      intro u _ _
      rfl
  have hev : ∀ m, ∀ᶠ x in nhds (1 : k), ev (ψ m / nxt ψ m) x = 1 := fun m =>
    ev_eventually_one _ _ (Filter.inter_mem (hset _ (hψ m)) (hnxt m)) fun x hx => by
      rw [div_eq_mul_inv]
      exact h4 _ _ x hx.1 (h5 _ x hx.2)
  refine ⟨?_, ?_⟩
  · unfold theta
    exact Finset.prod_eq_one fun m _ => by rw [minor_one', ev_one']
  · have hall : ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ m, ev (ψ m / nxt ψ m) (minor g m) = 1 := by
      rw [Filter.eventually_all]
      intro m
      have hc := (continuous_minor' (k := k) m).continuousAt (x := 1)
      rw [ContinuousAt, minor_one'] at hc
      exact hc.eventually (hev m)
    exact ⟨_, hall, fun g hg => Finset.prod_eq_one fun m _ => hg m⟩

end

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsCompUpperTriangular
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNQ

theorem qAll_affine : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  intro E N a d b f hE hN ha hd hf
  obtain ⟨c, hc, hcE⟩ := hf
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let e : ℕ → ℂ := fun k => Complex.exp (2 * Real.pi * Complex.I * (((k : ℚ) * b / (N * d) : ℚ) : ℂ))
  refine ⟨fun m => if a ∣ m then c (m / a) * e (m / a) else 0, ?_, ?_⟩
  · intro τ
    have hz : 0 < (((a : ℂ) * τ + b) / d).im := by
      have : (((a : ℂ) * τ + b) / d).im = a * τ.im / d := by
        simp [Complex.div_ofReal_im]
      rw [this]; have := τ.im_pos; positivity
    have hτ := hc (UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hτ
    simp only [UpperHalfPlane.coe_mk_subtype] at hτ
    have hinj : Function.Injective (fun k : ℕ => a * k) := fun x y h => by
      simpa [ha.ne'] using h
    rw [← hinj.hasSum_iff]
    · show HasSum (fun k => _) (f _)
      convert hτ using 1
      funext k
      simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left k ha, e]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
      exact congrArg f (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    · intro m hm
      have : ¬ a ∣ m := by
        rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩
      simp [this]
  · intro m
    by_cases h : a ∣ m
    · simp only [h, if_true]
      exact E.mul_mem (hcE _) (hE _)
    · simp only [h, if_false]; exact E.zero_mem

end GlobalTheory.FNQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory

theorem norm_root_monic_le (n : ℕ) (s : Fin n → ℂ) (y : ℂ)
    (hy : y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0) : ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖y‖ ≤ 1
  · linarith
  push_neg at h1
  cases n with
  | zero => simp at hy
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hy
    have hle : ‖y‖ ^ (m + 1) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      calc ‖y‖ ^ (m + 1) = ‖y ^ (m + 1)‖ := (norm_pow _ _).symm
        _ = ‖∑ j, s j * y ^ (j : ℕ)‖ := by rw [hyn, norm_neg]
        _ ≤ ∑ j, ‖s j * y ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ m := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          gcongr
          · exact h1.le
          · exact Nat.lt_succ_iff.1 j.isLt
        _ = (∑ j, ‖s j‖) * ‖y‖ ^ m := by rw [Finset.sum_mul]
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) _
    rw [pow_succ] at hle
    have : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith
    linarith

end GlobalTheory

namespace GlobalTheory

theorem quotient_integral_holomorphic : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  intro U n A D s hU hUc hA hD hs ⟨z₁, hz₁U, hz₁⟩ heq
  classical
  have hiso : ∀ z₀ ∈ U, ∀ᶠ w in 𝓝[≠] z₀, D w ≠ 0 := by
    intro z₀ hz₀
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    have := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hcon
    exact hz₁ (this hz₁U)
  have hroot : ∀ w ∈ U, D w ≠ 0 → (A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ) = 0 := by
    intro w hw hDw
    have hDn : D w ^ n ≠ 0 := pow_ne_zero _ hDw
    have key : D w ^ n * ((A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ))
        = A w ^ n + ∑ j, s j w * A w ^ (j : ℕ) * D w ^ (n - j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [div_pow, mul_div_cancel₀ _ hDn]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) ≤ n := j.isLt.le
        have hsplit : D w ^ n = D w ^ (j : ℕ) * D w ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
        rw [hsplit, div_pow]
        field_simp
    have := heq w hw
    rw [← key] at this
    exact (mul_eq_zero.1 this).resolve_left hDn
  have hAz : ∀ w ∈ U, D w = 0 → A w = 0 := by
    intro w hw hDw
    have := heq w hw
    have hsum : ∑ j : Fin n, s j w * A w ^ (j : ℕ) * D w ^ (n - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      rw [hDw, zero_pow (by omega : n - (j : ℕ) ≠ 0), mul_zero]
    rw [hsum, add_zero] at this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at this
    · exact (pow_eq_zero_iff hn.ne').1 this
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, ∀ z, h z =
      if D z = 0 then limUnder (𝓝[≠] z) (fun w => A w / D w) else A z / D z := ⟨_, fun z => rfl⟩
  have hdiffAt : ∀ z₀ ∈ U, DifferentiableAt ℂ h z₀ := by
    intro z₀ hz₀
    have hUn : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
    by_cases hDz : D z₀ = 0
    · have h1 : ∀ᶠ w in 𝓝 z₀, w ∈ U := hUn
      have h2 : ∀ᶠ w in 𝓝 z₀, w ≠ z₀ → D w ≠ 0 := eventually_nhdsWithin_iff.1 (hiso z₀ hz₀)
      have h3 : ∀ᶠ w in 𝓝 z₀, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := by
        rw [Filter.eventually_all]
        intro j
        have hc : ContinuousAt (fun w => ‖s j w‖) z₀ :=
          ((hs j).differentiableAt hUn).continuousAt.norm
        exact hc.eventually (Iio_mem_nhds (lt_add_one _))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
      have hsub : ∀ w ∈ Metric.ball z₀ r, w ∈ U := fun w hw => (hball w hw).1
      have hne : ∀ w ∈ Metric.ball z₀ r, w ≠ z₀ → D w ≠ 0 := fun w hw => (hball w hw).2.1
      have hsb : ∀ w ∈ Metric.ball z₀ r, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := fun w hw => (hball w hw).2.2
      have hfd : DifferentiableOn ℂ (fun w => A w / D w) (Metric.ball z₀ r \ {z₀}) := by
        intro w hw
        have hwU : U ∈ 𝓝 w := hU.mem_nhds (hsub w hw.1)
        exact ((hA.differentiableAt hwU).div (hD.differentiableAt hwU)
          (hne w hw.1 hw.2)).differentiableWithinAt
      have hbd : BddAbove (norm ∘ (fun w => A w / D w) '' (Metric.ball z₀ r \ {z₀})) := by
        refine ⟨1 + ∑ j, (‖s j z₀‖ + 1), ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have := GlobalTheory.norm_root_monic_le n (fun j => s j w) (A w / D w) (hroot w (hsub w hw.1) (hne w hw.1 hw.2))
        show ‖A w / D w‖ ≤ _
        refine this.trans ?_
        gcongr with j
        exact (hsb w hw.1 j).le
      have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds z₀ hr) hfd hbd
      have heqg : h =ᶠ[𝓝 z₀] Function.update (fun w => A w / D w) z₀
          (limUnder (𝓝[≠] z₀) (fun w => A w / D w)) := by
        filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
        by_cases hw0 : w = z₀
        · subst hw0; rw [hh, if_pos hDz, Function.update_self]
        · rw [hh, if_neg (hne w hw hw0), Function.update_of_ne hw0]
      exact (hg.differentiableAt (Metric.ball_mem_nhds z₀ hr)).congr_of_eventuallyEq heqg
    · have hDc : ContinuousAt D z₀ := (hD.differentiableAt hUn).continuousAt
      have heqf : h =ᶠ[𝓝 z₀] fun w => A w / D w := by
        filter_upwards [hDc.eventually_ne hDz] with w hw
        rw [hh, if_neg hw]
      exact ((hA.differentiableAt hUn).div (hD.differentiableAt hUn) hDz).congr_of_eventuallyEq heqf
  refine ⟨h, fun z hz => (hdiffAt z hz).differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    by_cases hDz : D z = 0
    · rw [hDz, mul_zero]; exact hAz z hz hDz
    · rw [hh, if_neg hDz, div_mul_cancel₀ _ hDz]
  · intro z hz
    by_cases hDz : D z = 0
    · have hUn : U ∈ 𝓝 z := hU.mem_nhds hz
      have hFd : DifferentiableAt ℂ (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) z := by
        apply ((hdiffAt z hz).pow n).add
        have hsum := DifferentiableAt.sum (u := Finset.univ)
          (A := fun (j : Fin n) (w : ℂ) => s j w * h w ^ (j : ℕ))
          (fun j _ => ((hs j).differentiableAt hUn).mul ((hdiffAt z hz).pow _))
        convert hsum using 1
        ext w
        simp [Finset.sum_apply]
      have hev : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ j, s j w * h w ^ (j : ℕ) = 0 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds hUn] with w hw hwU
        rw [hh, if_neg hw]
        exact hroot w hwU hw
      have ht : Tendsto (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) (𝓝[≠] z) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique (hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
    · rw [hh, if_neg hDz]
      exact hroot z hz hDz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueAlgebraicPolynomialDivisible
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_int_poly_root_mod_p : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt p x) → v (p : Ωl) < 1 → ∀ (y : Ωl) (b : O0 p), IsAlgebraic ℤ y → v y ≤ 1 → v (y - algebraMap (O0 p) Ωl b) < 1 → ∃ P : ℤ[X], P.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ (p : O0 p) ∣ aeval b P := by
  intro p hpf Ωl _ _ hC v hv _ y b hy hyv hyb
  haveI : CharZero Ωl := Basic.charZero_of_isClo hC
  obtain ⟨P0, hP0, hP0y⟩ := hy
  have hprim : P0.primPart.IsPrimitive := Polynomial.isPrimitive_primPart P0
  have hPy : aeval y P0.primPart = 0 := by
    have e := P0.eq_C_content_mul_primPart
    have hc : P0.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
    rw [e, map_mul, aeval_C] at hP0y
    rcases mul_eq_zero.1 hP0y with h | h
    · exact absurd (by simpa using h) hc
    · exact h
  refine ⟨P0.primPart, ?_, ?_⟩
  · intro h0
    have hd : ∀ n, (p : ℤ) ∣ P0.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    have hu := hprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).2 hd)
    have := Int.isUnit_iff.1 hu
    have h2 := hpf.out.two_le
    omega
  · set P := P0.primPart
    set b' := algebraMap (O0 p) Ωl b
    have hb' : v b' ≤ 1 := (hv b').2 isIntegral_algebraMap
    let yi : v.integer := ⟨y, hyv⟩
    let bi : v.integer := ⟨b', hb'⟩
    obtain ⟨d, hd⟩ := Polynomial.sub_dvd_eval_sub yi bi (P.map (Int.castRingHom v.integer))
    have hev : ∀ z : v.integer, v.integer.subtype ((P.map (Int.castRingHom v.integer)).eval z) = aeval (z : Ωl) P := by
      intro z
      rw [Polynomial.eval_map, aeval_def]
      have := Polynomial.hom_eval₂ P (Int.castRingHom v.integer) v.integer.subtype z
      rw [show v.integer.subtype.comp (Int.castRingHom v.integer) = algebraMap ℤ Ωl from RingHom.ext_int _ _] at this
      exact this
    have hd' := congrArg v.integer.subtype hd
    rw [map_sub, map_mul, map_sub, hev, hev] at hd'
    have hd'' : aeval y P - aeval b' P = (y - b') * (d : Ωl) := hd'
    have hkey : aeval b' P = -((y - b') * (d : Ωl)) := by
      rw [← hd'', hPy]; ring
    have hmap : algebraMap (O0 p) Ωl (aeval b P) = aeval b' P := by
      rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_int _ _
    have hlt : v (algebraMap (O0 p) Ωl (aeval b P)) < 1 := by
      rw [hmap, hkey, Valuation.map_neg, Valuation.map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hyb d.2
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have hnu : ¬ IsUnit (aeval b P) := by
      rintro ⟨u, hu⟩
      have h1 : v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) ≤ 1 := (hv _).2 isIntegral_algebraMap
      have h2 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, Valuation.map_one]
      have h3 : v (algebraMap (O0 p) Ωl (aeval b P)) * v (algebraMap (O0 p) Ωl (u⁻¹ : (O0 p)ˣ)) < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt h1
      rw [h2] at h3
      exact lt_irrefl _ h3
    have hm : aeval b P ∈ IsLocalRing.maximalIdeal (O0 p) := hnu
    rw [hmax, Ideal.mem_span_singleton] at hm
    exact hm

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleHeckePolyTransportRingEquiv
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.Transport

variable {R S : Type} [CommRing R] [CommRing S]

def mapF (φ : R →+* S) (F : ℂ → MvPolynomial (Fin 2) R) : ℂ → MvPolynomial (Fin 2) S :=
  fun z => MvPolynomial.map φ (F z)

theorem map_smul' (φ : R →+* S) (c : R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (c • p) = φ c • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_slP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (slP m p) = slP m (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, Betti.slP_X, MvPolynomial.map_X, map_add, map_smul', map_intCast]

theorem mapF_add (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F + G) = mapF φ F + mapF φ G := by
  funext z; simp [mapF]

theorem mapF_sub (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F - G) = mapF φ F - mapF φ G := by
  funext z; simp [mapF]

theorem mapF_smul (φ : R →+* S) (c : R) (F : ℂ → MvPolynomial (Fin 2) R) : mapF φ (c • F) = φ c • mapF φ F := by
  funext z; simp [mapF, map_smul']

theorem mapF_sum {ι : Type} (φ : R →+* S) (s : Finset ι) (F : ι → ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (∑ j ∈ s, F j) = ∑ j ∈ s, mapF φ (F j) := by
  funext z; simp [mapF, Finset.sum_apply, map_sum]

theorem mapF_opP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opP R m F) = opP S m (mapF φ F) := by
  funext z; simp [mapF, opP, map_slP]

theorem mapF_opL (φ : R →+* S) (N l : ℕ) (T : Letter) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opL R N l T F) = opL S N l T (mapF φ F) := by
  cases T with
  | T q => simp only [opL, LinearMap.add_apply, LinearMap.sum_apply, mapF_add, mapF_sum, mapF_opP]
  | U => simp only [opL, LinearMap.sum_apply, mapF_sum, mapF_opP]
  | D d => simp only [opL, mapF_opP]

theorem mapF_mem_pot (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Pot R w Γ) : mapF φ F ∈ Pot S w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map φ, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map φ p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, map_slP]; rfl

theorem mapF_mem_triv (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Triv R w Γ) : mapF φ F ∈ Triv S w Γ := by
  obtain ⟨ψ, p, h1, h2⟩ := hF
  refine ⟨mapF φ ψ, MvPolynomial.map φ p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
  · simp only [mapF]; rw [← map_slP, h1 γ hγ z hz]
  · simp only [mapF]; rw [h2 z hz, map_add]

theorem exists_preimage (ι : R ≃+* S) (N l : ℕ) (lam : Letter → R) {P : FreeAlgebra S Letter} (hP : P ∈ admissibleLettersSubalgebra S N l) :
    ∃ Q ∈ admissibleLettersSubalgebra R N l, ι (FreeAlgebra.lift R lam Q) = FreeAlgebra.lift S (fun T => ι (lam T)) P ∧
      ∀ F, mapF (ι : R →+* S) (FreeAlgebra.lift R (opL R N l) Q F) =
        FreeAlgebra.lift S (opL S N l) P (mapF (ι : R →+* S) F) := by
  unfold admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact ⟨FreeAlgebra.ι R T, Algebra.subset_adjoin ⟨T, hT, rfl⟩, by simp, fun F => by simp [mapF_opL]⟩
  | algebraMap r =>
    refine ⟨algebraMap R _ (ι.symm r), Subalgebra.algebraMap_mem _ _, by simp, fun F => ?_⟩
    simp [Module.algebraMap_end_apply, mapF_smul]
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q + Q', add_mem hQ hQ', by simp [h1, h1'], fun F => by simp [mapF_add, h2, h2']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q * Q', mul_mem hQ hQ', by simp [h1, h1'], fun F => by simp [h2, h2']⟩

theorem mapF_symm_mapF (ι : R ≃+* S) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF (ι.symm : S →+* R) (mapF (ι : R →+* S) F) = F := by
  funext z
  simp only [mapF, MvPolynomial.map_map]
  rw [RingEquiv.symm_comp, MvPolynomial.map_id]

end GlobalTheory.KZ.Transport

open GlobalTheory.KZ.Transport in

theorem GlobalTheory.KZ.ssPot_transport : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E),
    SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧
      ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T →
        (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  intro N l w E _ ι lam ⟨P, hP, h1, h2⟩
  obtain ⟨Q, hQ, e1, e2⟩ := exists_preimage ι N l lam hP
  refine ⟨Q, hQ, ι.injective (by rw [e1, h1, map_one]), fun F hF T hT => ?_⟩
  have h := mapF_mem_triv (ι.symm : ℂ →+* E) (h2 _ (mapF_mem_pot (ι : E →+* ℂ) hF) T hT)
  rw [← e2] at h
  rw [← mapF_symm_mapF ι ((opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) Q F))]
  convert h using 2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, mapF_sub, mapF_smul, mapF_opL]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupCharacterIdempotent_properties : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  first | exact @GlobalTheory.BadShare.EpsProj.eps_spec | exact GlobalTheory.BadShare.EpsProj.eps_spec | (intros; apply GlobalTheory.BadShare.EpsProj.eps_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevelStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGaloisAction_preserves_gammaLevel : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  first | exact @GlobalTheory.Tower.gal_level | exact GlobalTheory.Tower.gal_level | (intros; apply GlobalTheory.Tower.gal_level <;> assumption)
end

