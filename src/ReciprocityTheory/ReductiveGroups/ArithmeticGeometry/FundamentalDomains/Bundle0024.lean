import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0021

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientIndexLowerBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private lemma card_le_sum_of_one_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (h1 : 1 ≤ ∏ i, z i) : (Fintype.card ι : ℝ) ≤ ∑ i, z i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) z
    (fun i _ => by positivity) hw (fun i _ => (hz i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hz i).le), ← Finset.mul_sum] at key
  have h2 : 1 ≤ (∏ i, z i) ^ (1 / (Fintype.card ι : ℝ)) := Real.one_le_rpow h1 (by positivity)
  have h3 := h2.trans key
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hn] at h3
  linarith

private lemma prod_le_one_of_sum_le_card {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hs : ∑ i, v i ≤ Fintype.card ι) : ∏ i, v i ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) v
    (fun i _ => by positivity) hw (fun i _ => (hv i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hv i).le), ← Finset.mul_sum] at key
  have h3 : 1 / (Fintype.card ι : ℝ) * ∑ i, v i ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ hn]; linarith
  by_contra hgt
  push_neg at hgt
  have := Real.one_lt_rpow hgt (by positivity : (0 : ℝ) < 1 / (Fintype.card ι : ℝ))
  linarith

private lemma card_sq_div_le_two_mul_sum_of_bounds {ι : Type} [Fintype ι] [Nonempty ι] (d ν A R : ι → ℝ) (N NC k0 c1 ε : ℝ)
    (hN : 0 < N) (hNC : 0 < NC) (hk0 : 0 < k0) (hk2 : k0 ≤ 2) (hε : 0 < ε) (hc1 : 0 < c1)
    (hd : ∀ i, 0 < d i) (hν : ∀ i, 0 < ν i) (hνs : ∑ i, ν i ≤ c1)
    (hprod : 1 ≤ ∏ i, (N ^ 2 * d i))
    (hA : ∀ i, 1 / (NC ^ 2 * k0 * ε) ≤ A i)
    (hq : ∀ i, d i * A i ≤ ν i * R i) :
    (Fintype.card ι : ℝ) ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) ≤ 2 * ∑ i, R i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set K : ℝ := 1 / (NC ^ 2 * k0 * ε) with hK
  have hKpos : 0 < K := by positivity
  have hR : ∀ i, d i / ν i * K ≤ R i := by
    intro i
    rw [div_mul_eq_mul_div, div_le_iff₀ (hν i)]
    calc d i * K ≤ d i * A i := mul_le_mul_of_nonneg_left (hA i) (hd i).le
      _ ≤ ν i * R i := hq i
      _ = R i * ν i := mul_comm _ _
  have hv : ∏ i, (n * ν i / c1) ≤ 1 := by
    apply prod_le_one_of_sum_le_card (fun i => n * ν i / c1) (fun i => by have := hν i; positivity)
    rw [← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ hc1]
    exact mul_le_mul_of_nonneg_left hνs hn.le
  have hvpos : 0 < ∏ i, (n * ν i / c1) :=
    Finset.prod_pos fun i _ => by have := hν i; positivity
  have hz : n ≤ ∑ i, (N ^ 2 * d i) / (n * ν i / c1) := by
    apply card_le_sum_of_one_le_prod _ (fun i => by have := hν i; have := hd i; positivity)
    rw [Finset.prod_div_distrib]
    exact (one_le_div hvpos).mpr (hv.trans hprod)
  have hsum : ∑ i, (N ^ 2 * d i) / (n * ν i / c1) = (N ^ 2 * c1 / n) * ∑ i, d i / ν i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hν i
    field_simp
  rw [hsum] at hz
  have hdν : n ^ 2 / (N ^ 2 * c1) ≤ ∑ i, d i / ν i := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn] at hz
    nlinarith
  have h2K : 1 / (NC ^ 2 * ε) ≤ 2 * K := by
    rw [hK, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < NC ^ 2 * ε := by positivity
    nlinarith
  calc n ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) = (1 / (NC ^ 2 * ε)) * (n ^ 2 / (N ^ 2 * c1)) := by
        field_simp
    _ ≤ (2 * K) * (n ^ 2 / (N ^ 2 * c1)) := mul_le_mul_of_nonneg_right h2K (by positivity)
    _ ≤ (2 * K) * ∑ i, d i / ν i := mul_le_mul_of_nonneg_left hdν (by positivity)
    _ = 2 * ∑ i, d i / ν i * K := by rw [← Finset.sum_mul]; ring
    _ ≤ 2 * ∑ i, R i := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hR i) (by norm_num)

theorem coefficient_index_lower_bound (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientIndexLowerBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a ε hS hε hmaj χ hy
  obtain ⟨hH, hxL, hxξ, hxx, hne, hu0, hu⟩ := hS
  obtain ⟨_, hSS, hIso, hc1, hνc1, _, _, _, hchar, hz0, _⟩ := hH
  have hpair := FlowIsotropicPairs.isIsoPair_of X hIso hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hIso hxL
  obtain ⟨y, hyd, hy⟩ := hy
  have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
    by_contra hn
    apply hy
    unfold Data.fz
    rw [if_neg hn]
  have hSS' : X.IsBddSec la P ∧ _ := hSS
  have h3 := h3d r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS'.1.1 hchar ν χ y hyd
  have hy' : X.fz ![ξ, (X.NC : E) • x] X.g χ
      (X.fj la ((![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) 0) ν P) y ≠ 0 := hy
  rw [h3] at hy'
  by_cases hcond : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · rw [if_neg hcond] at hy'
    exact absurd rfl hy'
  rw [if_pos hcond] at hy'
  have hPD := h5 r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS hchar χ ⟨y, hyd, hy'⟩
  obtain ⟨β, -, hβ, hβint⟩ := (h2 r X ![ξ, (X.NC : E) • x] hpair hmem).2.2 χ hHF.1 hHF.2
  have hne0 : Nonempty X.Ψ := Fintype.card_pos_iff.mp (QuadraticCoefficientForms.card_Psi_pos (X := X.toData))

  have hz0dom : z0 ∈ X.dom := hz0.1
  have hmpos : ∀ τ, 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
    fun τ => X.maj_pos hz0dom τ (hu0 τ)
  have hck : ∀ τ, X.c τ = X.k0 := by
    intro τ
    show 2 * ‖τ.1 X.ξ0‖ = X.k0
    rw [X.ξ0_abs τ]
    ring

  have ha1 : ∀ τ, Complex.normSq (a τ 1) *
      ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    obtain ⟨T, hT, h⟩ : ∃ T : ℂ,
        T = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) ∧
        X.uvec ![ξ, (X.NC : E) • x] a τ = T • X.ucomp z0 ξ (X.embV x) τ := ⟨_, rfl, hu τ⟩
    have hV : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x -
        (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
          Data.emb τ.1 ξ := rfl
    have hU : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • ((X.NC : ℂ) • Data.emb τ.1 x) := by
      ext i
      simp [Data.uvec, Data.emb, Fin.sum_univ_two, smul_eq_mul, map_mul, map_natCast]
    rw [hU, hV] at h
    set S := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)
    have h0 : (a τ 0 + T * S) • Data.emb τ.1 ξ + (a τ 1 * X.NC - T) • Data.emb τ.1 x = 0 := by
      ext i
      have hi := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination hi
    have hq := QuadraticCoefficientForms.coef_zero hIso.2.2 hne τ.1 _ _ h0
    have hTa : a τ 1 * X.NC = T := sub_eq_zero.mp hq
    have hpos : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := by
      rw [hck τ]; exact mul_pos X.minWeight_pos (hmpos τ)
    have hT2 : Complex.normSq T = (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [hT, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
    have h4 : Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2 =
        (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [← hT2, ← hTa, Complex.normSq_mul, Complex.normSq_natCast]
      ring
    rw [hck τ] at h4 hpos
    rw [show Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        = (Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2) * (X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        by ring, h4]
    exact inv_mul_cancel₀ hpos.ne'

  have hχβ : ∀ (τ : X.Ψ) i k, χ τ i k = τ.1 (β i k) := by
    intro τ i k; rw [hβ]; rfl
  have hdpos : ∀ τ, 0 < (Matrix.of (χ τ)).det.re ∧ (Matrix.of (χ τ)).det.im = 0 := by
    intro τ
    have h := (hPD τ).det_pos
    rw [Complex.lt_def] at h
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hνpos : ∀ τ, 0 < ν τ := by
    intro τ
    have h := (hPD τ).diag_pos (i := 0)
    rw [Matrix.of_apply, hcond τ] at h
    exact_mod_cast h

  set Nn : ℕ := X.g * dEnat E ^ 2 with hNn
  have hdE : dE E = (dEnat E : ℝ) := by
    unfold dE dEnat
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNpos : 0 < (X.g : ℝ) * dE E ^ 2 := by
    rw [hdE]
    have h1 : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
    have h2 := X.g_pos
    positivity
  have hNcast : ((Nn : ℕ) : ℝ) = (X.g : ℝ) * dE E ^ 2 := by
    rw [hNn, hdE]; push_cast; ring
  set γ : E := (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 0) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 1) -
      (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 1) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 0) with hγ
  have hint : IsIntegral ℤ γ :=
    ((hβint 0 0).mul (hβint 1 1)).sub ((hβint 0 1).mul (hβint 1 0))
  have hγτ : ∀ τ : X.Ψ, τ.1 γ = ((Nn : ℂ)) ^ 2 * (Matrix.of (χ τ)).det := by
    intro τ
    rw [Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
      hχβ, hχβ, hχβ, hχβ, hγ]
    simp only [map_sub, map_mul, map_natCast, hNn]
    push_cast
    ring
  have hnorm : ∀ τ : X.Ψ, ‖τ.1 γ‖ = ((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re := by
    intro τ
    have hdet : (Matrix.of (χ τ)).det = (((Matrix.of (χ τ)).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hdpos τ).2])
    rw [hγτ τ, norm_mul, norm_pow, Complex.norm_natCast, hNcast]
    congr 1
    conv_lhs => rw [hdet]
    rw [Complex.norm_real, Real.norm_of_nonneg (hdpos τ).1.le]
  have hγ0 : γ ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := hne0
    have := hnorm τ
    rw [h0, map_zero, norm_zero] at this
    have := (hdpos τ).1
    have := hNpos
    nlinarith [mul_pos (pow_pos hNpos 2) (hdpos τ).1]
  have hp := QuadraticCoefficientForms.one_le_prod_norm (X := X.toData) γ hint hγ0
  simp_rw [hnorm] at hp
  rw [Finset.prod_pow] at hp
  have hprod : 1 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) := by
    have hnn : 0 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) :=
      Finset.prod_nonneg fun τ _ => by have := (hdpos τ).1; positivity
    by_contra hlt
    push_neg at hlt
    have := pow_lt_one₀ hnn hlt (two_ne_zero)
    linarith

  have hq : ∀ τ : X.Ψ, (Matrix.of (χ τ)).det.re * Complex.normSq (a τ 1) ≤
      ν τ * (X.chiAt χ a τ).re := by
    intro τ
    have h := QuadraticCoefficientForms.quad2 (Matrix.of (χ τ)) (hPD τ).1 (a τ)
    simp only [Matrix.of_apply] at h
    rw [hcond τ, Complex.ofReal_re] at h
    exact h
  have hA : ∀ τ : X.Ψ, 1 / ((X.NC : ℝ) ^ 2 * X.k0 * ε) ≤ Complex.normSq (a τ 1) := by
    intro τ
    have h := ha1 τ
    have hm := hmpos τ
    have hme := hmaj τ
    have hNC : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
    have hk := X.minWeight_pos
    rw [div_le_iff₀ (by positivity)]
    have hns := Complex.normSq_nonneg (a τ 1)
    have : Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ≤
        Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hme (by positivity)) hns
    linarith
  have key := card_sq_div_le_two_mul_sum_of_bounds (fun τ : X.Ψ => (Matrix.of (χ τ)).det.re) ν (fun τ => Complex.normSq (a τ 1))
    (fun τ => (X.chiAt χ a τ).re) ((X.g : ℝ) * dE E ^ 2) (X.NC : ℝ) X.k0 c1 ε hNpos
    (by exact_mod_cast X.NC_pos) X.minWeight_pos X.k0_le hε hc1 (fun τ => (hdpos τ).1) hνpos hνc1 hprod hA hq
  rw [QuadraticCoefficientForms.card_Psi (X := X.toData)] at key
  exact key

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecayHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem flow_coefficient_decay_holds (h1 : UnipotentVectorGroup (E := E)) (h2 : UnipotentLatticeLift (E := E))
    (h3 : FourierCoefficientProperties (E := E)) (h3d : FourierCoefficientSupport (E := E)) (h4 : HolomorphicPeriodicityExtension (E := E)) :
    FlowCoefficientDecay (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS χ z hz hf
  obtain ⟨hH, hxL, hxξ, hxx, hne, hxp0, hua⟩ := hS
  obtain ⟨-, hSS, hξ, -, -, -, -, hw, hχ, hz0, -⟩ := hH
  set u : Fin 2 → Fin r → E := ![ξ, (X.NC : E) • x] with hu
  set e := X.uvec u a with he
  set Q := X.fj la ξ ν P with hQ
  set S1 := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la Q y} with hS1
  have hpair := FlowIsotropicPairs.isIsoPair_of X hξ hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hξ hxL
  obtain ⟨hiso, heξ, hHe, hce⟩ :=
    FlowIsotropicPairs.e_facts X.toData hξ.2.1 hξ.2.2 hxξ hxx hz0.1 e hxp0 hua
  obtain ⟨httv, hTD1⟩ := FlowIsotropicPairs.flow_facts X.toData hz0 e hiso heξ hHe hce hz hf
  have hTdom : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := hTD1.1

  obtain ⟨CP, hCP⟩ := hSS.1.2
  have hQb : ∀ y ∈ X.dom, X.pnorm la Q y ≤ CP := fun y hy =>
    FlowCoefficientBounds.fj_bound X.toData la P CP hCP hξ ν hy
  have hCP0 : 0 ≤ CP :=
    le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz la).le) (hQb z hz)
  have hhat : ∀ y ∈ X.dom, X.hatN la Q y ≤ CP := fun y _ =>
    Real.sSup_le (by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy') hCP0
  have hle_hat : ∀ y ∈ X.dom, X.pnorm la Q y ≤ X.hatN la Q y := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy'⟩ ⟨y, hy, fun τ => rfl, rfl⟩
  have hle_S1 : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la Q y ≤ S1 := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', rfl⟩; exact hhat y' hy'.1⟩ ⟨y, hy, rfl⟩
  have hS10 : 0 ≤ S1 := le_trans (le_trans (mul_nonneg (norm_nonneg _)
    (FlowCoefficientBounds.nfac_pos X.toData hz0.1 la).le) (hle_hat z0 hz0.1)) (hle_S1 z0 hz0)

  obtain ⟨-, hL1⟩ := h1 r X.toData u hpair
  have hT1 : X.pnorm la (X.fz u X.g χ Q) (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    refine FlowCoefficientBounds.fz_bound X.toData u X.g χ Q la hTdom S1 hS10 fun b hb => ?_
    obtain ⟨-, -, -, -, -, hnfZ, -, hD1Z, -, -⟩ := hL1 b hb
    have hZ : X.Zb u b (X.flowV e (fun _ => -(I / 2)) z) ∈ X.FramesOverBasis ξ := hD1Z _ hTD1
    rw [← hnfZ la _ hTdom]
    exact (hle_hat _ hZ.1).trans (hle_S1 _ hZ)
  have hRHS : 0 ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hS10

  have hL3d : ∀ y ∈ X.dom, X.fz u X.g χ Q y =
      if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P y else 0 := fun y hy =>
    h3d r X u hpair hmem la P hSS.1.1 hχ ν χ y hy
  by_cases hc : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · have h0 : X.fz u X.g χ Q z = 0 := by rw [hL3d z hz, if_neg hc]
    show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
    rw [h0, norm_zero, zero_mul]
    exact hRHS
  have hGP : ∀ y ∈ X.dom, X.fz u X.g χ Q y = X.fz u X.g χ P y := fun y hy => by
    rw [hL3d y hy, if_pos hc]

  have hper := (h2 r X u hpair hmem).2.1 la P hSS.1.1 hχ
  obtain ⟨⟨hdiff, -, hcov⟩, -, -⟩ :=
    h3 r X.toData u X.g hpair X.g_pos la P hSS.1.1.1 hSS.1.1.2.1 hper χ

  obtain ⟨-, -, -, -, -, -, -, -, -, hRF⟩ := hL1 0 (fun τ i k => by simp)
  have hreal : ∀ s : X.Ψ → ℝ, X.fz u X.g χ P (X.flowV e (fun τ => (s τ : ℂ)) z) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * X.fz u X.g χ P z := by
    intro s
    have hb : IsHermFam (fun τ (i k : Fin 2) => (s τ : ℂ) * a τ i * conj (a τ k)) := by
      intro τ i k
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hRF' : X.flowV e (fun τ => (s τ : ℂ)) z =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) z := hRF a s z
    have hpr : X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) =
        ∑ τ, (X.chiAt χ a τ).re * s τ := by
      unfold Data.pairR Data.chiAt
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have : ∑ i, ∑ k, χ τ i k * ((s τ : ℂ) * a τ i * conj (a τ k)) =
          (s τ : ℂ) * ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [this, Complex.re_ofReal_mul, mul_comm]
    rw [hRF', hcov _ hb z hz, hpr, Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  have hL4 := h4 r X.toData e hiso (X.fz u X.g χ P) hdiff
    (fun τ => ((X.chiAt χ a τ).re : ℂ)) z hz hreal (fun _ => -(I / 2)) hTdom
  have hexp : 4 * (Real.pi : ℂ) * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * -(I / 2) =
      ((2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re : ℝ) : ℂ) := by
    rw [← Finset.sum_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ τ, ((X.chiAt χ a τ).re : ℂ)) * Complex.I_sq
  rw [hexp] at hL4
  have hnorm : ‖X.fz u X.g χ P z‖ = Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
      ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ := by
    rw [hL4, norm_mul, Complex.norm_exp_ofReal, ← mul_assoc, ← Real.exp_add,
      show -Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re) + 2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re = 0 by
        ring, Real.exp_zero, one_mul]

  have hq := m3bNorm_holds r X.toData e hiso la z hz (fun _ => -(I / 2)) hTdom
  have hq2 : X.nfac la z / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤
      ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) := by
    refine hq.2.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => ?_))
    simp only [httv τ]
    norm_num [max_def]
  have hprod : ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) ≤ 2 ^ (w / 2) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← Finset.sum_div]
    linarith
  have hnT := FlowCoefficientBounds.nfac_pos X.toData hTdom la
  have hnf : X.nfac la z ≤ 2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) := by
    rw [div_le_iff₀ hnT] at hq2
    exact hq2.trans (mul_le_mul_of_nonneg_right hprod hnT.le)

  have hT1' : ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
      X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    rw [← hGP _ hTdom]
    exact hT1
  show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
  rw [hGP z hz, hnorm]
  calc Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la z
      ≤ Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          (2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by gcongr
    _ = 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        (‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by ring
    _ ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 := by gcongr

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HCSumRight
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem sum_split' {M : Type*} [AddCommMonoid M] (f : Fin r → M) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → M, ∀ j (h : j < r), g j = f ⟨j, h⟩ :=
    ⟨fun j => if h : j < r then f ⟨j, h⟩ else 0, fun j h => dif_pos h⟩
  have h1 : ∑ j, f j = ∑ j : Fin r, g j :=
    Finset.sum_congr rfl fun j _ => (hg j j.isLt).symm
  have h2 : ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ a : Fin X.p0, g a :=
    Finset.sum_congr rfl fun a _ => (hg a (lt_of_lt_of_le a.isLt X.p0_le)).symm
  have h3 : ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ =
      ∑ m : Fin (r - X.p0), g (X.p0 + m) :=
    Finset.sum_congr rfl fun m _ =>
      (hg (X.p0 + m) (by have := m.isLt; have := X.p0_le; omega)).symm
  rw [h1, h2, h3, Fin.sum_univ_eq_sum_range g r, Fin.sum_univ_eq_sum_range g X.p0,
    Fin.sum_univ_eq_sum_range (fun m => g (X.p0 + m)) (r - X.p0)]
  conv_lhs => rw [← Nat.add_sub_of_le X.p0_le]
  exact Finset.sum_range_add g X.p0 (r - X.p0)

theorem hC_sum_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  simp only [hermC, Finset.sum_apply, map_sum, Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ i ∈ s, u a * τ (G a b) * conj (f i b))
      = ∑ a, ∑ i ∈ s, ∑ b, u a * τ (G a b) * conj (f i b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, u a * τ (G a b) * conj (f i b) := Finset.sum_comm

private theorem hermC_add_left_eq_add (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' w : Fin r → ℂ) :
    hermC τ G (u + u') w = hermC τ G u w + hermC τ G u' w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_smul_left_eq_smul_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hermC_finset_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * hermC τ G (v k) w := by
  classical
  induction s using Finset.induction_on
  · simp [hermC]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left_eq_add, hermC_smul_left_eq_smul_mul, ih]

theorem comb_col {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  rw [hermC_finset_sum_smul_left]
  have hab : ∀ a, hermC τ.1 X.Gm (col (mat x0 τ) a) (col (mat x0 τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have h := congrFun (congrFun (ho τ) a) b
    rw [Matrix.diagonal_apply] at h
    exact h
  simp [hab, mul_ite]

private theorem hermC_smul_right_eq_conj_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem comb_comb {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  rw [hC_sum_right']
  simp only [hermC_smul_right_eq_conj_mul, comb_col X ho τ c]
  exact Finset.sum_congr rfl fun a _ => by ring

def extP (g : Fin X.p0 → ℂ) : Fin r → ℂ := fun a => if h : (a : ℕ) < X.p0 then g ⟨a, h⟩ else 0

def extN (g : Fin (r - X.p0) → ℂ) : Fin r → ℂ :=
  fun a => if h : X.p0 ≤ (a : ℕ) then g ⟨a - X.p0, by have := a.isLt; omega⟩ else 0

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem unipotent_lattice_lift : UnipotentLatticeLift (E := E) := by
  intro r X u hu hmem
  exact ⟨fun b hb => X.exists_gamma u hu hmem b hb,
    fun la P hP hχ b hb x hx => X.LZ_periodic u hu hmem la P hP hχ b hb x hx,
    fun χ hχ hf => X.freq_to_beta χ hχ hf⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

