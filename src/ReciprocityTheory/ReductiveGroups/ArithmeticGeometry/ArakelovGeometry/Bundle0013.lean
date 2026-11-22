import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1

theorem dmap_injective {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) (a : K → ℕ) :
    Function.Injective (dmap W i a) := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hxy
  have hd : Ideal.Quotient.mk (dehomI W i) s = Ideal.Quotient.mk (dehomI W i) t := hxy
  have hsub : s - t ∈ dehomI W i := Ideal.Quotient.eq.1 hd
  have hW := mem_of_mem_dehomI hWp hWm hi (homog_of_mem (Submodule.sub_mem _ hs ht)) hsub
  apply Subtype.ext
  exact Ideal.Quotient.eq.2 hW

theorem dmap_mono (W : Ideal (MRing ι)) (i : ∀ k, ι k) {a a' : K → ℕ} (h : ∀ k, a k ≤ a' k)
    (x : mPiece W a) : ∃ x' : mPiece W a', dmap W i a' x' = dmap W i a x := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  obtain ⟨_, s, hs, rfl⟩ := x
  have hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a' := by
    apply Submodule.subset_span
    have := isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))
    have hsum : a + (fun k => a' k - a k) = a' := by
      funext k
      simp only [Pi.add_apply]
      have := h k
      omega
    rw [hsum] at this
    exact this
  refine ⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s
  rw [map_mul, mk_xpow, mul_one]

theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    IsMultiHomog (monomial m c : MRing ι) (fun k => ∑ i, m ⟨k, i⟩) := by
  classical
  intro m' hm' k
  rw [MvPolynomial.support_monomial] at hm'
  split_ifs at hm' with hc
  · simp at hm'
  · rw [Finset.mem_singleton] at hm'
    rw [hm']

theorem dmap_cover (W : Ideal (MRing ι)) (i : ∀ k, ι k) (y : MRing ι ⧸ dehomI W i) :
    ∃ (a : K → ℕ) (x : mPiece W a), dmap W i a x = y := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ := fun m k => ∑ j, m ⟨k, j⟩
  let a : K → ℕ := fun k => f.support.sup (fun m => deg m k)
  have hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k := fun m hm k =>
    Finset.le_sup (f := fun m => deg m k) hm
  have hterm : ∀ m ∈ f.support,
      monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a := by
    intro m hm
    apply Submodule.subset_span
    have := isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m))
      (isMultiHomog_xpow i (fun k => a k - deg m k))
    have hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a := by
      funext k
      simp only [Pi.add_apply]
      have := hle m hm k
      simp only [deg] at this ⊢
      omega
    rw [hsum] at this
    exact this
  have hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a :=
    Submodule.sum_mem _ hterm
  refine ⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i)
      (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) =
    Ideal.Quotient.mk (dehomI W i) f
  simp only [map_sum, map_mul, mk_xpow, mul_one]
  conv_rhs => rw [f.as_sum]
  rw [map_sum]

theorem card_dehom {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a₁ c0 : ℕ}
    (hconst : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → Nat.card (mPiece W a) = c0)
    (hfin : ∀ a : K → ℕ, Finite (mPiece W a)) {a : K → ℕ} (ha : ∀ k, a₁ ≤ a k) :
    Nat.card (MRing ι ⧸ dehomI W i) = c0 := by
  classical
  have hinj := fun b => dmap_injective hWp hWm hi b
  have hsurj : Function.Surjective (dmap W i a) := by
    intro y
    obtain ⟨b, x, hx⟩ := dmap_cover W i y
    let a' : K → ℕ := fun k => max (a k) (b k)
    have ha' : ∀ k, a₁ ≤ a' k := fun k => le_trans (ha k) (le_max_left _ _)
    obtain ⟨x', hx'⟩ := dmap_mono W i (fun k => le_max_right (a k) (b k)) x
    haveI := hfin a
    haveI := hfin a'
    have hsub : Set.range (dmap W i a) ⊆ Set.range (dmap W i a') := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨z', hz'⟩ := dmap_mono W i (fun k => le_max_left (a k) (b k)) z
      exact ⟨z', hz'⟩
    have hcard : (Set.range (dmap W i a')).ncard ≤ (Set.range (dmap W i a)).ncard := by
      show Nat.card (Set.range (dmap W i a')) ≤ Nat.card (Set.range (dmap W i a))
      first
        | rw [Set.Nat.card_range_of_injective (hinj a), Set.Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
        | rw [Nat.card_range_of_injective (hinj a), Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)
    have hy : y ∈ Set.range (dmap W i a') := ⟨x', hx'.trans hx⟩
    rw [← heq] at hy
    exact hy
  rw [← hconst a ha]
  exact (Nat.card_eq_of_bijective _ ⟨hinj a, hsurj⟩).symm

theorem natCard_eq_pow_length {A : Type*} [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : A, p • x = 0) : Nat.card A = p ^ (Module.length ℤ A).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) A := AddCommGroup.zmodModule h
  have hlen : Module.length ℤ A = Module.length (ZMod p) A :=
    Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)
  have hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞) :=
    @Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  have hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    @Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  rw [hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionBasisLocalUniformBound
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_pos_lower_bound_compact {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {ν : E → ℝ} (hc : ContinuousOn ν K) (hpos : ∀ y ∈ K, 0 < ν y) :
    ∃ νmin : ℝ, 0 < νmin ∧ ∀ y ∈ K, νmin ≤ ν y := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn h hc
    exact ⟨ν y, hpos y hy, fun z hz => hmin hz⟩

theorem exists_fderiv_bound_compact {U K : Set (Fin D → ℂ)} (hU : IsOpen U) {ν : (Fin D → ℂ) → ℝ}
    (hν : ContDiffOn ℝ 1 ν U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, ∀ y ∈ K, ‖fderiv ℝ ν y‖ ≤ L :=
  hK.exists_bound_of_continuousOn ((hν.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)

theorem section_basis_local_uniform_bound {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {U C : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (hγ : IsParam (coordIdeal ℤ x) U γ) (hC : IsCompact C)
    (hCU : C ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y₀ ∈ C, ∀ c : Fin r → ℂ,
        ‖∑ k, c k * secFun (b k) (γ y₀)‖ ^ 2 * wgt (interp m₀ m₁ t) n (γ y₀) ≤
          M * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n) c := by
  obtain ⟨ν, hν1, hνpos, hνint⟩ := hg₀.vol.2.2 U γ hγ
  have hνD : IsDensityFor μ U γ ν := ⟨hν1, hνpos, hνint⟩
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hγ.1 hCU
  have hC'c : IsCompact (Metric.cthickening δ C) := hC.cthickening
  obtain ⟨ψ₀, hψ₀def⟩ : ∃ ψ : (Fin D → ℂ) → ℝ, ψ = fun y => Real.log (m₀.ρ (γ y)) := ⟨_, rfl⟩
  obtain ⟨ψ₁, hψ₁def⟩ : ∃ ψ : (Fin D → ℂ) → ℝ, ψ = fun y => Real.log (m₁.ρ (γ y)) := ⟨_, rfl⟩
  have hψ₀ : ContDiffOn ℝ ∞ ψ₀ U := by rw [hψ₀def]; exact contDiffOn_log_metric_param m₀ hg₀.semipos.1 hγ
  have hψ₁ : ContDiffOn ℝ ∞ ψ₁ U := by rw [hψ₁def]; exact contDiffOn_log_metric_param m₁ hg₁.semipos.1 hγ
  obtain ⟨B₀₂, hB₀₂, hb₀₂⟩ := exists_bound_iteratedFDeriv_compact hγ.1 hψ₀ hC'c hδU 2
  obtain ⟨B₁₂, hB₁₂, hb₁₂⟩ := exists_bound_iteratedFDeriv_compact hγ.1 hψ₁ hC'c hδU 2
  obtain ⟨B₀₃, hB₀₃, hb₀₃⟩ := exists_bound_iteratedFDeriv_compact hγ.1 hψ₀ hC'c hδU 3
  obtain ⟨B₁₃, hB₁₃, hb₁₃⟩ := exists_bound_iteratedFDeriv_compact hγ.1 hψ₁ hC'c hδU 3
  obtain ⟨νmin, hνmin, hνminle⟩ := exists_pos_lower_bound_compact hC'c (hν1.continuousOn.mono hδU)
    (fun y hy => hνpos y (hδU hy))
  obtain ⟨Lν, hLν⟩ := exists_fderiv_bound_compact hγ.1 hν1 hC'c hδU
  obtain ⟨M, hM, hMor⟩ := morse_general_uniform (D := D) δ (2 * (B₀₂ + B₁₂)) (2 * (B₀₃ + B₁₃)) Lν
    νmin hδ hνmin
  refine ⟨M, hM.le, ?_⟩
  intro n r b hn hb t ht y₀ hy₀ c
  have hballC' : Metric.ball y₀ δ ⊆ Metric.cthickening δ C :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_cthickening hy₀ δ)
  have hball : Metric.ball y₀ δ ⊆ U := hballC'.trans hδU
  have hmem : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, y₀ + y ∈ Metric.ball y₀ δ :=
    fun y hy => gaap_mem_ball_add.2 hy
  have hne : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, γ (y₀ + y) ≠ 0 :=
    fun y hy => (hγ.2.2.1 _ (hball (hmem y hy))).1
  obtain ⟨φ, hφdef⟩ : ∃ φ : (Fin D → ℂ) → ℝ,
      φ = fun y => (2 * (1 - t)) * ψ₀ (y₀ + y) + (2 * t) * ψ₁ (y₀ + y) := ⟨_, rfl⟩
  have hexp : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ,
      Real.exp (-((n : ℝ) * φ y)) = wgt (interp m₀ m₁ t) n (γ (y₀ + y)) := by
    intro y hy
    rw [← exp_eq_interpolatedWeight m₀ m₁ t n _ (hne y hy)]
    simp only [hφdef, hψ₀def, hψ₁def]
    congr 1
    ring
  have hψ₀' : ContDiffOn ℝ ∞ (fun y => ψ₀ (y₀ + y)) (Metric.ball 0 δ) :=
    hψ₀.comp (contDiffOn_const.add contDiffOn_id) (fun y hy => hball (hmem y hy))
  have hψ₁' : ContDiffOn ℝ ∞ (fun y => ψ₁ (y₀ + y)) (Metric.ball 0 δ) :=
    hψ₁.comp (contDiffOn_const.add contDiffOn_id) (fun y hy => hball (hmem y hy))
  have hφ3 : ContDiffOn ℝ 3 φ (Metric.ball 0 δ) := by
    rw [hφdef]
    exact ((contDiffOn_const.mul hψ₀').add (contDiffOn_const.mul hψ₁')).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hbd : ∀ k : ℕ, ∀ B₀ B₁ : ℝ, 0 ≤ B₀ → 0 ≤ B₁ →
      (∀ y ∈ Metric.cthickening δ C, ‖iteratedFDeriv ℝ k ψ₀ y‖ ≤ B₀) →
      (∀ y ∈ Metric.cthickening δ C, ‖iteratedFDeriv ℝ k ψ₁ y‖ ≤ B₁) →
      ∀ y ∈ Metric.ball (0 : Fin D → ℂ) δ, ‖iteratedFDeriv ℝ k φ y‖ ≤ 2 * (B₀ + B₁) := by
    intro k B₀ B₁ h0 h1 hb0 hb1 y hy
    have hyC : y₀ + y ∈ Metric.cthickening δ C := hballC' (hmem y hy)
    have hyU : y₀ + y ∈ U := hδU hyC
    rw [hφdef]
    exact iteratedFDeriv_convexComb_le ψ₀ ψ₁ y₀ y k ht h0 h1
      ((hψ₀.contDiffAt (hγ.1.mem_nhds hyU)).of_le (by exact_mod_cast le_top))
      ((hψ₁.contDiffAt (hγ.1.mem_nhds hyU)).of_le (by exact_mod_cast le_top)) (hb0 _ hyC) (hb1 _ hyC)
  have h0 : (0 : Fin D → ℂ) ∈ Metric.ball (0 : Fin D → ℂ) δ := Metric.mem_ball_self hδ
  have hK2 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ 2 * (B₀₂ + B₁₂) := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hbd 2 B₀₂ B₁₂ hB₀₂ hB₁₂ hb₀₂ hb₁₂ 0 h0
  have hK3 : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) δ, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ 2 * (B₀₃ + B₁₃) :=
    hbd 3 B₀₃ B₁₃ hB₀₃ hB₁₃ hb₀₃ hb₁₃
  have hνc : ContinuousOn (fun y => ν (y₀ + y)) (Metric.ball 0 δ) :=
    hν1.continuousOn.comp (continuousOn_const.add continuousOn_id) (fun y hy => hball (hmem y hy))
  have hν0 : νmin ≤ ν (y₀ + 0) := by
    rw [add_zero]; exact hνminle y₀ (Metric.self_subset_cthickening C hy₀)
  have hνL : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) δ, ν (y₀ + 0) - Lν * ‖z‖ ≤ ν (y₀ + z) := by
    intro z hz
    have hd : ∀ y ∈ Metric.ball y₀ δ, DifferentiableAt ℝ ν y := fun y hy =>
      (hν1.contDiffAt (hγ.1.mem_nhds (hball hy))).differentiableAt one_ne_zero
    have hmv := (convex_ball y₀ δ).norm_image_sub_le_of_norm_fderiv_le hd
      (fun y hy => hLν y (hballC' hy)) (Metric.mem_ball_self hδ) (hmem z hz)
    rw [add_sub_cancel_left, Real.norm_eq_abs] at hmv
    rw [add_zero]
    have h2 := neg_abs_le (ν (y₀ + z) - ν y₀)
    linarith
  have hνnn : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) δ, 0 ≤ ν (y₀ + z) :=
    fun z hz => (hνpos _ (hball (hmem z hz))).le
  have hf : DifferentiableOn ℂ (fun y => ∑ k, c k * secFun (b k) (γ (y₀ + y))) (Metric.ball 0 δ) :=
    (differentiable_sectionCombination b c).comp_differentiableOn
      (hγ.2.1.differentiableOn.comp ((differentiable_const y₀).add differentiable_id).differentiableOn
        (fun y hy => hball (hmem y hy)))
  have hν' := IsDensityFor.translate hγ hνD y₀ hball
  have hgt := isGood_interp hg₀ hg₁ ht
  have hgi := integrable_normSq_combination (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n)
    (fun i j => integrable_secFun hgt hb i j) c
  have hgm : Measurable (fun z => ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt (interp m₀ m₁ t) n z) :=
    ((continuous_norm.comp (differentiable_sectionCombination b c).continuous).measurable.pow_const 2).mul
      (measurable_interpolatedWeight m₀ m₁ hg₀.semipos.1 hg₁.semipos.1 t n)
  have hc : ContinuousOn (fun y => ‖∑ k, c k * secFun (b k) (γ (y₀ + y))‖ ^ 2 *
      Real.exp (-((n : ℝ) * φ y)) * ν (y₀ + y)) (Metric.ball 0 δ) :=
    ((hf.continuousOn.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul hφ3.continuousOn).neg))).mul hνc
  obtain ⟨hI, hle⟩ := setIntegral_parametrisation_le hν' hgm (isDegreeZero_weightedCombination (interp m₀ m₁ t) hb.1 c)
    (fun z => mul_nonneg (sq_nonneg _) (cone_metric_weight_nonneg _ _ _)) hgi hc
    (fun y hy => by rw [hexp y hy])
  have hmo := hMor n hn φ (fun y => ν (y₀ + y)) (fun y => ∑ k, c k * secFun (b k) (γ (y₀ + y)))
    hφ3 hK2 hK3 hνc hν0 hνL hνnn hf hI
  have hMn : 0 ≤ M * (n : ℝ) ^ D := mul_nonneg hM.le (pow_nonneg (Nat.cast_nonneg _) _)
  calc ‖∑ k, c k * secFun (b k) (γ y₀)‖ ^ 2 * wgt (interp m₀ m₁ t) n (γ y₀)
      = ‖∑ k, c k * secFun (b k) (γ (y₀ + 0))‖ ^ 2 * Real.exp (-((n : ℝ) * φ 0)) := by
        rw [hexp 0 h0, add_zero]
    _ ≤ _ := hmo
    _ ≤ M * (n : ℝ) ^ D * ∫ z, ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt (interp m₀ m₁ t) n z ∂μ :=
        mul_le_mul_of_nonneg_left hle hMn
    _ = _ := rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

