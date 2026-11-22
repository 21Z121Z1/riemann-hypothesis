import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartDetRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem ChartDetRatio.mem_adjoin_of_mem_chartRing {Ω : Type} [Field Ω] [CharZero Ω] {ι : Type} (x : ι → Ω)
    (i₀ : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i₀) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin ℚ _ hy
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem ChartDetRatio.detE_sum {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a a' : Fin 2 → Ω) :
    T.detE e (∑ q, a q • b q) (∑ q, a' q • b q) = (a 0 * a' 1 - a 1 * a' 0) * T.detE e (b 0) (b 1) := by
  simp only [T.detE, Fin.sum_univ_two, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

theorem ChartDetRatio.detE_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) : T.detE e (b 0) (b 1) ≠ 0 := by
  have hu : IsUnit (e.det b) := (Module.Basis.is_basis_iff_det e).1 ⟨hli, hsp⟩
  have h : e.det b = T.detE e (b 0) (b 1) := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply, T.detE]
    ring
  rw [← h]
  exact hu.ne_zero

theorem ChartDetRatio.proof : ChartDetRatio.Statement := by
  intro Ω _ _ ι ν _ _ E _ _ x B e δ i₀ hx hδ
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  have hR : ∀ a ∈ chartRing ℤ x i₀, a ∈ F := fun a ha => ChartDetRatio.mem_adjoin_of_mem_chartRing x i₀ ha
  obtain ⟨k, f, c, hf, -, hcf, hb⟩ := B.frame i₀ hx
  obtain ⟨l₁, hl₁⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcf
  obtain ⟨b, hbli, hbsp, hbiff⟩ := hb l₁
  have hfF : f l₁ ∈ F := hR _ (hf l₁)
  have hcoord : ∀ u ∈ B.lat i₀, ∃ a : Fin 2 → Ω, (∀ q, a q ∈ F) ∧ u = ∑ q, a q • b q := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := (hbiff u).1 ⟨0, by simpa using hu⟩
    refine ⟨a, fun q => ?_, rfl⟩
    obtain ⟨n, hn⟩ := ha q
    have h2 : a q = (f l₁ ^ n)⁻¹ * (f l₁ ^ n * a q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl₁), one_mul]
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hfF n)) (hR _ hn)
  set D := T.detE e (b 0) (b 1) with hDdef
  have hD : D ≠ 0 := ChartDetRatio.detE_ne_zero e b hbli hbsp
  have hdet : ∀ u ∈ B.lat i₀, ∀ w ∈ B.lat i₀, ∃ s ∈ F, T.detE e u w = D * s := by
    intro u hu w hw
    obtain ⟨a, ha, rfl⟩ := hcoord u hu
    obtain ⟨a', ha', rfl⟩ := hcoord w hw
    refine ⟨a 0 * a' 1 - a 1 * a' 0,
      sub_mem (mul_mem (ha 0) (ha' 1)) (mul_mem (ha 1) (ha' 0)), ?_⟩
    rw [ChartDetRatio.detE_sum, mul_comm]
  have hspan : ∀ y ∈ Submodule.span (chartRing ℤ x i₀)
      {d | ∃ u ∈ B.lat i₀, ∃ w ∈ B.lat i₀, d = x i₀ * T.detE e u w}, ∃ s ∈ F, y = x i₀ * D * s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, w, hw, rfl⟩ := hy
      obtain ⟨s, hs, h⟩ := hdet u hu w hw
      exact ⟨s, hs, by rw [h]; ring⟩
    | zero => exact ⟨0, zero_mem _, by ring⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨s + t, add_mem hs ht, by ring⟩
    | smul a y _ hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨(a : Ω) * s, mul_mem (hR _ a.2) hs, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
  have hδs : ∀ l, ∃ s ∈ F, δ l = x i₀ * D * s := fun l => hspan _ ((hδ i₀ hx).1 l)
  have hbmem : ∀ q, ∃ n : ℕ, f l₁ ^ n • b q ∈ B.lat i₀ := by
    intro q
    refine (hbiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q' = q
      · subst h
        simp [one_mem (chartRing ℤ x i₀)]
      · simp [h, zero_mem (chartRing ℤ x i₀)]
    · fin_cases q <;> simp
  obtain ⟨n0, h0⟩ := hbmem 0
  obtain ⟨n1, h1⟩ := hbmem 1
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, δ l₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hm := (hδ i₀ hx).2 _ h0 _ h1
    have hbot : Submodule.span (chartRing ℤ x i₀) (Set.range fun l => (x i₀)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    rw [hbot, Submodule.mem_bot] at hm
    have hsm : T.detE e (f l₁ ^ n0 • b 0) (f l₁ ^ n1 • b 1) = f l₁ ^ n0 * f l₁ ^ n1 * D := by
      simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul, hDdef]
      ring
    rw [hsm] at hm
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl₁) (pow_ne_zero _ hl₁)) hD hm
  obtain ⟨s₀, hs₀, hδ₀⟩ := hδs l₀
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hl₀ (by rw [hδ₀, mul_zero])
  refine ⟨l₀, hl₀, fun l => ?_⟩
  obtain ⟨s, hs, hδl⟩ := hδs l
  rw [hδl, hδ₀, mul_div_mul_left _ _ (mul_ne_zero hx hD)]
  exact div_mem hs hs₀

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartDualRational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

namespace ChartDualRational

theorem exists_uniform {α : Type*} [Fintype α] (P : α → ℕ → Prop) (mono : ∀ a n m, n ≤ m → P a n → P a m)
    (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by
  choose N hN using h
  exact ⟨∑ a, N a, fun a ↦ mono a _ _ (Finset.single_le_sum (by simp) (Finset.mem_univ a)) (hN a)⟩

variable {Ω : Type*} [Field Ω] {R : Subalgebra ℤ Ω}

theorem pow_mul_mem_mono {u y : Ω} (hu : u ∈ R) {n m : ℕ} (hnm : n ≤ m) (h : u ^ n * y ∈ R) :
    u ^ m * y ∈ R := by
  rw [← pow_mul_pow_sub u hnm, mul_comm (u ^ n), mul_assoc]
  exact mul_mem (pow_mem hu _) h

theorem mem_of_cover {k : ℕ} {f c : Fin k → Ω} (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1)
    {y : Ω} (hy : ∀ l, ∃ N : ℕ, f l ^ N * y ∈ R) : y ∈ R := by
  obtain ⟨N, hN⟩ := exists_uniform _ (fun l _ _ h ↦ pow_mul_mem_mono (hf l) h) hy
  let f' : Fin k → R := fun l ↦ ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : ∑ l, (⟨c l, hc l⟩ : R) * f' l = 1 := Subtype.ext (by simpa [f'] using hsum)
    rw [← h1]
    exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hN' := Ideal.span_pow_eq_top _ htop N
  rw [← Set.range_comp, Ideal.eq_top_iff_one] at hN'
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hN'
  have hd' : ∑ l, (d l : Ω) * f l ^ N = 1 := by simpa [f'] using congrArg Subtype.val hd
  have : y = ∑ l, (d l : Ω) * (f l ^ N * y) := by
    simp_rw [← mul_assoc, ← Finset.sum_mul, hd', one_mul]
  rw [this]
  exact sum_mem fun l _ ↦ mul_mem (d l).2 (hN l)

theorem mem_adjoin_of_mem_chartRing [CharZero Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j ↦ x j / x i) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
  | algebraMap r => simp
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

end ChartDualRational

open ChartDualRational in

theorem ChartDualRational.proof : ChartDualRational.Statement := by
  intro Ω _ _ ι κ _ _ E _ _ x B φ i₀ hx hsec hgen
  obtain ⟨r, f, c, hf, hc, hsum, hfr⟩ := B.frame i₀ hx
  choose b hbli hbsp hbiff using hfr
  obtain ⟨l₀, hl₀⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hn1 : ∀ l p, ∃ m : ℕ, f l ^ m • b l p ∈ B.lat i₀ := fun l p ↦
    (hbiff l (b l p)).2 ⟨Pi.single p 1, fun q ↦ ⟨0, by by_cases hq : q = p <;> simp [hq, one_mem, zero_mem]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using fun l ↦ exists_uniform (fun p m ↦ f l ^ m • b l p ∈ B.lat i₀)
    (fun p m m' hmm' h ↦ by
      rw [← pow_mul_pow_sub (f l) hmm', mul_comm, mul_smul]
      exact B.stable i₀ _ (pow_mem (hf l) _) _ h) (hn1 l)
  obtain ⟨bb, hbb⟩ : ∃ bb : Module.Basis (Fin 2) Ω E, ∀ q, bb q = b l₀ q :=
    ⟨Module.Basis.mk (hbli l₀) (hbsp l₀).ge, fun q ↦ by simp⟩
  have hcoord : ∀ v ∈ B.lat i₀, ∀ q, ∃ t : ℕ, f l₀ ^ t * bb.coord q v ∈ chartRing ℤ x i₀ := by
    intro v hv q
    obtain ⟨a, ha, rfl⟩ := (hbiff l₀ v).1 ⟨0, by simpa using hv⟩
    obtain ⟨t, ht⟩ := ha q
    refine ⟨t, ?_⟩
    have : bb.coord q (∑ p, a p • b l₀ p) = a q := by
      fin_cases q <;> simp [← hbb, Module.Basis.coord_apply, Module.Basis.repr_self]
    rwa [this]
  obtain ⟨M, hM⟩ := exists_uniform
    (fun (a : Fin r × Fin 2 × Fin 2) t ↦ f l₀ ^ t * bb.coord a.2.2 (f a.1 ^ n a.1 • b a.1 a.2.1) ∈ chartRing ℤ x i₀)
    (fun _ _ _ h h' ↦ pow_mul_mem_mono (hf l₀) h h') (fun a ↦ hcoord _ (hn a.1 a.2.1) _)
  have hdual : ∀ q, f l₀ ^ M • bb.coord q ∈ T.dualLat B i₀ := by
    intro q
    simp only [T.dualLat, Set.mem_ofPred_eq]
    intro v hv
    rw [LinearMap.smul_apply, smul_eq_mul]
    refine mem_of_cover hf hc hsum fun l ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (hbiff l v).1 ⟨0, by simpa using hv⟩
    obtain ⟨m, hm⟩ := exists_uniform (fun p t ↦ f l ^ t * a p ∈ chartRing ℤ x i₀)
      (fun p _ _ h h' ↦ pow_mul_mem_mono (hf l) h h') ha
    refine ⟨m + n l, ?_⟩
    have : f l ^ (m + n l) * (f l₀ ^ M * bb.coord q (∑ p, a p • b l p)) =
        ∑ p, (f l ^ m * a p) * (f l₀ ^ M * bb.coord q (f l ^ n l • b l p)) := by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, pow_add]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    rw [this]
    exact sum_mem fun p _ ↦ mul_mem (hm p) (hM (l, p, q))
  choose d hdR hd using fun q ↦ hgen i₀ hx _ (hdual q)
  refine ⟨bb, fun k q ↦ φ k (bb q) / x i₀, fun k q ↦ by field_simp, fun k q ↦ ?_, ?_⟩
  · have hs : f l₀ ^ n l₀ • bb q ∈ B.lat i₀ := by rw [hbb]; exact hn l₀ q
    obtain ⟨a, ha, hae⟩ := (mem_lineLat x 1 i₀ _).1 (hsec i₀ hx k _ hs)
    rw [map_smul, smul_eq_mul, pow_one] at hae
    have : φ k (bb q) / x i₀ = a / f l₀ ^ n l₀ := by
      rw [div_eq_div_iff hx (pow_ne_zero _ hl₀), hae]
      ring
    show φ k (bb q) / x i₀ ∈ _
    rw [this]
    exact div_mem (mem_adjoin_of_mem_chartRing x i₀ ha) (pow_mem (mem_adjoin_of_mem_chartRing x i₀ (hf l₀)) _)
  · by_contra hmin
    push Not at hmin
    have hm : ∀ k k', φ k (bb 0) / x i₀ * (φ k' (bb 1) / x i₀) - φ k (bb 1) / x i₀ * (φ k' (bb 0) / x i₀) = 0 :=
      fun k k' ↦ hmin k k'
    have hrow : ∀ q p, ∑ k, d q k * (φ k (bb p) / x i₀) = f l₀ ^ M * if p = q then 1 else 0 := by
      intro q p
      have h := LinearMap.congr_fun (hd q) (bb p)
      simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        LinearMap.sum_apply, smul_eq_mul] at h
      rw [h]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hdet : (∑ k, d 0 k * (φ k (bb 0) / x i₀)) * (∑ k, d 1 k * (φ k (bb 1) / x i₀)) -
        (∑ k, d 0 k * (φ k (bb 1) / x i₀)) * (∑ k, d 1 k * (φ k (bb 0) / x i₀)) = 0 := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k' _ ↦ ?_
      linear_combination (d 0 k * d 1 k') * hm k k'
    rw [hrow 0 0, hrow 1 1, hrow 0 1, hrow 1 0] at hdet
    simp [hl₀] at hdet

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace FibreLocal

@[local instance] theorem isProbabilityMeasure_sphere : IsProbabilityMeasure sphereMeasure :=
  sphereInv_thm.1

theorem add_mul_gPoly (k : ℕ) :
    (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) * gPoly k = X 1 * (X 0 ^ (2 * k) - X 1 ^ (2 * k)) := by
  have h := (Commute.all (-(X 1 : MvPolynomial (Fin 2) ℝ)) (X 0)).geom_sum₂_mul (2 * k)
  have hs : ∑ j ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ j • ((X 0 : MvPolynomial (Fin 2) ℝ) ^ (2 * k - 1 - j) * X 1 ^ j) =
      ∑ i ∈ Finset.range (2 * k), (-(X 1 : MvPolynomial (Fin 2) ℝ)) ^ i * X 0 ^ (2 * k - 1 - i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_pow, map_neg, map_one, neg_pow (X 1 : MvPolynomial (Fin 2) ℝ)]
    ring
  rw [gPoly, hs]
  rw [(even_two_mul k).neg_pow] at h
  linear_combination (-(X 1 : MvPolynomial (Fin 2) ℝ)) * h

theorem gPoly_eq (k : ℕ) : gPoly k = FlagBundles.gKernel ℝ k := by
  have hne : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  exact mul_left_cancel₀ hne (by rw [add_mul_gPoly, (FlagBundles.GKernelIdentity.full ℝ k).1])

theorem dgPoly_eq (k : ℕ) : dgPoly k = FlagBundles.gMixed k := by
  rw [dgPoly, FlagBundles.gMixed, gPoly_eq]

theorem integrable_kernel :
    Integrable (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_kernel FlagBundles.FibreConstantClosedForm.full

theorem integrable_mul (f : S2 × S2 → ℝ) (hf : Continuous f) :
    Integrable (fun p : S2 × S2 =>
      (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2) * f p)
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_term integrable_kernel f hf

theorem continuous_evalPair (g : MvPolynomial (Fin 2) ℝ) (u v : S2 × S2 → ℝ) (hu : Continuous u)
    (hv : Continuous v) : Continuous fun p => eval ![u p, v p] g := by
  have h2 : Continuous fun p => (![u p, v p] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hu
    · simpa using hv
  exact (MvPolynomial.continuous_eval g).comp h2

theorem kappa_eq (k : ℕ) : kappa k = -FlagBundles.fibreConstant k := by
  have hc : Continuous fun p : S2 × S2 => eval ![(p.1 : E3) 2, (p.2 : E3) 2] (dgPoly k) :=
    continuous_evalPair _ _ _ ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp (continuous_subtype_val.comp continuous_snd))
  rw [kappa, FlagBundles.fibreConstant, neg_inj]
  refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
  simp_rw [dgPoly_eq]
  rfl

theorem sphere_moment (a : E3) (m : ℕ) :
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m) ∂sphereMeasure = inner ℝ a a ^ m / (2 * m + 1) := by
  by_cases ha : a = 0
  · subst ha
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [inner_zero_left, zero_pow (by omega : 2 * m ≠ 0), zero_pow (by omega : m ≠ 0)]
  · set r : ℝ := ‖a‖ with hr
    have hr0 : r ≠ 0 := norm_ne_zero_iff.mpr ha
    set u : E3 := r⁻¹ • a with hu
    have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, ← hr, inv_mul_cancel₀ hr0]
    have hin : ∀ n : S2, inner ℝ a (n : E3) = r * inner ℝ (n : E3) u := by
      intro n
      rw [hu, inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    have hA := (archimedes_thm u u u (fun t => (r * t) ^ (2 * m)) hu1
      (Continuous.intervalIntegrable (by fun_prop) _ _)).2.1
    simp_rw [hin]
    rw [hA]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_pow, real_inner_self_eq_norm_sq, ← hr]
    have h1 : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, (even_two_mul m).neg_one_pow]; ring
    rw [h1, ← pow_mul]
    push_cast
    field_simp
    ring

theorem eval_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ m, Integrable (fun p => w p * coeff m Q p) μ)
    (a : Fin 3 → ℝ) :
    eval a (momentPoly μ w Q) = ∫ p, w p * eval₂ (Pi.evalRingHom (fun _ : Ω => ℝ) p) a Q ∂μ := by
  rw [momentPoly, map_sum]
  simp only [eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun m _ => (hQ m).mul_const _)]
  congr 1
  funext p
  rw [eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Finsupp.prod]
  ring

def coordS (i : Fin 3) : C(S2, ℝ) :=
  ⟨fun n => (n : E3) i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

theorem dotPoly_id_pow (N : ℕ) :
    (dotPoly (id : S2 → S2)) ^ N =
      MvPolynomial.map (ContinuousMap.coeFnRingHom : C(S2, ℝ) →+* (S2 → ℝ)) ((∑ i, X i * C (coordS i)) ^ N) := by
  rw [map_pow, dotPoly]
  simp only [map_sum, map_mul, map_X, map_C]
  rfl

theorem pushMomentPoly_eq (k : ℕ) (hk : 1 ≤ k) :
    pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
  apply MvPolynomial.funext
  intro a
  have hQ : ∀ m, Integrable (fun p : S2 => (1 : ℝ) * coeff m ((dotPoly (id : S2 → S2)) ^ (2 * k - 2)) p)
      sphereMeasure := by
    intro m
    rw [dotPoly_id_pow, coeff_map]
    simp only [one_mul]
    exact (ContinuousMap.continuous (coeff m ((∑ i, X i * C (coordS i)) ^ (2 * k - 2)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pushMomentPoly, smul_eval, eval_momentPoly _ _ _ hQ]
  have he : ∀ p : S2, eval₂ (Pi.evalRingHom (fun _ : S2 => ℝ) p) a ((dotPoly id) ^ (2 * k - 2)) =
      inner ℝ (WithLp.toLp 2 a : E3) (p : E3) ^ (2 * k - 2) := by
    intro p
    rw [eval₂_pow, dotPoly]
    simp [eval₂_sum, PiLp.inner_apply, mul_comm]
  simp_rw [he, one_mul]
  have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [hkk, sphere_moment]
  have haa : inner ℝ (WithLp.toLp 2 a : E3) (WithLp.toLp 2 a) = ∑ i, a i ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [haa]
  simp only [map_neg, map_pow, map_sum, eval_X]
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hc]
  have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  ring

theorem fibreMomentPoly_eq (k : ℕ) : fibreMomentPoly k = FlagBundles.fibrePoly k := by
  have hQ : aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (dgPoly k) =
      FlagBundles.FibreIntegralInvariant.fibreQ k := by
    rw [FlagBundles.FibreIntegralInvariant.fibreQ, dgPoly_eq]
    refine congrArg (fun x => aeval x (FlagBundles.gMixed k)) ?_
    funext r
    fin_cases r <;> simp [dotPoly]
  rw [FlagBundles.FibreIntegralInvariant.fibrePoly_eq, fibreMomentPoly, momentPoly, hQ]
  rfl

theorem proof : FibreLocal.Statement := by
  refine ⟨fun k a => ?_, fun k B _ _ a => ?_, fun k hk a => ?_, fun k hk B _ _ a => ?_, fun k => ?_⟩
  · have hc : Continuous fun p : S2 × S2 => eval ![inner ℝ a (p.1 : E3), inner ℝ a (p.2 : E3)] (dgPoly k) :=
      continuous_evalPair _ _ _ (continuous_const.inner (continuous_subtype_val.comp continuous_fst))
        (continuous_const.inner (continuous_subtype_val.comp continuous_snd))
    refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
    simp_rw [dgPoly_eq]
    rw [kappa_eq, neg_neg]
    exact FlagBundles.FibreIntegralInvariant.full.1 k a
  · rw [fibreMomentPoly_eq, FlagBundles.FibreIntegralInvariant.full.2 k B a, kappa_eq, neg_neg]
  · have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
    rw [hkk, sphere_moment]
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hc]
    have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp
    ring
  · rw [pushMomentPoly_eq k hk]
    simp [map_neg, map_pow, map_sum, aeval_X]
  · rw [kappa_eq, FlagBundles.fibreConstant_eq]
    ring

end FibreLocal

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StDiagRatioBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagRatioBasis.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type)
    [AddCommGroup E] [Module Ω E] (Φ : Type) [Field Φ] [CharZero Φ] [Algebra Ω Φ] (x : ι → Ω)
    (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (g : κ → Fin 2 → Ω) (i₀ : ι) (l₀ : ν)
    (k₀ k₁ : κ) (d : ℕ) (t : Fin d → Ω) (a : Φ),
    x i₀ ≠ 0 → AlgebraicIndependent ℚ t →
    (∀ n, t n ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ j, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) (x j / x i₀)) →
    δ l₀ ≠ 0 → (∀ l, δ l / δ l₀ ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ k q, φ k (b q) = x i₀ * g k q) →
    (∀ k q, g k q ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0 → Transcendental Ω a →
      ∃ (c : ∀ k, T.wwIdx ι ν κ k) (t' : Fin (d + 1) → Φ), (∀ k, T.wwCoord x δ e φ a a ⟨k, c k⟩ ≠ 0) ∧
        AlgebraicIndependent ℚ t' ∧
        (∀ n, t' n ∈ IntermediateField.adjoin ℚ (coneRatios (T.wwCoord x δ e φ a a) c)) ∧
        ∀ r ∈ coneRatios (T.wwCoord x δ e φ a a) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t')) r

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StHorizNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HorizNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (s s' : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P d → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    W ∈ divSupp P s → IsHorizontal W → s' ∉ W

end GroundTheory.Heights₂.Heights.Inter
end
end

