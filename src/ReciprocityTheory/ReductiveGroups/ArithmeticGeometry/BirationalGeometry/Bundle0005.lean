import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

private theorem coneMap_monomial' (x : ι → Ω) (e : ι →₀ ℕ) (a : o) :
    coneMap o x (monomial e a) = Polynomial.C (aeval x (monomial e a)) * Polynomial.X ^ e.degree := by
  unfold coneMap
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, Polynomial.C_pow,
    Finset.prod_pow_eq_pow_sum]
  congr 1

private theorem coeff_coneMap_eq_aeval_homogeneousComponent (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [Polynomial.finset_sum_coeff]
  simp only [coneMap_monomial', Polynomial.coeff_C_mul_X_pow]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_ne e.degree d with h | h
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coneMap_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneMap o x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  ext d
  rw [coeff_coneMap_eq_aeval_homogeneousComponent, Polynomial.coeff_C_mul_X_pow,
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf)]
  rcases eq_or_ne d n with rfl | h
  · simp
  · rw [if_neg h, if_neg h, map_zero]

theorem mem_coordIdeal_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous o x hf, h, map_zero, zero_mul]

theorem coeff_coneMap (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  exact coeff_coneMap_eq_aeval_homogeneousComponent o x f d

theorem coordIdeal_isHomogIdeal (x : ι → Ω) : IsHomogIdeal o (coordIdeal o x) := by
  intro f hf d
  rw [coordIdeal, RingHom.mem_ker] at hf ⊢
  rw [coneMap_of_isHomogeneous o x (homogeneousComponent_isHomogeneous d f), ← coeff_coneMap, hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end Coord

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenMet
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section On

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

variable (C ι) in

structure ConeMetricOn (S : Set (ι → C)) where

  ρ : (ι → C) → ℝ
  pos : ∀ z ∈ S, 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), z ∈ S → c • z ∈ S → ρ (c • z) = ‖c‖ * ρ z

def ConeMetric.restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0) :
    ConeMetricOn C ι S where
  ρ := m.ρ
  pos z hz := m.pos z (hS z hz)
  smul c z _ _ := m.smul c z

def ptNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d

def supNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) : ℝ :=
  sSup (ptNormOn m σ d f '' S)

def IsPtsMeasureOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (μ : MeasureTheory.Measure (ι → ℂ)) :
    Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ (S ∩ {z | m.ρ z = 1})ᶜ = 0

def l2NormOn {S : Set (ι → ℂ)} (m : ConeMetricOn ℂ ι S) (σ : o →+* ℂ)
    (μ : MeasureTheory.Measure (ι → ℂ)) (d : ℕ) (f : MvPolynomial ι o) : ℝ :=
  Real.sqrt (∫ z, ptNormOn m σ d f z ^ 2 ∂μ)

theorem conePts_ne_zero (σ : o →+* C) (I : Ideal (MvPolynomial ι o)) :
    ∀ z ∈ conePts σ I, z ≠ 0 :=
  fun _ hz => hz.1

theorem ptNormOn_restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0)
    (σ : o →+* C) (d : ℕ) (f : MvPolynomial ι o) (z : ι → C) :
    ptNormOn (m.restrict S hS) σ d f z = ptNorm m σ d f z :=
  rfl

theorem supNormOn_restrict (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial ι o))
    (d : ℕ) (f : MvPolynomial ι o) :
    supNormOn (m.restrict (conePts σ I) (conePts_ne_zero σ I)) σ d f = supNorm m σ I d f :=
  rfl

end On

section Gauss

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem ptNorm_le_ptNorm_maxMetric (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (hz : z ≠ 0) (hle : ‖z‖ ≤ h.ρ z) :
    ptNorm h σ d f z ≤ ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos ((maxMetric C ι).pos z hz) d)
    (pow_le_pow_left₀ (norm_nonneg _) hle d)

theorem ptNorm_eq_ptNorm_maxMetric (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (heq : ‖z‖ = h.ρ z) :
    ptNorm h σ d f z = ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  rw [← heq]
  rfl

end Gauss

section Homog

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem eval_smul_of_isHomogeneousP {R : Type*} [CommRing R] {φ : MvPolynomial ι R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : ι → R) : eval (c • z) φ = c ^ d * eval z φ := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hφ (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem ptNormOn_smul {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) {d : ℕ}
    {f : MvPolynomial ι o} (hf : (map σ f).IsHomogeneous d) {c : C} (hc : c ≠ 0) {z : ι → C}
    (hz : z ∈ S) (hcz : c • z ∈ S) : ptNormOn m σ d f (c • z) = ptNormOn m σ d f z := by
  unfold ptNormOn
  rw [eval_smul_of_isHomogeneousP hf, m.smul c z hz hcz, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))

end Homog

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenVol
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Vol

variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

def ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : Set ℝ :=
  {r | ∃ (e : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (e + τ) ∧ h ∈ homogeneousSubmodule ι o e ∧
    aeval x g = s * aeval x h ∧ z ∈ conePts σ (coordIdeal o x) ∧ eval z (map σ h) ≠ 0 ∧
    r = ‖eval z (map σ g)‖ / (‖eval z (map σ h)‖ * m.ρ z ^ τ)}

def ratSupNorm (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) (τ : ℕ) (s : Ω) : ℝ :=
  sSup (ratVals m σ x τ s)

def supNormAll {E : Type*} [Fintype E] (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω)
    (τ : ℕ) (s : Ω) : ℝ :=
  ⨆ e, ratSupNorm (m e) (σ e) x τ s

def IsSmall {E : Type*} (m : E → ConeMetric ℂ ι) (σ : E → (o →+* ℂ)) (x : ι → Ω) (τ : ℕ) (s : Ω) : Prop :=
  ∀ e (d : ℕ) (g h : MvPolynomial ι o) (z : ι → ℂ),
    g ∈ homogeneousSubmodule ι o (d + τ) → h ∈ homogeneousSubmodule ι o d →
    aeval x g = s * aeval x h → z ∈ conePts (σ e) (coordIdeal o x) →
    ‖eval z (map (σ e) g)‖ ≤ ‖eval z (map (σ e) h)‖ * (m e).ρ z ^ τ

def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})

def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

theorem ptNorm_mem_ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) {τ : ℕ}
    {f : MvPolynomial ι o} (hf : f ∈ homogeneousSubmodule ι o τ) {z : ι → ℂ}
    (hz : z ∈ conePts σ (coordIdeal o x)) :
    ptNorm m σ τ f z ∈ ratVals m σ x τ (aeval x f) := by
  refine ⟨0, f, 1, z, by simpa using hf, ?_, by simp, hz, by simp, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule 0 1).2 (MvPolynomial.isHomogeneous_one ι o)
  · simp [ptNorm]

end Vol

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

