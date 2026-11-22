import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullPsh

variable {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

theorem comp_chart_eventuallyEq {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (g ∘ h ∘ (A'.chart j).symm) =ᶠ[𝓝 t]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm) := by
  have hc : ContinuousAt (h ∘ (A'.chart j).symm) t :=
    hh.1.continuousAt.comp ((A'.chart j).continuousAt_symm ht)
  have hmem : ∀ᶠ s in 𝓝 t, h ((A'.chart j).symm s) ∈ (A.chart k).source :=
    hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hmem] with s hs
  simp only [Function.comp_apply, (A.chart k).left_inv hs]

theorem levi_pull_nonneg {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t))
    (hn : ∀ v, 0 ≤ levi (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) v)
    (w : Fin e' → ℂ) : 0 ≤ levi (g ∘ h ∘ (A'.chart j).symm) t w := by
  rw [ReciprocityTheory.AnForm.levi_congr (comp_chart_eventuallyEq hh g j k ht hk) w,
    ReciprocityTheory.AnForm.levi_comp w (hh.2 j k t ⟨ht, hk⟩) hg]
  exact hn _

theorem chart_image_mem {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (A.chart k ∘ h ∘ (A'.chart j).symm) t ∈ (A.chart k).target ∧
      (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) = h ((A'.chart j).symm t) := by
  exact ⟨(A.chart k).map_source hk, (A.chart k).left_inv hk⟩

theorem contDiffAt_of_smoothOn {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) (k : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart k).target)
    (hzU : (A.chart k).symm z ∈ U) : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) z := by
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target hU
  exact (hf k).contDiffAt (ho.mem_nhds ⟨hz, hzU⟩)

theorem smoothOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    A'.SmoothOn (h ⁻¹' U) (f ∘ h) := by
  intro j
  have key : ∀ t ∈ (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (h ⁻¹' U),
      ContDiffAt ℝ ∞ ((f ∘ h) ∘ (A'.chart j).symm) t := by
    rintro t ⟨ht, htU⟩
    obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm t))
    have hF : AnalyticAt ℂ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hh.2 j k t ⟨ht, hk⟩
    have hF' : ContDiffAt ℂ ∞ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hF.contDiffAt
    have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
    have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) ∈ U := by
      rw [hci.2]; exact htU
    have hfk : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) :=
      contDiffAt_of_smoothOn hU hf k hci.1 hzU
    have hcomp : ContDiffAt ℝ ∞ ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm)) t :=
      hfk.comp t (hF'.restrict_scalars ℝ)
    exact hcomp.congr_of_eventuallyEq (comp_chart_eventuallyEq hh f j k ht hk)
  intro t ht
  exact (key t ht).contDiffWithinAt

theorem isPsh_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} (hP : IsPotential A P) (hpsh : IsPsh A P) :
    IsPsh A' (P.pullback h hh.1) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 (P.φ (h x) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    (contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzU).of_le h2
  exact levi_pull_nonneg hh (P.φ (h x)) j k hy.1 hk hg (fun v => hpsh (h x) k _ ⟨hci.1, hzU⟩ v) w

theorem isPshOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} {U : Set X} {f : X → ℝ} (hU : IsOpen U)
    (hP : IsPotential A P) (hf : A.SmoothOn U f) (hpsh : IsPshOn A U (P + LocPot.ofFun f)) :
    IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2.1.1
  have hyU : h ((A'.chart j).symm y) ∈ U := hy.2.2
  have hzP : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ U := by
    rw [hci.2]; exact hyU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 ((fun z => P.φ (h x) z + f z) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    ((contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzP).add
      (contDiffAt_of_smoothOn hU hf k hci.1 hzU)).of_le h2
  have hmem : (A.chart k ∘ h ∘ (A'.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((P + LocPot.ofFun f).U (h x) ∩ U) :=
    ⟨hci.1, ⟨hzP, Set.mem_univ _⟩, hzU⟩
  exact levi_pull_nonneg hh (fun z => P.φ (h x) z + f z) j k hy.1 hk hg
    (fun v => hpsh (h x) k _ hmem v) w

theorem pullPsh : PullPshStatement := by
  intro e e' X X' _ _ A A' h hh P U f hU hP
  exact ⟨fun hf => smoothOn_pull hh hU hf, fun hpsh => isPsh_pull hh hP hpsh,
    fun hf hpsh => isPshOn_pull hh hU hP hf hpsh⟩

end PullPsh

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddingsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_twist_eq_union_embeddings : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ), p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q → fibre (twist p Q) Ψ y = embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪ embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FinitePrimesSumSquaresZero
section
namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add, map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add, map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainUnitaryTriangularStatement
section
open Complex Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.removable_log_growth_singularity : ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ → DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} → (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) → ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) :
    gramLog hd m (cellMat N z) = logDetFlag N hd m hm z := by
  let e : Fin m ≃ {a : Fin N // (a : ℕ) < m} :=
    { toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hdet : (gramHead hd m (cellMat N z)).det =
      (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix
        (Fin.castLE hm) (Fin.castLE hm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]
    rfl
  delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag
  rw [hdet]

theorem contDiffAt_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N) :
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 := by
  have hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z| :=
    logDetFlag_eq N hd m hm
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) =
      fun z => 1 / 2 * Real.log (detGram N hd m hm z) := by
    funext z
    rw [gramLog_cellMat N hd m hm z, hE]
    simp only [Real.log_abs]
  rw [hf]
  obtain ⟨hC, h0, -⟩ := detGram_deriv N hd m hm
  have hne : detGram N hd m hm 0 ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _
  exact contDiffAt_const.mul (hC.contDiffAt.log hne)

theorem levi_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (w : Pairs N → ℂ) :
    levi (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0 := by
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm := by
    funext z
    exact gramLog_cellMat N hd m hm z
  rw [hf]
  exact homDensity N hd hd0 m hm w

theorem sigForm_ne_zero (N j : ℕ) (k : Fin N) : sigForm N j k ≠ 0 := by
  delta GlobalTheory.CompanionTheory.Ar.PB.sigForm
  split_ifs <;> norm_num

theorem levi_stepPot_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ), let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j); ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧ levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w = ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2) then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  intro N j hj i w
  dsimp only
  have hs := sigForm_ne_zero N j
  have hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1 := fun k => rfl
  have G : ∀ m, m ≤ N →
      ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 :=
    fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm
  have Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0 :=
    fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w
  have hi := i.2
  by_cases hij : (i : ℕ) + 1 ≤ j
  · have h1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have h0 : N - j ≤ N := by omega
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) +
          (-1) * gramLog (sigForm N j) (N - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_pos hij]
      ring
    rw [hfun]
    refine ⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_
    rw [Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring
  · have h1 : N - j ≤ N := by omega
    have h2 : (i : ℕ) + 1 - j ≤ N := by omega
    have hN : N ≤ N := le_refl N
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) +
          1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_neg hij]
      ring
    have GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0 :=
      (G _ hN).add (contDiffAt_const.mul (G _ h1))
    rw [hfun]
    refine ⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_
    rw [levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]
    rw [Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open GlobalTheory.CompanionTheory.Ar.FlagBun

def IsGenFam (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) : Prop :=
  (∀ s a, u s a a = 1) ∧ (∀ s a b, a < b → u s a b = 0) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) = ⊤

def revInv {G : Type} [Field G] {r : ℕ} (u : Matrix (Fin r) (Fin r) G) : Matrix (Fin r) (Fin r) G :=
  (u.transpose⁻¹).submatrix Fin.rev Fin.rev

theorem genU_isGenFam (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : IsGenFam Ω (GenField Ω r) (genU Ω r) := by
  have hdiag : ∀ s (a : Fin (r s)), genU Ω r s a a = 1 := fun s a => by
    simp [genU]
  have habove : ∀ s (a b : Fin (r s)), a < b → genU Ω r s a b = 0 := fun s a b h => by
    simp [genU, not_lt.2 h.le, h.ne]
  have hbelow : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
      genU Ω r q.1 q.2.1.1 q.2.1.2 =
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) :=
    fun q => by
      simp only [genU]
      exact dif_pos q.2.2
  refine ⟨hdiag, habove, ?_, ?_⟩
  · have hinj : Function.Injective
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) := by
      rw [IsScalarTower.coe_toAlgHom']
      exact IsFractionRing.injective _ _
    have hX := (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map' hinj
    have hfun : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) ∘ MvPolynomial.X := by
      funext q
      exact hbelow q
    rw [hfun]
    exact hX
  · rw [eq_top_iff]
    intro x _
    have hXmem : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro q
      rw [← hbelow q]
      exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1⟩, rfl⟩
    have hA : ∀ a : MvPolynomial (GenIx r) Ω,
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) a ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro a
      induction a using MvPolynomial.induction_on
      · rename_i c
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
      · rename_i p q hp hq
        rw [map_add]
        exact add_mem hp hq
      · rename_i p i hp
        rw [map_mul]
        exact mul_mem hp (hXmem i)
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) x
    exact div_mem (hA a) (hA b)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfArithSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem exists_family_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  rintro ⟨II, hII, -⟩
  exact ⟨II, hII⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_cofactor_expansion : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap ℂ (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mdisc_split_fibre_direction | exact GlobalTheory.CompanionTheory.Ar.PB.mdisc_split_fibre_direction | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mdisc_split_fibre_direction <;> assumption)
end

