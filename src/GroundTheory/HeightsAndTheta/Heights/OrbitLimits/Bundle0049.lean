import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace CurveVerticalPointChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem prod_pow_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e f : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e + f) k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

theorem form_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine form_add hf ?_
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

theorem form_C (n : ℤ) : IsMultiHomog (C n : MRing ι) 0 := by
  classical
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst this
  simp

theorem mem_of_aeval_eq (y : (Σ k, ι k) → Ω) {W : Ideal (MRing ι)} (hPW : mCoordIdeal y ≤ W)
    {f g : MRing ι} {a a' : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a') (haa : a = a')
    (he : aeval y f = aeval y g) (hfW : f ∈ W) : g ∈ W := by
  subst haa
  have h0 : f - g ∈ mCoordIdeal y :=
    HilbertSamuel.SmallSectionsNonzero.mem_mCoordIdeal_of_aeval_eq_zero y (form_sub hf hg)
      (by rw [map_sub, he, sub_self])
  have h1 := W.sub_mem hfW (hPW h0)
  rwa [sub_sub_cancel] at h1

theorem chartMono_notMem {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (e : K → ℕ) :
    HilbertSamuel.SmallSectionsNonzero.chartMono c e ∉ W := by
  classical
  rw [HilbertSamuel.SmallSectionsNonzero.chartMono, Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hc k (hWp.mem_of_pow_mem _ hk)

theorem mem_of_chartMono_mul {W : Ideal (MRing ι)} (hWp : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {e : K → ℕ} {f : MRing ι}
    (h : HilbertSamuel.SmallSectionsNonzero.chartMono c e * f ∈ W) : f ∈ W :=
  (hWp.mem_or_mem h).resolve_left (chartMono_notMem hWp hc e)

theorem exists_rep (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRingZ y c) :
    ∃ (e : K → ℕ) (k : MRing ι), IsMultiHomog k e ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k := by
  obtain ⟨e, k, hk, he⟩ :=
    HilbertSamuel.SmallSectionsNonzero.exists_form_of_mem_chartRingZ y c hyc hr
  exact ⟨e, k, hk, he.symm⟩

theorem mem_chart (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : curveRing y) :
    (b : Ω) ∈ chartRingZ y c :=
  mem_curveRing.mp b.2 c hyc

def chartPrime (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι)) : Set Ω :=
  {r | ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧ g ∈ W ∧ r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y g}

theorem mem_chartPrime_iff (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) {r : Ω}
    {e : K → ℕ} {k : MRing ι} (hk : IsMultiHomog k e) (hr : r * ∏ k, y ⟨k, c k⟩ ^ e k = aeval y k) :
    r ∈ chartPrime y c W ↔ k ∈ W := by
  constructor
  · rintro ⟨d, g, hg, hgW, hd⟩
    apply mem_of_chartMono_mul hWp hc (e := d)
    refine mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d) hk)
      (add_comm e d) ?_ (W.mul_mem_left _ hgW)
    simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * hr
  · intro hkW
    exact ⟨e, k, hk, hkW, hr⟩

theorem chartPrime_add (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)} {r r' : Ω}
    (hr : r ∈ chartPrime y c W) (hr' : r' ∈ chartPrime y c W) : r + r' ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, g', hg', hg'W, he⟩ := hr'
  have h1 := Inter.AvoidRing.isMultiHomog_mul hg (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
  have h2 := Inter.AvoidRing.isMultiHomog_mul hg' (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d)
  rw [add_comm e d] at h2
  refine ⟨d + e, _, form_add h1 h2, W.add_mem (W.mul_mem_right _ hgW) (W.mul_mem_right _ hg'W), ?_⟩
  simp only [map_add, map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
  rw [prod_pow_add]
  linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hd + (∏ k, y ⟨k, c k⟩ ^ d k) * he

theorem chartPrime_mul (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {W : Ideal (MRing ι)} {a r : Ω} (ha : a ∈ chartRingZ y c) (hr : r ∈ chartPrime y c W) :
    a * r ∈ chartPrime y c W := by
  obtain ⟨d, g, hg, hgW, hd⟩ := hr
  obtain ⟨e, k, hk, hae⟩ := exists_rep y hyc ha
  refine ⟨e + d, k * g, Inter.AvoidRing.isMultiHomog_mul hk hg, W.mul_mem_left _ hgW, ?_⟩
  rw [map_mul, prod_pow_add]
  linear_combination (r * ∏ k, y ⟨k, c k⟩ ^ d k) * hae + (aeval y k) * hd

def chartPrimeB (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (W : Ideal (MRing ι))
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Ideal (curveRing y) where
  carrier := {b | (b : Ω) ∈ chartPrime y c W}
  add_mem' {a b} ha hb := by
    change ((a : Ω) + b) ∈ chartPrime y c W
    exact chartPrime_add y ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, W.zero_mem, by simp⟩
  smul_mem' a b hb := by
    change ((a : Ω) * b) ∈ chartPrime y c W
    exact chartPrime_mul y hyc (mem_chart y hyc a) hb

theorem mem_chartPrimeB {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    {hyc : ∀ k, y ⟨k, c k⟩ ≠ 0} {b : curveRing y} : b ∈ chartPrimeB y c W hyc ↔ (b : Ω) ∈ chartPrime y c W :=
  Iff.rfl

theorem chartPrimeB_isPrime (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : (chartPrimeB y c W hyc).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff y hPW hWp hc (r := ((1 : curveRing y) : Ω)) (e := 0) (k := 1)
      Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartPrimeB.mp h)
    exact hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep y hyc (mem_chart y hyc a)
    obtain ⟨e', k', hk', hb⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkk : k * k' ∈ W := (mem_chartPrime_iff y hPW hWp hc (r := ((a * b : curveRing y) : Ω))
      (Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [Subring.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e' k) * ha + (aeval y k) * hb)).mp
      (mem_chartPrimeB.mp hab)
    rcases hWp.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem curvePtIdeal_eq (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) : curvePtIdeal y W = chartPrimeB y c W hyc := by
  apply le_antisymm
  · rw [curvePtIdeal, Ideal.span_le]
    rintro b ⟨δ, g, h, hg, hh, hgW, hhW, hb⟩
    obtain ⟨e, k, hk, hbk⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hkh : k * h ∈ W := mem_of_aeval_eq y hPW
      (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hg)
      (Inter.AvoidRing.isMultiHomog_mul hk hh) rfl
      (by
        simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
        linear_combination (-(∏ k, y ⟨k, c k⟩ ^ e k)) * hb + (aeval y h) * hbk)
      (W.mul_mem_left _ hgW)
    exact ⟨e, k, hk, (hWp.mem_or_mem hkh).resolve_right hhW, hbk⟩
  · intro b hb
    obtain ⟨d, g, hg, hgW, hd⟩ := mem_chartPrimeB.mp hb
    apply Ideal.subset_span
    refine ⟨d, g, HilbertSamuel.SmallSectionsNonzero.chartMono c d, hg,
      HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c d, hgW, chartMono_notMem hWp hc d, ?_⟩
    rw [HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
    exact hd

theorem chartPrimeB_isMaximal (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} {W : Ideal (MRing ι)}
    (hB : Module.Finite ℤ (curveRing y))
    (hPW : mCoordIdeal y ≤ W) (hWp : W.IsPrime) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {n : ℤ} (hn : n ≠ 0) (hnW : (C n : MRing ι) ∈ W) :
    (chartPrimeB y c W hyc).IsMaximal := by
  have := chartPrimeB_isPrime y hPW hWp hc hyc
  have hnm : (n : curveRing y) ∈ chartPrimeB y c W hyc := by
    refine mem_chartPrimeB.mpr ⟨0, C n, form_C n, hnW, ?_⟩
    simp
  have : Module.Finite ℤ (curveRing y ⧸ chartPrimeB y c W hyc) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (chartPrimeB y c W hyc)).toLinearMap
      Ideal.Quotient.mk_surjective
  have htor : Module.IsTorsion ℤ (curveRing y ⧸ chartPrimeB y c W hyc) := by
    intro x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    show n • Ideal.Quotient.mk _ b = 0
    rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk (chartPrimeB y c W hyc)), ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hnm
  have : Finite (curveRing y ⧸ chartPrimeB y c W hyc) := Module.finite_of_fg_torsion _ htor
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

def locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) : Subring Ω where
  carrier := {r | ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a}
  mul_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul]
    linear_combination ((b' : Ω) * r') * h + (a : Ω) * h'
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  add_mem' {r r'} := by
    rintro ⟨a, b, hb, h⟩ ⟨a', b', hb', h'⟩
    refine ⟨a * b' + b * a', b * b', fun h'' => (hm.mem_or_mem h'').elim hb hb', ?_⟩
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_mul, Subring.coe_mul]
    linear_combination (b' : Ω) * h + (b : Ω) * h'
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, by simp⟩
  neg_mem' {r} := by
    rintro ⟨a, b, hb, h⟩
    refine ⟨-a, b, hb, ?_⟩
    rw [Subring.coe_neg]
    linear_combination -h

theorem mem_locSub {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} {hm : m.IsPrime} {r : Ω} :
    r ∈ locSub y m hm ↔ ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * r = a :=
  Iff.rfl

theorem chart_le_locSub (y : (Σ k, ι k) → Ω) (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y m hm) {r : Ω} (hr : r ∈ chartRingZ y c) :
    r ∈ locSub y m hm := by
  rw [chartRingZ] at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap n =>
    rw [algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ n
  | add x x' _ _ hx hx' => exact add_mem hx hx'
  | mul x x' _ _ hx hx' => exact mul_mem hx hx'

end CurveVerticalPointChart

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MemMCoordIdealIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.SectionBounded

noncomputable section

namespace CurveVerticalPointSurjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ringHom_aeval {A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] (f : A →+* A')
    (z : (Σ k, ι k) → A) (g : MRing ι) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hg, mul_eq_zero, C_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (hg : IsMultiHomog g d) (h : aeval y f = aeval y g) :
    f - g ∈ mCoordIdeal y := by
  rw [mem_mCoordIdeal_iff y (homog_sub hf hg), map_sub, h, sub_self]

omit [Fintype K] in

theorem homogD {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : a = b) : IsMultiHomog f b :=
  h ▸ hf

omit [∀ k, Fintype (ι k)] in

theorem prod_pow_add {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e₁ e₂ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (e₁ + e₂) k = (∏ k, y ⟨k, c k⟩ ^ e₁ k) * ∏ k, y ⟨k, c k⟩ ^ e₂ k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

omit [∀ k, Fintype (ι k)] in

theorem chartMon_notMem {Q : Ideal (MRing ι)} (hQ : Q.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ Q) (n : K → ℕ) : chartMon c n ∉ Q := by
  intro h
  rw [chartMon] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ)).mp h
  exact hc k (hQ.mem_of_pow_mem _ hk)

theorem exists_form {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (b : curveRing y) :
    ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧ aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k :=
  exists_form_of_mem_chartRingZ y c hc (mem_curveRing.mp b.2 c hc)

def formSet {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (Q : Ideal (MRing ι)) :
    Set (curveRing y) :=
  {b | ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧
    aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q}

def formIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (Q : Ideal (MRing ι)) : Ideal (curveRing y) where
  carrier := formSet y c Q
  add_mem' := by
    classical
    rintro b₁ b₂ ⟨e₁, g₁, hg₁, hv₁, hQ₁⟩ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    refine ⟨e₁ + e₂, g₁ * chartMon c e₂ + g₂ * chartMon c e₁,
      homog_add (homog_mul hg₁ (homog_chartMon c e₂))
        (homogD (homog_mul hg₂ (homog_chartMon c e₁)) (add_comm _ _)), ?_,
      Q.add_mem (Q.mul_mem_right _ hQ₁) (Q.mul_mem_right _ hQ₂)⟩
    rw [map_add, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hv₁, hv₂, prod_pow_add,
      Subring.coe_add]
    ring
  zero_mem' := ⟨0, 0, homog_zero _, by simp, Q.zero_mem⟩
  smul_mem' := by
    rintro b b₂ ⟨e₂, g₂, hg₂, hv₂, hQ₂⟩
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine ⟨e + e₂, h * g₂, homog_mul hh hg₂, ?_, Q.mul_mem_left _ hQ₂⟩
    rw [map_mul, hv, hv₂, prod_pow_add, smul_eq_mul, Subring.coe_mul]
    ring

theorem mem_formIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {hc : ∀ k, y ⟨k, c k⟩ ≠ 0}
    {Q : Ideal (MRing ι)} {b : curveRing y} :
    b ∈ formIdeal y c hc Q ↔ ∃ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e ∧
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k ∧ g ∈ Q :=
  Iff.rfl

theorem le_of_minimal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hfin : Module.Finite ℤ (curveRing y)) (m : Ideal (curveRing y)) (hm : m.IsMaximal)
    (W Q : Ideal (MRing ι)) (hQ : Q.IsPrime) (hPQ : mCoordIdeal y ≤ Q) (hQW : Q ≤ W)
    (hXc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W)
    (hWB : ∀ {g : MRing ι} {e : K → ℕ} (b : curveRing y), IsMultiHomog g e →
      aeval y g = (b : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k → (g ∈ W ↔ b ∈ m))
    (hWfrac : ∀ {f : MRing ι} {n : K → ℕ}, IsMultiHomog f n → f ∈ W →
      ∃ a' b' : curveRing y, a' ∈ m ∧ b' ∉ m ∧ (b' : Ω) * aeval y f = (a' : Ω) * ∏ k, y ⟨k, c k⟩ ^ n k)
    (hWforms : IsMultiHomogIdeal W) {a b : curveRing y} (ha0 : a ≠ 0) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) (hsQ : s ∈ Q) (hbx : (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k) :
    W ≤ Q := by
  classical
  have hmonQ : ∀ n, chartMon c n ∉ Q := chartMon_notMem hQ fun k h => hXc k (hQW h)
  have htr : ∀ {f g : MRing ι} {n : K → ℕ}, IsMultiHomog f n → IsMultiHomog g n →
      aeval y f = aeval y g → g ∈ Q → f ∈ Q := by
    intro f g n hf hg he hgQ
    have h1 := Q.add_mem (hPQ (sub_mem_mCoordIdeal y hf hg he)) hgQ
    rwa [sub_add_cancel] at h1
  have hIQm : formIdeal y c hc Q ≤ m := by
    intro x hx
    obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp hx
    exact (hWB x hg hv).mp (hQW hgQ)
  have haIQ : a ∈ formIdeal y c hc Q := by
    obtain ⟨e, h, hh, hv⟩ := exists_form y c hc b
    refine mem_formIdeal.mpr ⟨e + d, h * s, homog_mul hh hs, ?_, Q.mul_mem_left _ hsQ⟩
    rw [map_mul, hv, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ e k) * hbx
  have hIQprime : (formIdeal y c hc Q).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h1
      refine hmonQ e (htr (homog_chartMon c e) hg ?_ hgQ)
      rw [aeval_chartMon, hv]
      simp
    · intro x₁ x₂ h12
      obtain ⟨e, g, hg, hv, hgQ⟩ := mem_formIdeal.mp h12
      obtain ⟨e₁, h₁, hh₁, hv₁⟩ := exists_form y c hc x₁
      obtain ⟨e₂, h₂, hh₂, hv₂⟩ := exists_form y c hc x₂
      have hf : h₁ * h₂ * chartMon c e ∈ Q := by
        refine htr (homog_mul (homog_mul hh₁ hh₂) (homog_chartMon c e))
          (homogD (homog_mul hg (homog_chartMon c (e₁ + e₂))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (e₁ + e₂)) hgQ)
        simp only [map_mul, aeval_chartMon, hv₁, hv₂, hv, prod_pow_add, Subring.coe_mul]
        ring
      rcases hQ.mem_or_mem hf with h12 | h3
      · rcases hQ.mem_or_mem h12 with h1Q | h2Q
        · exact Or.inl (mem_formIdeal.mpr ⟨e₁, h₁, hh₁, hv₁, h1Q⟩)
        · exact Or.inr (mem_formIdeal.mpr ⟨e₂, h₂, hh₂, hv₂, h2Q⟩)
      · exact absurd h3 (hmonQ e)
  have hIQmax : (formIdeal y c hc Q).IsMaximal := by
    have : Algebra.IsIntegral ℤ (curveRing y) := Algebra.IsIntegral.of_finite ℤ _
    have hcomap : (formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 haIQ (Algebra.IsIntegral.isIntegral a)
    have : ((formIdeal y c hc Q).comap (algebraMap ℤ (curveRing y))).IsPrime := Ideal.IsPrime.comap _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (IsPrime.to_maximal_ideal hcomap)
  have hIQeq : formIdeal y c hc Q = m := hIQmax.eq_of_le hm.ne_top hIQm

  obtain ⟨S, hS, hWS⟩ := hWforms
  intro f hfW
  rw [hWS] at hfW
  refine (Ideal.span_le.mpr ?_) hfW
  intro f hf
  obtain ⟨δ, hδ⟩ := hS f hf
  have hfW' : f ∈ W := by rw [hWS]; exact Ideal.subset_span hf
  obtain ⟨a', b', ha'm, hb'm, hv'⟩ := hWfrac hδ hfW'
  have ha'IQ : a' ∈ formIdeal y c hc Q := by rw [hIQeq]; exact ha'm
  obtain ⟨ea, ga, hga, hva, hgaQ⟩ := mem_formIdeal.mp ha'IQ
  obtain ⟨eb, hb, hhb, hvb⟩ := exists_form y c hc b'
  have hbQ : hb ∉ Q := by
    intro h
    have hbIQ : b' ∈ formIdeal y c hc Q := mem_formIdeal.mpr ⟨eb, hb, hhb, hvb, h⟩
    rw [hIQeq] at hbIQ
    exact hb'm hbIQ
  have h1 : hb * f * chartMon c ea ∈ Q := by
    refine htr (homog_mul (homog_mul hhb hδ) (homog_chartMon c ea))
      (homogD (homog_mul hga (homog_chartMon c (eb + δ))) (add_comm _ _)) ?_ (Q.mul_mem_right (chartMon c (eb + δ)) hgaQ)
    simp only [map_mul, aeval_chartMon, hvb, hva, prod_pow_add]
    linear_combination (∏ k, y ⟨k, c k⟩ ^ eb k) * (∏ k, y ⟨k, c k⟩ ^ ea k) * hv'
  rcases hQ.mem_or_mem h1 with h2 | h3
  · rcases hQ.mem_or_mem h2 with h4 | h5
    · exact absurd h4 hbQ
    · exact h5
  · exact absurd h3 (hmonQ ea)

theorem locLen_quot_eq_zero {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {a : R} (ha : a ∉ m) :
    locLen m (R ⧸ Ideal.span {a}) = 0 := by
  have key : ∀ w : LocalizedModule m.primeCompl (R ⧸ Ideal.span {a}), w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h x t =>
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨a, ha⟩, ?_⟩
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  have hsub : Subsingleton (LocalizedModule m.primeCompl (R ⧸ Ideal.span {a})) :=
    ⟨fun u v => by rw [key u, key v]⟩
  rw [locLen, dif_pos ‹m.IsPrime›, Module.length_eq_zero_iff.mpr hsub]
  rfl

end CurveVerticalPointSurjective

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalPointLength

theorem maximal_and_mult_eq (hCh : CurveVertPointChart.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hP : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) (hsP : s ∉ mCoordIdeal y)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
        locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
  choose c hc using hW.2
  obtain ⟨hmax, hrat, hmem⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hPW : mCoordIdeal y ≤ W := le_trans le_sup_left hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
  obtain ⟨a, b, -, hb, hab⟩ := (hmem d s hs).mp hsW
  refine ⟨hmax, ?_⟩
  rw [hMC K ι Ω y s d hP hs hsP W hW c hc a b hb hab,
    hSQ K ι Ω y s d hP hs hsP _ c hmax.isPrime hyc hrat a b hb hab]

end CurveVerticalPointLength

theorem CurveVertPointLength.proof (hCh : CurveVertPointChart.Statement) (hInj : CurveVertPointInj.Statement)
    (hSurj : CurveVertPointSurj.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) : CurveVertPointLength.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj K ι Ω y s d hP hs hsP,
      fun m hm => hSurj K ι Ω y s d hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

