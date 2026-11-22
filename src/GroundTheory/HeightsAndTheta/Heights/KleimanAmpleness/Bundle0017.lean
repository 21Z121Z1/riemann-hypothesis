import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Local

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')

def locAt : Set Ω :=
  {a | ∃ (f s : Poly k N) (e : ℕ), f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ aeval y s ≠ 0 ∧
    a = aeval x f / aeval x s}

open Classical in

def redAt (a : Ω) : K' :=
  if h : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ a = aeval x p.1 / aeval x p.2
  then aeval y h.choose.1 / aeval y h.choose.2 else 0

variable {k x y}

theorem aeval_ne_zero_of_primeOf_le (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    {s : Poly k N} {e : ℕ} (hs : s.IsHomogeneous e) (h : aeval y s ≠ 0) : aeval x s ≠ 0 := fun h0 =>
  h ((mem_primeOf_of_isHomogeneous y hs).mp (hsp ((mem_primeOf_of_isHomogeneous x hs).mpr h0)))

theorem mem_locAt {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : aeval x f / aeval x s ∈ locAt k x y :=
  ⟨f, s, e, hf, hs, h, rfl⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp

theorem redAt_eq {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : redAt k x y (aeval x f / aeval x s) = aeval y f / aeval y s := by
  have hex : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ aeval x f / aeval x s = aeval x p.1 / aeval x p.2 :=
    ⟨(f, s), e, hf, hs, h, rfl⟩
  rw [redAt, dif_pos hex]
  obtain ⟨e', hf', hs', h', heq⟩ := hex.choose_spec
  have hx := aeval_ne_zero_of_primeOf_le hsp hs h
  have hx' := aeval_ne_zero_of_primeOf_le hsp hs' h'
  rw [div_eq_div_iff hx hx'] at heq
  have hhom : (f * hex.choose.2 - hex.choose.1 * s).IsHomogeneous (e + e') := by
    refine (hf.mul hs').sub ?_
    rw [add_comm e e']; exact hf'.mul hs
  have hmem : f * hex.choose.2 - hex.choose.1 * s ∈ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x hhom]
    simp only [map_sub, map_mul, heq, sub_self]
  have hy := (mem_primeOf_of_isHomogeneous y hhom).mp (hsp hmem)
  simp only [map_sub, map_mul] at hy
  rw [div_eq_div_iff h' h]
  linear_combination -hy

theorem locAt_algebraMap (c : k) :
    algebraMap k Ω c ∈ locAt k x y ∧ redAt k x y (algebraMap k Ω c) = algebraMap k K' c := by
  have h1 : aeval y (1 : Poly k N) ≠ 0 := by simp
  have hc : algebraMap k Ω c = aeval x (C c : Poly k N) / aeval x (1 : Poly k N) := by
    simp
  rw [hc]
  refine ⟨mem_locAt (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1, ?_⟩
  rw [redAt_eq hsp (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1]
  simp

theorem locAt_zero : (0 : Ω) ∈ locAt k x y ∧ redAt k x y (0 : Ω) = 0 := by
  simpa using locAt_algebraMap hsp (0 : k)

theorem locAt_one : (1 : Ω) ∈ locAt k x y ∧ redAt k x y (1 : Ω) = 1 := by
  simpa using locAt_algebraMap hsp (1 : k)

theorem locAt_add {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a + b ∈ locAt k x y ∧ redAt k x y (a + b) = redAt k x y a + redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  have hsx' := aeval_ne_zero_of_primeOf_le hsp hs' hsy'
  have hhom : (f * s' + s * f').IsHomogeneous (e + e') := (hf.mul hs').add (hs.mul hf')
  have hsum : aeval x f / aeval x s + aeval x f' / aeval x s' =
      aeval x (f * s' + s * f') / aeval x (s * s') := by
    rw [div_add_div _ _ hsx hsx']; simp only [map_add, map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hsum]
  refine ⟨mem_locAt hhom (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp hhom (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_add_div _ _ hsy hsy']
  simp only [map_add, map_mul]

theorem locAt_mul {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a * b ∈ locAt k x y ∧ redAt k x y (a * b) = redAt k x y a * redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hprod : aeval x f / aeval x s * (aeval x f' / aeval x s') =
      aeval x (f * f') / aeval x (s * s') := by
    rw [div_mul_div_comm]; simp only [map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hprod]
  refine ⟨mem_locAt (hf.mul hf') (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp (hf.mul hf') (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_mul_div_comm]
  simp only [map_mul]

theorem locAt_pow {a : Ω} (ha : a ∈ locAt k x y) (n : ℕ) :
    a ^ n ∈ locAt k x y ∧ redAt k x y (a ^ n) = redAt k x y a ^ n := by
  induction n with
  | zero => simpa using locAt_one hsp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := locAt_mul hsp ih.1 ha
    rw [pow_succ, pow_succ]
    exact ⟨h1, by rw [h2, ih.2]⟩

theorem locAt_sum {ι : Type*} (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ locAt k x y) :
    ∑ i ∈ s, a i ∈ locAt k x y ∧ redAt k x y (∑ i ∈ s, a i) = ∑ i ∈ s, redAt k x y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locAt_zero hsp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := locAt_add hsp (ha i (Finset.mem_insert_self i s)) h1
    exact ⟨h3, by rw [h4, h2]⟩

theorem locAt_inv {a : Ω} (ha : a ∈ locAt k x y) (hr : redAt k x y a ≠ 0) :
    a ≠ 0 ∧ a⁻¹ ∈ locAt k x y ∧ redAt k x y a⁻¹ = (redAt k x y a)⁻¹ := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  rw [redAt_eq hsp hf hs hsy] at hr
  have hfy : aeval y f ≠ 0 := fun h => hr (by rw [h, zero_div])
  have hfx := aeval_ne_zero_of_primeOf_le hsp hf hfy
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  refine ⟨div_ne_zero hfx hsx, by rw [inv_div]; exact mem_locAt hs hf hfy, ?_⟩
  rw [inv_div, redAt_eq hsp hs hf hfy, redAt_eq hsp hf hs hsy, inv_div]

theorem locAt_div {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) (hr : redAt k x y b ≠ 0) :
    a / b ∈ locAt k x y ∧ redAt k x y (a / b) = redAt k x y a / redAt k x y b := by
  obtain ⟨-, h1, h2⟩ := locAt_inv hsp hb hr
  obtain ⟨h3, h4⟩ := locAt_mul hsp ha h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨h3, by rw [h4, h2]⟩

theorem chartRing_sub_locAt (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {a : Ω}
    (ha : a ∈ chartRing k x (liftChart hxy I)) :
    a ∈ locAt k x y ∧ redAt k x y a ∈ chartRing k y I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
  exact ⟨mem_locAt hf hse hsy, by rw [redAt_eq hsp hf hse hsy]; exact ⟨f, s, e, hs, hf, hse, rfl⟩⟩

theorem exists_redAt_eq (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {c : K'}
    (hc : c ∈ chartRing k y I) : ∃ a ∈ chartRing k x (liftChart hxy I), redAt k x y a = c := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  exact ⟨aeval x f / aeval x s, ⟨f, s, e, hs, hf, hse, rfl⟩,
    redAt_eq hsp hf hse (eval_ne_zero_of_mem_monos I hs)⟩

end Local

section Specialize

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}

theorem primeOf_le_primeOf_of_algHom {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') :
    primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
  have key : ∀ {B : Type w} [CommRing B] [Algebra k B] (φ : chartRing k x (singleChart hj) →ₐ[k] B)
      (g : Poly k N), φ (aeval (ratio (S := k) hj) g) = aeval (fun i => φ (ratio hj i)) g := by
    intro B _ _ φ g
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  intro f hf
  have hcomp : ∀ d, homogeneousComponent d f ∈ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    intro d
    have hg := homogeneousComponent_isHomogeneous d f
    have h0 : aeval x (homogeneousComponent d f) = 0 :=
      (mem_primeOf_of_isHomogeneous x hg).mp (homogeneousComponent_mem_primeOf x hf d)
    rw [mem_primeOf_of_isHomogeneous _ hg, ← key]
    have hval : aeval (ratio (S := k) hj) (homogeneousComponent d f) = 0 := by
      apply Subtype.ext
      have := key (chartRing k x (singleChart hj)).val (homogeneousComponent d f)
      simp only [Subalgebra.coe_val] at this
      rw [this, ZeroMemClass.coe_zero]
      change aeval (fun l => x l / x j) (homogeneousComponent d f) = 0
      rw [aeval_div_of_isHomogeneous hg j, h0, zero_div]
    rw [hval, map_zero]
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => hcomp d

theorem algHom_ratio_self {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') : ψ (ratio hj j) = 1 := by
  have : ratio (S := k) hj j = 1 := Subtype.ext (div_self hj)
  rw [this, map_one]

end Specialize

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

open Classical in

def SectionCount.Drop.Filt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) → 1 ≤ b →
    ∃ β ∈ (twistSys k x (b : ℤ)).secs,
      (∃ I, β ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub I) ∧
      ∃ (m : ℕ) (pp : Fin m → Ideal (Poly k N)) (e : Fin m → ℕ) (c : Fin m → ℤ),
        (∀ j, IsSubvar x (pp j) (e j) ∧ e j ≤ d ∧
          primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β ≤ pp j) ∧
        (∀ qq : Ideal (Poly k N),
          ((Finset.univ.filter fun j => e j = d ∧ pp j = qq).card : ℤ) =
            if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
                IsSubvar x qq d then
              haveI : qq.IsPrime := h.1.1.1
              ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ)
            else 0) ∧
        ∀ n i : ℕ,
          (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℤ) -
              (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℤ) ≤
            ∑ j, (Module.finrank k (SubSystem.quotH
              ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j)))
              (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j))).twist
                (idealSys x (pp j))) 0) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropHilbWSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.HilbW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (pp : Ideal (Poly k N)) (e : ℕ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      |(Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
          ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) : ℝ) -
        (interNum pp (fun _ : Fin e => Nb.toSubSystem) : ℝ) * (m : ℝ) ^ e / (e.factorial : ℝ)| ≤
        C * (m : ℝ) ^ e / m

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) -
          (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℝ) ≤
        (interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℝ) * (n : ℝ) ^ d / (d.factorial : ℝ) +
          C * (n : ℝ) ^ d / n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropTermSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def SectionCount.Drop.Term.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (b : ℕ) (pp : Ideal (Poly k N)) (e : ℕ) (c : ℤ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ c' : ℕ, ∀ n i : ℕ,
      Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
        ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0) ∧
      Module.finrank k (SubSystem.quotH
          ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c))
          (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c)).twist
            (idealSys x pp)) 0) ≤
        Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
          ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountTopSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Top.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) (d + 1) → IsVeryAmple Nb.toSubSystem →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def eulerCharQuot {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (SubSystem.quotH F₁ F₂ i) : ℤ)

def pieceChar (pp : Ideal (Poly k N)) (a : ℤ) {t : ℕ} (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : ℤ :=
  eulerCharQuot k
    (((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
    ((((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c))

end Defs

def IsNumPolyLT (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) : Prop :=
  ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, (Q = 0 ∨ Q.totalDegree < D) ∧
    ∀ (n : Fin t → ℕ) (c : ℤ), f n c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

variable (S x) in

def spanBundle (s : Ω) (hs : s ≠ 0) : LineBundle S x where
  sub I := Submodule.span (chartRing S x I) {s}
  mono I J h y hy := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨chartIncl h a, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨a, ha, hab⟩ := exists_isUnit_mul_mem h b
      refine ⟨a, ha, Submodule.mem_span_singleton.mpr ⟨⟨_, hab⟩, ?_⟩⟩
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      refine Submodule.mem_span_singleton.mpr ⟨(↑u⁻¹ : chartRing S x J) * chartIncl h c, ?_⟩
      rw [chartRing_smul_def, Subalgebra.coe_mul, mul_assoc]
      change (↑u⁻¹ : chartRing S x J).1 * ((c : Ω) * s) = y
      rw [← chartRing_smul_def c s, hc, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  fg _ := Submodule.fg_span_singleton s
  invertible I := ⟨Submodule.span (chartRing S x I) {s⁻¹}, by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hs, ← Submodule.one_eq_span]⟩

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubFamily.sup (F G : SubFamily S x E) : SubFamily S x E where
  sub I := F.sub I ⊔ G.sub I
  mono I J h y hy := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    exact Submodule.mem_sup.mpr ⟨a, F.mono I J h a ha, b, G.mono I J h b hb, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨u, hu, hua⟩ := (F.mem_iff I J h a).mp ha
      obtain ⟨v, hv, hvb⟩ := (G.mem_iff I J h b).mp hb
      refine ⟨u * v, by rw [map_mul]; exact hu.mul hv, ?_⟩
      have : ((u * v : chartRing S x I) : Ω) • (a + b) = v • ((u : Ω) • a) + u • ((v : Ω) • b) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul, smul_add,
          mul_comm (v : Ω) (u : Ω)]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ v hua))
        (Submodule.mem_sup_right (Submodule.smul_mem _ u hvb))
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ : (a : Ω) • y ∈ F.sub J ⊔ G.sub J := by
        obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hay
        exact Submodule.mem_sup.mpr ⟨c, F.mono I J h c hc, d, G.mono I J h d hd, hcd⟩
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ClaimSeq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x),
    ∃ Jg : FinGradedSub (S := k) (x := x) Ω,
      (∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
        f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) ∧
      ∀ (b : ℕ) (c : ℤ) (I : Chart x) (z : Ω),
        z ∈ ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I ↔
          ∃ y ∈ ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I, z = T.si * y

end

end GroundTheory.Heights₂.Heights.Kleiman
end

