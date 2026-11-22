import Mathlib

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.EulerProductSatake
section
open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors

noncomputable section

abbrev Place (K : Type) [Field K] [NumberField K] := HeightOneSpectrum (𝓞 K)

def normAt {K : Type} [Field K] [NumberField K] (w : Place K) : ℝ :=
  (Ideal.absNorm w.asIdeal : ℝ)

def zetaR (σ : ℝ) : ℝ := (riemannZeta (σ : ℂ)).re

section Euler

variable {K : Type} [Field K] [NumberField K] {ι : Type}

def localFactor (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∏ i ∈ I, (1 - x w i)⁻¹

def eulerProd (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∏' w : {w : Place K // w ∉ T}, localFactor I x w.1

def localLog (I : Finset ι) (x : Place K → ι → ℂ) (w : Place K) : ℂ :=
  ∑ i ∈ I, -Complex.log (1 - x w i)

def eulerLog (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : ℂ :=
  ∑' w : {w : Place K // w ∉ T}, localLog I x w.1

def ConvergesAbsolutely (T : Set (Place K)) (I : Finset ι) (x : Place K → ι → ℂ) : Prop :=
  (∀ w, w ∉ T → ∀ i ∈ I, ‖x w i‖ < 1) ∧
  Summable (fun w : {w : Place K // w ∉ T} => ‖localFactor I x w.1 - 1‖) ∧
  Summable (fun w : {w : Place K // w ∉ T} => ‖localLog I x w.1‖) ∧
  Multipliable (fun w : {w : Place K // w ∉ T} => localFactor I x w.1) ∧
  eulerProd T I x ≠ 0 ∧
  Complex.exp (eulerLog T I x) = eulerProd T I x

end Euler

def SatakeBound {E : Type} [Field E] [NumberField E] (T : Set (Place E)) (r : ℕ) (s : ℝ)
    (x : Place E → Fin r → ℂ) : Prop :=
  ∀ w, w ∉ T → ∀ i, ‖x w i‖ ≤ normAt w ^ (((r : ℝ) - 1) / 2 - s)

def twistTerm {F : Type} [Field F] [NumberField F] (ω : Place F → ℂ) (v : Place F) (i : ℕ) : ℂ :=
  ω v ^ i * ((normAt v : ℂ) ^ i)⁻¹

def dPart {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerProd S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)

def dLog {F : Type} [Field F] [NumberField F] (S : Set (Place F)) (ω : Place F → ℂ)
    (r t : ℕ) : ℂ :=
  eulerLog S (Finset.Icc (t + 1) (r + t)) (twistTerm ω)

def placesOver {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (S : Set (Place F)) : Set (Place E) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

def StandardBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f r : ℕ), Module.finrank ℚ E = 2 * f →
    ∀ (s : ℝ), 7 / 2 ≤ s - ((r : ℝ) - 1) / 2 →
    ∀ (T : Set (Place E)) (x : Place E → Fin r → ℂ), SatakeBound T r s x →
      ConvergesAbsolutely T Finset.univ x ∧
      ‖eulerLog T Finset.univ x‖ ≤ 2 * f * r * Real.log (zetaR (7 / 2)) ∧
      |Real.log ‖eulerProd T Finset.univ x‖| ≤ 2 * f * r * Real.log (zetaR (7 / 2)) ∧
      2 * f * r * Real.log (zetaR (7 / 2)) ≤ 0.24 * f * r

def NormalisingBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f r t : ℕ), Module.finrank ℚ F = f →
    Odd t → r + 5 ≤ t →
    ∀ (S : Set (Place F)) (ω : Place F → ℂ), (∀ v, v ∉ S → ‖ω v‖ ≤ 1) →
      ConvergesAbsolutely S (Finset.Icc (t + 1) (r + t)) (twistTerm ω) ∧
      (∀ i ∈ Finset.Icc (t + 1) (r + t), ConvergesAbsolutely S {i} (twistTerm ω)) ∧
      dPart S ω r t = ∏ i ∈ Finset.Icc (t + 1) (r + t), eulerProd S {i} (twistTerm ω) ∧
      ((∀ v, v ∉ S → (ω v).im = 0) → (dPart S ω r t).im = 0 ∧ 0 < (dPart S ω r t).re) ∧
      ‖dLog S ω r t‖ ≤ f * r * Real.log (zetaR ((t : ℝ) + 1)) ∧
      |Real.log ‖dPart S ω r t‖| ≤ f * r * Real.log (zetaR ((t : ℝ) + 1)) ∧
      f * r * Real.log (zetaR ((t : ℝ) + 1)) ≤ 0.005 * f * r

def QuotientBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (f r t : ℕ), Module.finrank ℚ F = f → Module.finrank F E = 2 → Odd t → r + 5 ≤ t →
    ∀ (S : Set (Place F)) (ω : Place F → ℂ), (∀ v, v ∉ S → ‖ω v‖ ≤ 1) →
    ∀ (x : Place E → Fin r → ℂ), SatakeBound (placesOver E S) r ((1 + (t : ℝ)) / 2) x →
      eulerProd (placesOver E S) Finset.univ x ≠ 0 ∧ dPart S ω r t ≠ 0 ∧
      Complex.exp (eulerLog (placesOver E S) Finset.univ x - dLog S ω r t)
        = eulerProd (placesOver E S) Finset.univ x / dPart S ω r t ∧
      ‖eulerLog (placesOver E S) Finset.univ x - dLog S ω r t‖ ≤ (f : ℝ) * r / 4 ∧
      |Real.log ‖eulerProd (placesOver E S) Finset.univ x / dPart S ω r t‖| ≤ (f : ℝ) * r / 4

def EulerLogBounds : Prop :=
  StandardBound ∧ NormalisingBound ∧ QuotientBound

def SharpConstant : Prop :=
  2 * Real.log (zetaR (7 / 2)) ≤ 0.2387

open Classical in

def quadSign {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] (v : Place F) : ℂ :=
  if (placesOver E ({v} : Set (Place F))).ncard = 2 then 1
  else if (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime then -1 else 0

end

end GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
section
open MeasureTheory Set

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]

noncomputable def flatIntegrand (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) (x : X) : ℂ :=
  f x * ((a x : ℝ) : ℂ) ^ (s - s₀)

noncomputable def flatZeta (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) : ℂ :=
  ∫ x, flatIntegrand f a s₀ s x ∂μ

def ConvergesAbsLocUnifOn (μ : Measure X) (F : ℂ → X → ℂ) (D : Set ℂ) : Prop :=
  (∀ s ∈ D, Integrable (F s) μ) ∧
    ∀ s ∈ D, ∃ U ∈ nhdsWithin s D, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ s' ∈ U, ∀ x, ‖F s' x‖ ≤ g x

def FlatZetaHolomorphic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s₁ : ℂ),
    Measurable a → (∀ x, 0 < a x) → (∀ x, a x ≤ 1) →
    Integrable (flatIntegrand f a s₀ s₁) μ →
      ConvergesAbsLocUnifOn μ (flatIntegrand f a s₀) {s | s₁.re ≤ s.re} ∧
      DifferentiableOn ℂ (flatZeta μ f a s₀) {s | s₁.re < s.re} ∧
      ContinuousOn (flatZeta μ f a s₀) {s | s₁.re ≤ s.re}

omit [MeasurableSpace X] in

theorem flatIntegrand_self (f : X → ℂ) (a : X → ℝ) (s₀ : ℂ) : flatIntegrand f a s₀ s₀ = f := by
  funext x
  simp [flatIntegrand]

omit [MeasurableSpace X] in

theorem norm_flatIntegrand (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by
  rw [flatIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re]

example (s : ℂ) :
    Integrable (flatIntegrand (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s)
        (Measure.dirac ()) ∧
      flatZeta (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => (1 / 2 : ℝ)) 0 s
        = (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s := by
  refine ⟨?_, ?_⟩
  · exact Integrable.of_finite
  · simp [flatZeta, flatIntegrand]

end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
section
noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup

section Defs

variable (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))]

abbrev Int : Subring F := (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ))).integer

def upperBorel (r : ℕ) (k : Type) [CommRing k] : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k).BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun {g} hg => by
    have := g.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular hg
    simpa [Matrix.coe_units_inv] using h

def maxId : Ideal (Int F) where
  carrier := {x | Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ))}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simpa using Valuation.map_add_lt _ ha hb
  smul_mem' := fun c x hx => by
    have hc : Valued.v (c : F) ≤ (1 : WithZero (Multiplicative ℤ)) := c.2
    have hx' : Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ)) := hx
    show Valued.v ((c * x : Int F) : F) < (1 : WithZero (Multiplicative ℤ))
    rw [Subring.coe_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx'

def iwahoriInt (r : ℕ) : Subgroup (GL (Fin r) (Int F)) :=
  (upperBorel r (Int F ⧸ maxId F)).comap
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)))

def iwahori (r : ℕ) : Subgroup (GL (Fin r) F) :=
  (iwahoriInt F r).map (Matrix.GeneralLinearGroup.map (Int F).subtype)

variable {F}

def diagPow {r : ℕ} (ϖ : F) (a : Fin r → ℤ) : Matrix (Fin r) (Fin r) F :=
  Matrix.diagonal fun i => ϖ ^ a i

def iwahoriDoubleCoset {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : Set (Matrix (Fin r) (Fin r) F) :=
  {g | ∃ i₁ ∈ iwahori F r, ∃ i₂ ∈ iwahori F r,
    g = (i₁ : Matrix (Fin r) (Fin r) F) * t * (i₂ : Matrix (Fin r) (Fin r) F)}

end Defs

def IwahoriEigenvalues : Prop :=
  ∀ (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] [CompleteSpace F]
    (ϖ : F), Valued.v ϖ = WithZero.exp (-1 : ℤ) →
    ∀ (r : ℕ) (a : Fin r → ℤ), StrictAnti a →
    ∀ g ∈ iwahoriDoubleCoset (diagPow ϖ a),
      (∃ x : Fin r → F, Function.Injective x ∧
        g.charpoly = ∏ i, (X - C (x i)) ∧
        ∀ i, Valued.v (x i) = WithZero.exp (-(a i))) ∧
      g.charpoly.Separable

theorem mem_iwahoriInt_iff (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] (r : ℕ)
    (g : GL (Fin r) (Int F)) :
    g ∈ iwahoriInt F r ↔ ∀ i j : Fin r, j < i →
      Valued.v (((g : Matrix (Fin r) (Fin r) (Int F)) i j : Int F) : F)
        < (1 : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro h i j hij
    have := h (i := i) (j := j) hij
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · intro h i j hij
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h i j hij)

theorem self_mem_iwahoriDoubleCoset {F : Type} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : t ∈ iwahoriDoubleCoset t :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

example (h : IwahoriEigenvalues) (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (r : ℕ) (a : Fin r → ℤ)
    (ha : StrictAnti a) : (diagPow ϖ a).charpoly.Separable :=
  (h _ ϖ hϖ r a ha _ (self_mem_iwahoriDoubleCoset _)).2

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LowerUnipotentMinors
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials

open MvPolynomial Matrix MeasureTheory

abbrev Var (n p q : ℕ) := Fin n × (Fin p ⊕ Fin q)

abbrev Pol (n p q : ℕ) := MvPolynomial (Var n p q) ℂ

def zPlus (n p q : ℕ) : Matrix (Fin n) (Fin p) (Pol n p q) := fun c a => X (c, Sum.inl a)

def zMinus (n p q : ℕ) : Matrix (Fin n) (Fin q) (Pol n p q) := fun c b => X (c, Sum.inr b)

def subst {n p q : ℕ} (yp : Matrix (Fin n) (Fin p) (Pol n p q))
    (ym : Matrix (Fin n) (Fin q) (Pol n p q)) : Pol n p q →ₐ[ℂ] Pol n p q :=
  aeval fun v : Var n p q => Sum.elim (fun a => yp v.1 a) (fun b => ym v.1 b) v.2

def nextRow {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : i.val + 1 < l then a ⟨i.val + 1, h⟩ else 0

section Minors

variable {R : Type*} [CommRing R] {n l : ℕ}

def topMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det

def botMinor (hl : l ≤ n) (y : Matrix (Fin n) (Fin l) R) (i : Fin l) : R :=
  (y.submatrix (fun k : Fin (i.val + 1) => (⟨n - (i.val + 1) + k.val, by omega⟩ : Fin n))
    (fun k : Fin (i.val + 1) => (⟨k.val, by omega⟩ : Fin l))).det

def powProd (a : Fin l → ℕ) (m : Fin l → R) : R := ∏ i, m i ^ (a i - nextRow a i)

end Minors

def delPlus {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) : Pol n p q :=
  powProd ap (topMinor (by omega) (zPlus n p q))

def delMinus {n p q : ℕ} (h : p + q ≤ n) (am : Fin q → ℕ) : Pol n p q :=
  powProd am (botMinor (by omega) (zMinus n p q))

def del {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ) : Pol n p q :=
  delPlus h ap * delMinus h am

def lower {n p q : ℕ} (a : Fin p) (b : Fin q) (P : Pol n p q) : Pol n p q :=
  ∑ c : Fin n, pderiv (c, Sum.inl a) (pderiv (c, Sum.inr b) P)

def leftAct {n : ℕ} (p q : ℕ) (h : GL (Fin n) ℂ) : Pol n p q →ₐ[ℂ] Pol n p q :=
  subst (((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map C * zPlus n p q)
    ((h : Matrix (Fin n) (Fin n) ℂ)ᵀ.map C * zMinus n p q)

def rightMul (n : ℕ) {p q : ℕ} (m₁ : Matrix (Fin p) (Fin p) ℂ) (m₂ : Matrix (Fin q) (Fin q) ℂ) :
    Pol n p q →ₐ[ℂ] Pol n p q :=
  subst (zPlus n p q * m₁.map C) (zMinus n p q * m₂.map C)

def compactAct (n : ℕ) {p q : ℕ} (k₁ : Matrix (Fin p) (Fin p) ℂ) (w₁ : ℂˣ)
    (k₂ : Matrix (Fin q) (Fin q) ℂ) (w₂ : ℂˣ) (P : Pol n p q) : Pol n p q :=
  ((w₁ ^ (n : ℤ) * w₂ ^ (-(n : ℤ)) : ℂˣ) : ℂ) • rightMul n k₁ (k₂.map (starRingEnd ℂ)) P

def IsLowerUnipotent {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, i < j → u i j = 0

def IsUpperUnipotent {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def fockForm {σ : Type*} [DecidableEq σ] (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ P.support ∪ Q.support,
    ((α.prod fun _ k => k.factorial : ℕ) : ℂ) * coeff α P * starRingEnd ℂ (coeff α Q)

def fockDensity {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℂ) (z : σ → ℂ) : ℝ :=
  ‖eval z P‖ ^ 2 * Real.exp (-∑ v, ‖z v‖ ^ 2) / Real.pi ^ Fintype.card σ

def hookProd {l : ℕ} (a : Fin l → ℕ) : ℝ :=
  (∏ i : Fin l, ((a i + (l - (i.val + 1))).factorial : ℝ)) /
    ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, ((a i : ℝ) - (a j : ℝ) + (j.val : ℝ) - (i.val : ℝ))

section Clauses

variable {n p q : ℕ} (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ)

def KilledByLower : Prop := ∀ (a : Fin p) (b : Fin q), lower a b (del h ap am) = 0

def LeftFixed : Prop :=
  ∀ g : GL (Fin n) ℂ, IsLowerUnipotent (g : Matrix (Fin n) (Fin n) ℂ) →
    leftAct p q g (del h ap am) = del h ap am

def RightFixed : Prop :=
  ∀ (u₁ : Matrix (Fin p) (Fin p) ℂ) (u₂ : Matrix (Fin q) (Fin q) ℂ),
    IsUpperUnipotent u₁ → IsUpperUnipotent u₂ → rightMul n u₁ u₂ (del h ap am) = del h ap am

def LeftWeight : Prop :=
  ∀ (t : Fin n → ℂˣ) (g : GL (Fin n) ℂ),
    (g : Matrix (Fin n) (Fin n) ℂ) = diagonal (fun c => (t c : ℂ)) →
    leftAct p q g (del h ap am) =
      (((∏ c : Fin p, t ⟨c.val, by omega⟩ ^ (-(ap c : ℤ))) *
        ∏ i : Fin q, t ⟨n - 1 - i.val, by omega⟩ ^ (am i : ℤ) : ℂˣ) : ℂ) • del h ap am

def RightWeight : Prop :=
  ∀ (s : Fin p → ℂˣ) (s' : Fin q → ℂˣ),
    rightMul n (diagonal fun a => (s a : ℂ)) (diagonal fun b => (s' b : ℂ)) (del h ap am) =
      (((∏ a, s a ^ ap a) * ∏ b, s' b ^ am b : ℂˣ) : ℂ) • del h ap am

def CompactWeight : Prop :=
  ∀ (u : Fin p → ℂˣ) (v : Fin q → ℂˣ), (∀ a, ‖(u a : ℂ)‖ = 1) → (∀ b, ‖(v b : ℂ)‖ = 1) →
    compactAct n (diagonal fun a => (u a : ℂ) ^ 2) (∏ a, u a)
        (diagonal fun b => (v b : ℂ) ^ 2) (∏ b, v b) (del h ap am) =
      (((∏ a, u a ^ (2 * (ap a : ℤ) + n)) * ∏ b, v b ^ (-(2 * (am b : ℤ)) - n) : ℂˣ) : ℂ) •
        del h ap am

def NormSq : Prop :=
  fockForm (del h ap am) (del h ap am) = ((hookProd ap * hookProd am : ℝ) : ℂ)

def NormSqIntegral : Prop :=
  Integrable (fockDensity (del h ap am)) ∧
    ∫ z, fockDensity (del h ap am) z = hookProd ap * hookProd am

end Clauses

def JointHarmonic : Prop :=
  ∀ (n p q : ℕ) (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    KilledByLower h ap am ∧ LeftFixed h ap am ∧ RightFixed h ap am ∧ LeftWeight h ap am ∧
      RightWeight h ap am ∧ CompactWeight h ap am ∧ NormSq h ap am

def JointHarmonicIntegral : Prop :=
  ∀ (n p q : ℕ) (h : p + q ≤ n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    NormSqIntegral h ap am

example : hookProd ![2, 1] = 3 := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [hookProd, Fin.prod_univ_two, h0, h1, Nat.factorial]
  norm_num

example (k m : ℕ) : del (n := 2) (p := 1) (q := 1) le_rfl ![k] ![m] =
    X (0, Sum.inl 0) ^ k * X (1, Sum.inr 0) ^ m := by
  simp [del, delPlus, delMinus, powProd, nextRow, topMinor, botMinor, zPlus, zMinus,
    Matrix.det_unique]

end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
end
end

