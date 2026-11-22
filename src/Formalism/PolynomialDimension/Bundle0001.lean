import Mathlib

-- bundled from Formalism.PolynomialDimension.FrameSum
section
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

def LocTelescope : Prop :=
  ∀ (p J n' : ℕ) (z : ℕ → ℕ), (∀ j < J, z j ≤ z (j + 1)) → z J = z 0 + n' →
    (∑ j ∈ range J, (p : ℤ) ^ z j * ((p : ℤ) ^ (z (j + 1) - z j) - 1) = (p : ℤ) ^ z 0 * ((p : ℤ) ^ n' - 1)) ∧
      ∏ j ∈ range J, p ^ (z (j + 1) - z j) = p ^ n'

def swapCol (r k : ℕ) (h : r ≤ k) (i : Fin r) (c : Fin k) : Fin r → Fin k :=
  Function.update (Fin.castLE h) i c

abbrev IIdx (r k : ℕ) := Fin r × {c : Fin k // r ≤ c.val}

def GraphMinor : Prop :=
  ∀ (F : Type) [Field F] (r k : ℕ) (h : r ≤ k) (H : Matrix (Fin r) (Fin k) F),
    (H.submatrix id (Fin.castLE h)).det ≠ 0 → (∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ H i c ≠ 0) →
      ∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ (H.submatrix id (swapCol r k h i c)).det ≠ 0

def frameRow (p r k : ℕ) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A) (a : ℕ) (t : Fin r → A) :
    Fin k → A :=
  t ᵥ* H.map (fun x => x ^ p ^ a)

def piMinor (p r k : ℕ) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A) (pos : Fin r → ℕ)
    (t : Fin r → Fin r → A) (zj : ℕ) (cols : Fin r → Fin k) : A :=
  (Matrix.of fun l c' => (frameRow p r k H (pos l) (t l) (cols c')) ^ p ^ (zj - pos l)).det

def localizer (p r k J : ℕ) (h : r ≤ k) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A)
    (pos : ℕ → Fin r → ℕ) (t : ℕ → Fin r → Fin r → A) (z : ℕ → ℕ) : A :=
  piMinor p r k H (pos 0) (t 0) (z 0) (Fin.castLE h) *
    ∏ I : IIdx r k,
      (∏ j ∈ range J, piMinor p r k H (pos j) (t j) (z j) (Fin.castLE h) ^ (p ^ (z (j + 1) - z j) - 1) -
        ∏ j ∈ range J, piMinor p r k H (pos j) (t j) (z j) (swapCol r k h I.1 I.2.1) ^ (p ^ (z (j + 1) - z j) - 1))

def LocalizerVanishes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p] (n' r k J : ℕ) (h : r ≤ k),
    Fintype.card F = p ^ n' →
    ∀ z : ℕ → ℕ, (∀ j < J, z j ≤ z (j + 1)) → z J = z 0 + n' →
    ∀ (pos : ℕ → Fin r → ℕ), (∀ j < J, ∀ l, pos j l ≤ z j) →
    ∀ H : Matrix (Fin r) (Fin k) F, (∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ H i c ≠ 0) →
    ∀ (A : Type) [CommRing A] [Algebra F A] (t : ℕ → Fin r → Fin r → A),
      localizer p r k J h (H.map (algebraMap F A)) pos t z = 0

def LocExpand : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (J : ℕ) (Del : ℕ → R) (piI : ι → ℕ → R)
    (Q : ℕ → ℕ), 1 ≤ J →
    Del 0 * ∏ I, (∏ j ∈ range J, Del j ^ (Q j - 1) - ∏ j ∈ range J, piI I j ^ (Q j - 1)) =
      ∑ S : Finset ι, (-1) ^ S.card *
        (∏ j ∈ range J, Del j ^ ((if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1))) *
          ∏ I ∈ S, ∏ j ∈ range J, piI I j ^ (Q j - 1)

def NormalMinor : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (r k : ℕ) (h : r ≤ k) (M : Matrix (Fin r) (Fin k) R),
    (∀ (i : Fin r) (c : Fin k), r ≤ c.val → M i c ∈ I) →
      ∀ (i : Fin r) (c : Fin k), r ≤ c.val → (M.submatrix id (swapCol r k h i c)).det ∈ I

def borderedMatrix {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R) (T : Matrix (Fin r) (Fin r) R)
    (b : Fin r → R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of (Fin.cons (α := fun _ => Fin (r + 1) → R) (Fin.snoc (α := fun _ => R) ts u)
    (fun l => Fin.snoc (α := fun _ => R) (T l) (b l)))

def BorderedDetLinear : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (ts : Fin r → R) (T : Matrix (Fin r) (Fin r) R),
    ∃ c : Fin r → R, ∀ (u : R) (b : Fin r → R),
      (borderedMatrix r ts u T b).det = (-1) ^ r * u * T.det + ∑ l, b l * c l

def DetMulEqSumAdjugate : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (T : Matrix (Fin r) (Fin r) R) (s : Fin r → R) (a : Fin r),
    T.det * s a = ∑ l, (T *ᵥ s) l * T.adjugate a l

def KeyVanish : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] (r k : ℕ) (h : Matrix (Fin k) (Fin k) F),
    IsUnit h.det → ∀ s : ℕ,
    (∀ (A : Fin (r + 1) → ℕ) (t : Fin (r + 1) → Fin k → F) (cols : Fin (r + 1) → Fin k),
      (∀ l, A l ≤ s) → (∀ l (i : Fin k), r ≤ i.val → t l i = 0) →
        (Matrix.of fun l c => ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)).det = 0) ∧
    (∀ (a : ℕ) (t v : Fin k → F), a ≤ s → (∀ i : Fin k, r ≤ i.val → t i = 0) → (∀ i : Fin k, i.val < r → v i = 0) →
      ∑ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) *
        (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) c = 0)

def CleanInduction : Prop :=
  ∀ (M : Type) [AddCommGroup M] (Deg : AddSubgroup M) (FF FF' : ℕ → AddSubgroup M), Antitone FF → Antitone FF' →
    ∀ (τ : Type) (level : τ → ℕ) (spare : τ → ℤ × ℤ) (sym raw : τ → M) (o c' Q : ℕ),
    (∀ x, sym x ∈ Deg ∧ raw x ∈ Deg) →
    (∀ x, sym x ∈ FF (level x)) →
    (∀ x, raw x ∈ FF' (level x + c')) →
    (∀ x, level x < o + c' →
      (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - level x) ≤ (spare x).1 → ((o : ℤ) + c' - 1 - level x) ≤ (spare x).2 →
        ∃ (ch : Finset τ) (ρ : M), ρ ∈ FF (o + c') ∧ ρ ∈ Deg ∧ raw x - sym x = ∑ y ∈ ch, sym y + ρ ∧
          ∀ y ∈ ch, level x < level y ∧ level y < o + c' ∧
            spare y = ((spare x).1 - (2 * (Q : ℤ) + 1) * ((level y : ℤ) - level x),
              (spare x).2 - ((level y : ℤ) - level x))) →
    ∀ S : Finset τ, (∀ x ∈ S, o ≤ level x ∧ spare x = ((((2 * Q + 3) * c' : ℕ) : ℤ), (c' : ℤ))) →
      ∃ f : M, f ∈ Deg ∧ f - ∑ x ∈ S, sym x ∈ FF (o + c') ∧ f ∈ FF' (o + c')

def CleanArith : Prop :=
  (∀ (j v o e' Q : ℕ), j + v = o + e' → o ≤ 2 * Q → 1 ≤ e' → j ≤ (2 * Q + 1) * e') ∧
    (∀ (e c' Q : ℕ), e < c' → (2 * Q + 1) * e ≤ (2 * Q + 3) * c' ∧ e ≤ c')

def PowerSplit : Prop :=
  ∀ (R : Type) [CommRing R] (D h π : R) (P n c : ℕ), 1 ≤ P →
    (D ^ P + π * h) ^ n ∈ Ideal.span {D ^ (n - c)} ⊔ Ideal.span {π ^ c}

def Lemma4Geom : Prop :=
  ∀ (p a B : ℝ) (D0 : ℕ) (S : Finset ℕ) (d : ℕ → ℝ), 13 ≤ p → 0 < a → a / p ^ D0 ≤ B →
    (∀ m ∈ S, 1 ≤ m ∧ 0 ≤ d m ∧ d m ≤ 2.02 * a / p ^ (D0 + 2 * m)) →
      ∑ m ∈ S, d m ≤ 2.02 * B / (p ^ 2 - 1) ∧ 2.02 * B / (p ^ 2 - 1) ≤ B / 80

def Lemma4Arith : Prop :=
  ∀ (B B' sl mstar val : ℝ), 0 ≤ B → B' ≤ B / 80 → sl ≤ B / 100 → mstar ≤ sl → B / 2 - sl ≤ val →
    B / 4 + mstar ≤ val - B' ∧ mstar ≤ B / 4

def Lemma4Count : Prop :=
  ∀ (N1 ntops m kQ c' al : ℕ), ntops ≤ N1 →
    ntops * (m + kQ + c') + (c' * al + 2 * c') ≤ (N1 + 1) * (m + kQ + c' * al + 3 * c')

def factProd {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : ℕ := ∏ i, (α i).factorial

def vG {σ : Type} (p : ℕ) (F : MvPolynomial σ ℚ) : WithTop ℝ :=
  F.support.inf fun α => (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ)

def vBB {σ : Type} [Fintype σ] (p : ℕ) (F : MvPolynomial σ ℚ) : WithTop ℝ :=
  F.support.inf fun α =>
    ((((padicValRat p (F.coeff α) : ℤ) : ℝ) + (padicValNat p (factProd α) : ℝ) / 2 : ℝ) : WithTop ℝ)

def IsLetterHom {σ Z : Type} [Fintype σ] [DecidableEq Z] (letter : σ → Z) (d : Z → ℕ)
    (F : MvPolynomial σ ℚ) : Prop :=
  ∀ α ∈ F.support, ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z

def FockGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ Z : Type) [Fintype σ] [DecidableEq σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ), 0 ≤ a →
    Fintype.card σ ≤ N * k → (∀ z, (d z : ℝ) ≤ 2 * a) →
    ∀ F : MvPolynomial σ ℚ, IsLetterHom letter d F →
      vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 -
          (N * k * (Real.logb p (2 * a + k) + 1)) / 2 : ℝ) : WithTop ℝ) ≤ vBB p F ∧
        vBB p F ≤ vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 : ℝ) : WithTop ℝ)

def FrameSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Z : Type) [Fintype Z] [DecidableEq Z] (Fr : Finset Z) (r N k : ℕ) (a : ℝ)
    (d : Z → ℕ) (M : Z → Fin r → ℕ), 0 ≤ a →
    Fr.card ≤ N → r + 1 ≤ k → (∀ z, (d z : ℝ) ≤ 2 * a) → (∀ z ∈ Fr, ∑ i, M z i ≤ d z) →
      (∀ z ∈ Fr, (padicValNat p ((d z).factorial / ((d z - ∑ i, M z i).factorial * ∏ i, (M z i).factorial)) : ℝ) ≤
          (r + 1) * (Real.logb p (2 * a + k) + 1)) ∧
      2 * ((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        2 * ((padicValNat p (∏ z, (if z ∈ Fr then d z - ∑ i, M z i else d z).factorial) : ℝ) / 2) +
          (padicValNat p (∏ z ∈ Fr, ∏ i, (M z i).factorial) : ℝ)

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.StatementHar
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

abbrev XY (k : ℕ) : Type := Fin k ⊕ Fin k

abbrev PolXY (K : Type) [Field K] (k : ℕ) : Type := MvPolynomial (XY k) K

def xDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inl i)

def yDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inr i)

def xFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inl i)).factorial

def yFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inr i)).factorial

variable (K : Type) [Field K] (k : ℕ)

def hXY : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * X (Sum.inr i)

def ctrF : PolXY K k →ₗ[K] PolXY K k :=
  ∑ i : Fin k, (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap ∘ₗ
    (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap

def hDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • LinearMap.mulLeft K (hXY K k ^ l)

def ctrDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • (ctrF K k ^ l)

def PolAB (A B : ℕ) : Submodule K (PolXY K k) where
  carrier := {f | ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B}
  zero_mem' := by
    intro m hm
    simp at hm
  add_mem' := by
    intro f g hf hg m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hf m h
    · exact hg m h
  smul_mem' := by
    intro c f hf m hm
    exact hf m (MvPolynomial.support_smul hm)

def HarAB (A B : ℕ) : Submodule K (PolXY K k) := PolAB K k A B ⊓ LinearMap.ker (ctrF K k)

def harProj (A B : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ∑ l ∈ range (min A B + 1),
    ((-1 : K) ^ l / (((A + B + k - 2).choose l : ℕ) : K)) • (hDiv K k l ∘ₗ ctrDiv K k l)

def levelProj (A B j : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹) •
    (hDiv K k j ∘ₗ harProj K k (A - j) (B - j) ∘ₗ ctrDiv K k j)

def fischer (f g : PolXY K k) : K :=
  ∑ m ∈ f.support, ((xFact m : K) * (yFact m : K)) * (coeff m f * coeff m g)

variable {K k}

def glAct (g : GL (Fin k) K) : PolXY K k →ₐ[K] PolXY K k :=
  aeval (Sum.elim
    (fun i : Fin k => ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j))
    (fun i : Fin k => ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)))

def GaussLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, coeff m f ∈ R}

def FockLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, (xFact m : K) * coeff m f ∈ R}

def DualLat (R : Subring K) : Set (PolXY K k) :=
  {f | ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ∈ R}

def SqrtFockLat (R : Subring K) : Set (PolXY K k) :=
  {f | ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ^ 2 ∈ R}

def SqrtGaussLat (R : Subring K) (n : ℕ) : Set (PolXY K k) := {f | ∀ m, (n : K) * coeff m f ^ 2 ∈ R}

def latOf (g : GL (Fin k) K) (S : Set (PolXY K k)) : Set (PolXY K k) := glAct g '' S

def PLocal (R : Subring K) (p : ℕ) : Prop := ∀ n : ℕ, ¬ p ∣ n → ((n : K))⁻¹ ∈ R

def SlTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ctrF K k (hXY K k * f) - hXY K k * ctrF K k f = ((A + B + k : ℕ) : K) • f

def SlTwoPower : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b i : ℕ), 1 ≤ k → ∀ w : PolXY K k, w ∈ HarAB K k a b →
    ctrF K k (hXY K k ^ (i + 1) * w) = (((i + 1) * (a + b + k + i) : ℕ) : K) • (hXY K k ^ i * w)

def DivPowerEigen : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b : ℕ), 1 ≤ k → ∀ w : PolXY K k, w ∈ HarAB K k a b →
    (∀ i l : ℕ, hDiv K k l (ctrDiv K k l (hXY K k ^ i * w)) =
        ((i.choose l * (a + b + k + i - 1).choose l : ℕ) : K) • (hXY K k ^ i * w)) ∧
    (∀ j : ℕ, ctrDiv K k j (hDiv K k j w) = (((a + b + k + j - 1).choose j : ℕ) : K) • w)

def FischerAdjoint : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (f g : PolXY K k),
    fischer K k (hXY K k * f) g = fischer K k f (ctrF K k g)

def CtrSurj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k → ∀ g : PolXY K k, g ∈ PolAB K k A B →
    ∃ f ∈ PolAB K k (A + 1) (B + 1), ctrF K k f = g

def HarDecomp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k → ∀ f : PolXY K k, f ∈ PolAB K k A B →
    ∃! w : Fin (min A B + 1) → PolXY K k,
      (∀ j : Fin (min A B + 1), w j ∈ HarAB K k (A - (j : ℕ)) (B - (j : ℕ))) ∧
        f = ∑ j : Fin (min A B + 1), hXY K k ^ (j : ℕ) * w j

def HarDim : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k' A B : ℕ),
    Module.finrank K (PolAB K (k' + 1) A B) = (A + k').choose k' * (B + k').choose k' ∧
    Module.finrank K (HarAB K (k' + 1) (A + 1) (B + 1)) + (A + k').choose k' * (B + k').choose k' =
      (A + 1 + k').choose k' * (B + 1 + k').choose k' ∧
    HarAB K (k' + 1) A 0 = PolAB K (k' + 1) A 0 ∧ HarAB K (k' + 1) 0 B = PolAB K (k' + 1) 0 B

def HarProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B →
      harProj K k A B f ∈ HarAB K k A B ∧
      ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g) ∧
    (∀ f : PolXY K k, f ∈ HarAB K k A B → harProj K k A B f = f) ∧
    (1 ≤ A → 1 ≤ B → ∀ g : PolXY K k, g ∈ PolAB K k (A - 1) (B - 1) →
      harProj K k A B (hXY K k * g) = 0)

def LevelProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ j ≤ min A B,
      ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ i ≤ min A B, ∀ j ≤ min A B,
      levelProj K k A B i (levelProj K k A B j f) = if i = j then levelProj K k A B j f else 0) ∧
    (∀ i ≤ min A B, ∀ j ≤ min A B, ∀ w : PolXY K k, w ∈ HarAB K k (A - i) (B - i) →
      levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0)

def Canonical : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (g : GL (Fin k) K),
    glAct g (hXY K k) = hXY K k ∧
    (∀ f : PolXY K k, ctrF K k (glAct g f) = glAct g (ctrF K k f)) ∧
    (∀ (A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B → glAct g f ∈ PolAB K k A B) ∧
    (∀ (A B : ℕ) (f : PolXY K k), harProj K k A B (glAct g f) = glAct g (harProj K k A B f)) ∧
    (∀ (A B j : ℕ) (f : PolXY K k), levelProj K k A B j (glAct g f) = glAct g (levelProj K k A B j f))

def FockStable : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (R : Subring K) (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k),
    f ∈ latOf g (FockLat R) →
      hDiv K k l f ∈ latOf g (FockLat R) ∧ ctrDiv K k l f ∈ latOf g (FockLat R)

def SqrtFockStable : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K) (l : ℕ)
    (f : PolXY K k), f ∈ latOf g (SqrtFockLat O.toSubring) →
      hDiv K k l f ∈ latOf g (SqrtFockLat O.toSubring) ∧ ctrDiv K k l f ∈ latOf g (SqrtFockLat O.toSubring)

def BinomVal : Prop :=
  ∀ p : ℕ, p.Prime →
    (∀ n m : ℕ, padicValNat p (n.choose m) ≤ Nat.log p n) ∧
    (∀ k A B l j : ℕ, 1 ≤ k → l ≤ min A B → j ≤ min A B →
      (padicValNat p ((A + B + k - 2).choose l) : ℝ) ≤ Real.logb p ((A : ℝ) + B + k) ∧
      (padicValNat p ((A + B + k - 2 * j + j - 1).choose j) : ℝ) ≤ Real.logb p ((A : ℝ) + B + k)) ∧
    (∀ k A B a l j : ℕ, 1 ≤ k → A ≤ 8 * a → B ≤ 8 * a → l ≤ min A B → j ≤ min A B →
      (padicValNat p ((A + B + k - 2).choose l) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + k - 1) + 1 ∧
      (padicValNat p ((A + B + k - 2 * j + j - 1).choose j) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + k - 1) + 1)

def FockProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) →
      ((p : K) ^ Nat.log p (A + B + k)) • harProj K k A B f ∈ latOf g (FockLat R) ∧
      ∀ j ≤ min A B,
        ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (FockLat R)

def SqrtFockProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p →
    ∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (SqrtFockLat O.toSubring) →
      ((p : K) ^ Nat.log p (A + B + k)) • harProj K k A B f ∈ latOf g (SqrtFockLat O.toSubring) ∧
      ∀ j ≤ min A B,
        ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (SqrtFockLat O.toSubring)

def FockGaussXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (FockLat R) → (A.factorial : K) • f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ latOf g (FockLat R))

def SqrtFockGaussXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (SqrtFockLat O.toSubring) →
        f ∈ latOf g (SqrtGaussLat O.toSubring (A.factorial * B.factorial))) ∧
      (f ∈ latOf g (SqrtGaussLat O.toSubring (A.factorial * B.factorial)) →
        ((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f ∈ latOf g (SqrtFockLat O.toSubring))

def GaussProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (GaussLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (DualLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (DualLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (DualLat R))

def GaussProjText : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B a p e : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → A ≤ 8 * a → B ≤ 8 * a →
    3 * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) + 4 * (k : ℝ) * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) ≤ (e : ℝ) →
    ∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ j ≤ min A B,
      (f ∈ latOf g (GaussLat R) → ((p : K) ^ e) • levelProj K k A B j f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (DualLat R) → ((p : K) ^ e) • levelProj K k A B j f ∈ latOf g (DualLat R))

def GaussLemmaH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K) (j : ℕ)
    (G : PolXY K k), 1 ≤ k →
      hXY K k ^ j * G ∈ latOf g (GaussLat O.toSubring) → G ∈ latOf g (GaussLat O.toSubring)

def HPrime : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ), 2 ≤ k → Prime (hXY F k)

def LevelLattice : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b j : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K), 1 ≤ k →
    latOf g (GaussLat O.toSubring) ∩ {f | ∃ w ∈ HarAB K k a b, f = hXY K k ^ j * w} =
      (fun w => hXY K k ^ j * w) '' (latOf g (GaussLat O.toSubring) ∩ (HarAB K k a b : Set (PolXY K k)))

def HarQuot : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p →
    (∀ w G : PolXY K k, w ∈ HarAB K k A B → w = hXY K k * G → w = 0) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (GaussLat O.toSubring) →
      ∃ w ∈ HarAB K k A B, ∃ G ∈ PolAB K k (A - 1) (B - 1),
        w ∈ latOf g (GaussLat O.toSubring) ∧ G ∈ latOf g (GaussLat O.toSubring) ∧
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • f = w + hXY K k * G)

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.WeylDim
section
noncomputable section

open scoped BigOperators

namespace Formalism.CountingSumsFrames

def weylDim (n : ℕ) (lam : Fin n → ℤ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))
    else 1

end Formalism.CountingSumsFrames
end
end

