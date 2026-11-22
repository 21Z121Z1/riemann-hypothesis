import Mathlib

-- bundled from Formalism.MahlerMeasure.LevelSum
section
namespace Formalism.GM

open MvPolynomial Finset

def qch (a j : ℕ) : ℚ := (a.choose j : ℚ)

def LevelSum : Prop :=
  ∀ (A z l : ℕ), z + l ≤ A →
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * qch l j * qch (A - z - l) j / qch A j = qch (z + l) l / qch A l

noncomputable def tieE {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (∑ c, X (w c) * X (e c))

noncomputable def tieF {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ c, (pderiv (w c)).toLinearMap ∘ₗ (pderiv (e c)).toLinearMap

noncomputable def tiePhi {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (o n z : ℕ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (o + 1),
    (((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((o + n + r + z - 1).choose j : k))) •
      (((tieE w e) ^ j).comp ((tieF w e) ^ j))

def BiHom {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (a b : ℕ) (u : MvPolynomial σ k) : Prop :=
  ∀ m ∈ u.support, (∑ c, m (w c)) = a ∧ (∑ c, m (e c)) = b

def LevelAct : Prop :=
  ∀ (k σ : Type) [Field k] [CharZero k] (r : ℕ) (w e : Fin r → σ), Function.Injective w →
    Function.Injective e → (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z l : ℕ) (u : MvPolynomial σ k), l ≤ o → l ≤ n → tieF w e u = 0 → BiHom w e (o - l) (n - l) u →
      tiePhi w e o n z ((tieE w e ^ l) u) =
        (((z + l).choose l : k) / ((o + n + r + z - 1).choose l : k)) • ((tieE w e ^ l) u)

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.Statement
section
namespace Formalism.GM

open Finset Polynomial

noncomputable def gch (x : ℚ) (k : ℕ) : ℚ := (descPochhammer ℚ k).eval x / (k.factorial : ℚ)

noncomputable def gchPoly (c : ℚ) (k : ℕ) : ℚ[X] :=
  Polynomial.C ((k.factorial : ℚ)⁻¹) * (descPochhammer ℚ k).comp (X + Polynomial.C c)

def GchBasics : Prop :=
  (∀ n k : ℕ, gch (n : ℚ) k = (n.choose k : ℚ)) ∧ (∀ (c x : ℚ) (k : ℕ), (gchPoly c k).eval x = gch (x + c) k)

def BinomRatio : Prop :=
  ∀ (x : ℚ) (l J : ℕ), l ≤ J → gch x J * gch (J : ℚ) l = gch x l * gch (x - l) (J - l)

def DetDegTop : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (a b : Fin n → ℕ),
    (∀ i j, (A i j).natDegree ≤ a i + b j) →
      (A.det).natDegree ≤ ∑ i, a i + ∑ j, b j ∧
      (A.det).coeff (∑ i, a i + ∑ j, b j) = (Matrix.of fun i j => (A i j).coeff (a i + b j)).det

def DetBlockLead : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (D : ℕ) (e : Fin n → ℕ),
    (∀ i, e i ≤ D) → (∀ i j, (A i j).natDegree + max (e i) (e j) ≤ D) →
      (A.det).natDegree ≤ ∑ i, (D - e i) ∧
      (A.det).coeff (∑ i, (D - e i)) =
        (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ∧
      ((Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ≠ 0 →
        (A.det).natDegree = ∑ i, (D - e i) ∧
        (A.det).leadingCoeff = (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det)

noncomputable def tiePoly {m : ℕ} (J : ℕ) (c : ℚ) (B : ℕ → Matrix (Fin m) (Fin m) ℚ) :
    Matrix (Fin m) (Fin m) ℚ[X] :=
  ∑ l ∈ range (J + 1),
    ((-1 : ℚ[X]) ^ l * gchPoly (c - l) (J - l) * Polynomial.C ((gch (J : ℚ) l)⁻¹)) • (B l).map Polynomial.C

def TiePoly : Prop :=
  ∀ (m J : ℕ) (c : ℚ) (B : ℕ → Matrix (Fin m) (Fin m) ℚ), B 0 = 1 →
    (∀ i j, ((tiePoly J c B) i j).natDegree ≤ J) ∧
    (∀ i j, ((tiePoly J c B) i j).coeff J = if i = j then ((J.factorial : ℚ))⁻¹ else 0)

def LegendreDigits : Prop :=
  ∀ (p m : ℕ), p.Prime →
    (m : ℝ) / ((p : ℝ) - 1) - (padicValNat p m.factorial : ℝ) ≤ (Nat.log p m : ℝ) + 1

noncomputable def vmin (p : ℕ) {K : Type} [NormedField K] (h : ℕ) (x : K) : ℝ :=
  -Real.logb p (max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))))

def WindowCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (ζ : K) (t₀ : ℤ) (Y₀ h : ℕ),
    ∑ t ∈ Ico t₀ (t₀ + Y₀), vmin p h ((t : K) - ζ) ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1)

open Classical in

def DiscsDisjoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (t₀ : ℤ) (Y₀ h : ℕ), Y₀ ≤ p ^ h →
    ∑ t ∈ Ico t₀ (t₀ + Y₀), (roots.filter (fun ζ => ‖(t : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card ≤ roots.card

open Classical in

def WindowMean : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (lam La₀ E : ℝ) (n₀ del₀ : ℕ) (t₀ : ℤ) (Y₀ h : ℕ) (β : ℤ → ℕ),
    0 < Y₀ → Y₀ ≤ p ^ h → 0 < E →
    roots.card ≤ del₀ * n₀ →
    lam + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * La₀ →
    (∀ t ∈ Ico t₀ (t₀ + Y₀),
      (β t : ℝ) * E ≤ (lam + (roots.map (fun ζ => vmin p h ((t : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) →
    (∑ t ∈ Ico t₀ (t₀ + Y₀), (β t : ℝ)) / (Y₀ : ℝ) ≤
      (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)

def CycleProd : Prop :=
  ∀ (J : ℕ) [NeZero J] (p : ℝ) (Q : Fin J → ℝ) (R : Fin J → ℤ), p ≠ 0 →
    ∏ j, Q (j + 1) * p ^ (R (j + 1) - R j) = ∏ j, Q j

def CoarseSlack : Prop :=
  ∀ (p a Y k Ns Qn be : ℝ) (D₁ L₁ Rj Rn : ℤ),
    1 < p → 0 < a → 0 < Y → 0 < k → 0 < Ns → 0 < Qn →
    be ≤ 4 * a * p ^ (-D₁ - L₁ - Rj) →
    a / (4 * Y * k ^ 2 * Ns * p ^ D₁ * Qn) < p ^ (Rn + 1) →
    64 * p * k ^ 2 * Ns * Y ^ 2 ≤ p ^ L₁ →
    be / (Qn * p ^ (Rn - Rj)) ≤ 16 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ∧
      16 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ≤ 1 / (4 * Y)

open Classical in

def FrameCount : Prop :=
  ∀ (r Q b : ℕ) (c : ℤ), 2 ≤ r → 0 < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 8 * r * b / Q) ≤
      ((univ.filter (fun e : Fin r → Fin Q =>
        (∀ i, (e i : ℕ) + 4 * b < Q) ∧ (∑ i, ((e i : ℕ) : ℤ)) ≡ c [ZMOD Q])).card : ℝ)

def TrueRing : Prop :=
  ∀ (R : Type) [CommRing R] (r Q : ℕ), 0 < Q →
    Function.Bijective (fun f : (Fin r → Fin Q) → MvPolynomial (Fin r) R =>
      ∑ e, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))) (1 : R) *
        MvPolynomial.expand Q (f e))

def SatSub : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] (n : ℕ)
    (L : Submodule R (Fin n → R)),
    ∃ M : Submodule R (Fin n → R), M ≤ L ∧
      Module.finrank R M =
        Module.finrank (IsLocalRing.ResidueField R)
          (Submodule.span (IsLocalRing.ResidueField R)
            ((fun v : Fin n → R => fun i => IsLocalRing.residue R (v i)) '' (L : Set (Fin n → R)))) ∧
      ∀ (a : R) (x : Fin n → R), a ≠ 0 → a • x ∈ M → x ∈ M

def CoarseDiv : Prop :=
  ∀ (p m n i : ℕ), p.Prime → 1 ≤ i → i ≤ p ^ m * n →
    m ≤ padicValNat p ((p ^ m * n).choose i) + padicValNat p i

def MeanBad : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : Finset ℤ) (ntop : ℤ) (mult n₀ : ι → ℝ) (bad y : ι → ℤ → ℝ) (CK : ℝ),
    N.Nonempty → (∀ w, 0 ≤ mult w) → (∀ w n, n ∈ N → 0 ≤ bad w n) →
    (∀ w n, n ∈ N → 0 ≤ y w n ∧ y w n ≤ y w ntop) →
    (∀ w, (∑ n ∈ N, bad w n) / N.card ≤ CK * n₀ w) →
    (∑ n ∈ N, ∑ w, mult w * bad w n * y w n) / N.card ≤ CK * ∑ w, mult w * n₀ w * y w ntop

end Formalism.GM
end

