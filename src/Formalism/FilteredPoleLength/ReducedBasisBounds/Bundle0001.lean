import Mathlib

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.AlternatingBinomial
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Real

def TieBoundN : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V),
      (∀ y ∈ Γ, B x x / 2 ≤ B (x + y) (x + y) / 2) →
      ∀ g ∈ Γ, ∀ N : ℕ, 2 ≤ N →
        B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 =
            (N : ℝ) * B x g + (N : ℝ) ^ 2 * (B g g / 2) ∧
        (N : ℝ) * ((N : ℝ) - 1) * (B g g / 2) ≤
            B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 ∧
        (0 < B g g → B x x / 2 < B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2)

def FPrimeWeights : Prop :=
  ∀ (T D r nW n' c ap am : ℤ), 0 < T → 0 ≤ D →
    let T' := T + D + 2
    let cW := (c + 2) / T'
    let rem := (c + 2) % T'
    let apW := (ap - (D + 2) * nW - 2 * r) / T'
    let s₁ := (ap - (D + 2) * nW - 2 * r) % T'
    let amW := am / T'
    let s₂ := am % T'
    (c - T * cW = (D + 2) * cW + rem - 2 ∧ (1 ≤ cW → 0 ≤ c - T * cW)) ∧
    (ap - T * apW = (D + 2) * apW + (D + 2) * nW + 2 * r + s₁ ∧
      (0 ≤ apW → 0 ≤ nW → 1 ≤ r → 1 ≤ ap - T * apW)) ∧
    (am - T * amW = (D + 2) * amW + s₂ ∧ (0 ≤ amW → 0 ≤ am - T * amW) ∧
      (1 ≤ amW → 1 ≤ am - T * amW)) ∧
    (n' ≤ nW → r ≤ nW → 0 ≤ nW → (D + 3) * nW ≤ (D + 4) * nW - n' ∧ r ≤ (D + 4) * nW - n')

def RemClass : Prop :=
  ∀ (T D r nW nV f c ap am : ℤ), 0 < T → 0 ≤ D → 1 ≤ r → 2 ≤ nW → 1 ≤ f →
    let T' := T + D + 2
    let n' := nV - T * nW
    let cW := (c + 2) / T'
    let rem := (c + 2) % T'
    let apW := (ap - (D + 2) * nW - 2 * r) / T'
    let s₁ := (ap - (D + 2) * nW - 2 * r) % T'
    let amW := am / T'
    let s₂ := am % T'
    let nrem := nV - T' * nW - (2 * r - 2)
    (c - T' * cW + 2 = rem ∧ 0 ≤ rem ∧ rem < T') ∧
    ap - T' * apW = (D + 2) * nW + 2 * r + s₁ ∧
    am - T' * amW = s₂ ∧
    nrem = n' - (D + 2) * nW - 2 * r + 2 ∧
    (n' ≤ nW → nrem < 0) ∧
    (ap - T' * apW) + (am - T' * amW) + nrem - r + 1 = s₁ + s₂ + n' + 3 - r ∧
    s₁ + s₂ + n' + 3 - r < n' + 2 + 2 * T' ∧
    (8 * f * r + 4 ≤ n' → 0 < s₁ + s₂ + n' + 3 - r) ∧
    (-2 + (D + 2) * cW + rem = c - T * cW ∧
      (D + 2) * apW + (ap - T' * apW) = ap - T * apW ∧
      (D + 2) * amW + (am - T' * amW) = am - T * amW ∧
      (2 * r - 2) + (D + 2) * nW + nrem = n')

def JetGapColumns : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ v, 0 ≤ B v v) →
    ∀ (X : AddSubgroup V) (J ι : Type) [Fintype J] [Fintype ι] (b : J → V)
      (M₀ Cφ DF q μ : ℝ),
      (∀ j, ∀ w ∈ X, |B (b j) w| ≤ M₀ * (B w w / 2)) →
      (∀ j, B (b j) (b j) / 2 ≤ Cφ) →
      (∀ w ∈ X, w ≠ 0 → μ ≤ B w w / 2) → 0 < μ → 0 ≤ M₀ → DF * M₀ < q → 0 ≤ Cφ →
      ∀ e : J → ι → ℕ, (∑ j, ∑ k, (e j k : ℝ)) ≤ DF →
        (∀ z : ι → V, (∀ k, z k ∈ X) →
          |∑ k, B (∑ j, (e j k : ℝ) • b j) (z k)| ≤ DF * M₀ * ∑ k, B (z k) (z k) / 2) ∧
        (∀ z : ι → V, (∀ k, z k ∈ X) → z ≠ 0 →
          (q - DF * M₀) * μ ≤
            ∑ k, B (∑ j, (e j k : ℝ) • b j) (z k) + q * ∑ k, B (z k) (z k) / 2) ∧
        0 < (q - DF * M₀) * μ ∧
        ∑ k, B (∑ j, (e j k : ℝ) • b j) (∑ j, (e j k : ℝ) • b j) / 2 ≤ DF ^ 2 * Cφ

def AlternatingBinomial : Prop :=
  ∀ (σ R : Type) [Fintype σ] [DecidableEq σ] [CommRing R] (a : σ → ℕ) (T : σ → R),
    ∑ e ∈ Fintype.piFinset (fun j => Finset.range (a j + 1)),
        (-1 : R) ^ (∑ j, (a j - e j)) * ((∏ j, (a j).choose (e j) : ℕ) : R) *
          ∏ j, (1 + T j) ^ (e j) =
      ∏ j, T j ^ (a j)

def DescentNoLinearTerm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) (w₀ w₀b : V →ₗ[ℝ] V),
    (∀ x y, B x y = B y x) → (∀ x y, B x (w₀ y) = B (w₀b x) y) → w₀ + w₀b = LinearMap.id →
    ∀ z, B z (w₀ z) = B z z / 2

def DescentCocycle : Prop :=
  ∀ (X Y M : Type) [AddCommGroup X] [AddCommGroup Y] [CommGroup M] (τ : X → Y → M)
    (lam : X →+ Y) (w₀ w₀b : X →+ X),
    (∀ x x' y, τ (x + x') y = τ x y * τ x' y) → (∀ x y y', τ x (y + y') = τ x y * τ x y') →
    (∀ z z', τ z' (lam (w₀ z)) = τ z (lam (w₀b z'))) → (∀ z, w₀ z + w₀b z = z) →
    ∀ z z', τ (z + z') (lam (w₀ (z + z'))) =
      τ z (lam (w₀ z)) * τ z' (lam (w₀ z')) * τ z (lam z')

def CBConstant : Prop :=
  ∀ (RR PP dp DF n₁ nW q g' : ℝ), 0 ≤ RR → 0 ≤ dp → 1 ≤ DF → 0 ≤ n₁ → n₁ ≤ nW → 0 < q →
    q ≤ g' → nW * dp ^ 4 / 4 + 2 * dp ^ 3 ≤ PP →
    (n₁ * dp * (RR * dp ^ 3) / (4 * g') + 2 * (RR * dp ^ 3) * DF ^ 2 / g' ≤
        (nW * dp ^ 4 / 4 + 2 * dp ^ 3 * DF ^ 2) * RR / q ∧
      (nW * dp ^ 4 / 4 + 2 * dp ^ 3 * DF ^ 2) * RR / q ≤ RR * PP * DF ^ 2 / q) ∧
    (∀ Xq : ℝ, Xq ≤ q → Xq ≤ g') ∧
    (∀ D g : ℝ, 0 ≤ D → (D + 4) * DF ≤ q - 2 → q ≤ g → DF < g - 1)

def NuStarSum : Prop :=
  ∀ (DF D q g₁ g₂ RR PP : ℝ), 1 ≤ DF → 0 ≤ D → 0 ≤ RR → 0 ≤ PP → 8 ≤ RR ^ 4 * PP ^ 3 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → (D + 4) * DF ≤ q - 2 → q ≤ g₁ → q ≤ g₂ →
    DF / (g₁ - 1) < 1 ∧ DF / (g₂ - 1) < 1 ∧
      DF * (Real.log g₁ / (g₁ - 1) + Real.log g₂ / (g₂ - 1)) < 1

def columnOperation {R : Type} [CommRing R] {i N : ℕ} (x : Fin i → Fin N → R) (a b : Fin i) :
    MvPolynomial (Fin i × Fin N) R →ₗ[R] MvPolynomial (Fin i × Fin N) R :=
  ∑ k, x a k • (MvPolynomial.pderiv (b, k) :
    Derivation R (MvPolynomial (Fin i × Fin N) R) (MvPolynomial (Fin i × Fin N) R)).toLinearMap

def columnOperationComposite {R : Type} [CommRing R] {i N : ℕ} (x : Fin i → Fin N → R) (c : ℕ)
    (s : Fin c → Equiv.Perm (Fin i)) :
    MvPolynomial (Fin i × Fin N) R →ₗ[R] MvPolynomial (Fin i × Fin N) R :=
  (Finset.univ : Finset (Fin c × Fin i)).toList.foldr
    (fun p acc => columnOperation x p.2 (s p.1 p.2) ∘ₗ acc) LinearMap.id

def DetPowerIdentity : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (i N c : ℕ) (x η : Fin i → Fin N → R),
    (∑ s : Fin c → Equiv.Perm (Fin i),
        (∏ t, ((Equiv.Perm.sign (s t) : ℤ) : R)) • columnOperationComposite x c s)
      (∏ b : Fin i, (MvPolynomial.C ((c.factorial : R)⁻¹) *
        (∑ k, MvPolynomial.C (η b k) * MvPolynomial.X (b, k)) ^ c)) =
    MvPolynomial.C ((Matrix.of fun a b : Fin i => ∑ k, η b k * x a k).det ^ c)

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

def CovolAbsorb : Prop :=
  ∀ (A κ₀ φ : ℝ), 0 < A → 0 < κ₀ → 0 < φ →
    A * Real.log (κ₀ * φ) ≤ φ + A * Real.log (A * κ₀) ∧
    (∀ (i K PP lEt : ℝ), 0 ≤ i → K + A * Real.log (A * κ₀) ≤ PP →
      lEt ≤ i * (K + A * Real.log (κ₀ * φ) - 2 * π * φ) →
      lEt ≤ -i * ((2 * π - 1) * φ - PP)) ∧
    (∀ (RR dp lmax cov : ℝ) (d : ℕ), 0 ≤ lmax → cov ≤ lmax ^ d →
      lmax ^ 2 ≤ 4 * RR * dp ^ 2 * φ → cov ≤ (4 * RR * dp ^ 2 * φ) ^ ((d : ℝ) / 2))

def MinimumChainBounds : Prop :=
  ∀ (dp lmax2 φ RR PP r₁ r E0 minQ δ : ℝ), 0 ≤ dp → 0 ≤ φ → 0 ≤ RR → 1 ≤ r₁ → 0 ≤ r →
    minQ ≤ dp * lmax2 / (4 * r₁ ^ 2) → lmax2 ≤ 2 * RR * dp ^ 2 * φ → E0 ≤ r * minQ →
    r * dp ^ 3 ≤ PP →
    minQ ≤ RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧ E0 ≤ r * RR * dp ^ 3 * φ / (2 * r₁ ^ 2) ∧
      E0 ≤ RR * PP * φ ∧
      (φ ≤ r₁ ^ 4 * E0 → φ ≤ 2 * r₁ ^ 4 * E0 / 2) ∧
      (2 * r₁ ^ 4 * r) * δ - 2 * r₁ ^ 4 * E0 = 2 * r₁ ^ 4 * (r * δ - E0)

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.FourTermSumBoundOfParameters
section
namespace Formalism.LatticeBaseChangeAlt

def FourTermSumBound : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ : ℝ), 0 ≤ d → 0 < T → 0 < ga → 0 ≤ PP → 0 ≤ D →
    0 ≤ RR ^ 2 * c + 1 / T → κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfParameters : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 0 < PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T → 2 ≤ PP ^ 2 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfSqLe : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 1 ≤ PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 → PP ^ 2 ≤ f * m * b * δ₂ / 4 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.GFiniteOrderUnipotent
section
open scoped BigOperators
open Polynomial Finset

namespace Formalism.LatticeBaseChangeAlt

def GSeriesBound : Prop :=
  ∀ f N n : ℕ, 8 * f * N + 4 ≤ n →
    Summable (fun m : ℕ => ((m + 2 : ℕ) : ℝ) ^ (((4 * f * N : ℕ) : ℝ) - (n : ℝ) / 2)) ∧
    ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (((4 * f * N : ℕ) : ℝ) - (n : ℝ) / 2) < 1

def GSublatticeCount : Prop :=
  ∀ ρ m : ℕ, 1 ≤ m →
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ

def GStdLat (ρ : ℕ) : AddSubgroup (Fin ρ → ℚ) :=
  (AddMonoidHom.compLeft (Int.castAddHom ℚ) (Fin ρ)).range

def GLatticeCount : Prop :=
  ∀ ρ m : ℕ, 1 ≤ m →
    {L' : AddSubgroup (Fin ρ → ℚ) |
      ((GStdLat ρ ⊓ L').addSubgroupOf (GStdLat ρ)).index = m ∧
      ((GStdLat ρ ⊓ L').addSubgroupOf L').index = m}.Finite ∧
    {L' : AddSubgroup (Fin ρ → ℚ) |
      ((GStdLat ρ ⊓ L').addSubgroupOf (GStdLat ρ)).index = m ∧
      ((GStdLat ρ ⊓ L').addSubgroupOf L').index = m}.ncard ≤ m ^ (2 * ρ)

def GNormBound : Prop :=
  ∀ (f N n : ℕ), 8 * f * N + 4 ≤ n →
  ∀ (ι : Type) (idx : ι → ℕ) (a : ι → ℝ),
    (∀ i, 2 ≤ idx i) →
    (∀ i, 0 ≤ a i ∧ a i ≤ ((idx i : ℕ) : ℝ) ^ (-((n : ℝ) / 2))) →
    (∀ m : ℕ, {i | idx i = m}.Finite ∧ {i | idx i = m}.ncard ≤ m ^ (4 * f * N)) →
    Summable a ∧ ∑' i, a i < 1

def GNeumannPositive : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : E →L[ℂ] E), ‖T‖ < 1 →
    (∀ F : E, F ≠ 0 → 0 < RCLike.re (inner ℂ (F + T F) F)) ∧
    (∀ (c : ℝ), 0 < c → ∀ F : E, (c : ℂ) * inner ℂ (F + T F) F = 0 → F = 0)

def GGridNonvanishing : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (p : MvPolynomial σ K) (d : ℕ),
    p ≠ 0 → p.totalDegree ≤ d →
    ∃ x : σ → ℕ, (∀ i, x i ≤ d) ∧ MvPolynomial.eval (fun i => (x i : K)) p ≠ 0

noncomputable def GAdjVec {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (h : V →ₗ[R] V → R) (e e' g : Fin N → V) (b : Fin N) : V :=
  (Matrix.of fun a' a => h (e' a') (e a)).det • g b -
    ∑ a, ∑ a', ((Matrix.of fun a' a => h (e' a') (e a)).adjugate a a' * h (g b) (e a)) • e' a'

def GAdjugateOrth : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (h : V →ₗ[R] V → R) (e e' g : Fin N → V),
    (∀ b c, h (GAdjVec h e e' g b) (e c) = 0) ∧
    (∀ (O : Subring R) (S : AddSubgroup V),
      (∀ (c : R) (v : V), c ∈ O → v ∈ S → c • v ∈ S) →
      (∀ v w, v ∈ S → w ∈ S → h v w ∈ O) →
      (∀ a, e a ∈ S) → (∀ a, e' a ∈ S) → (∀ a, g a ∈ S) → ∀ b, GAdjVec h e e' g b ∈ S)

def GAdjugateNormBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (N : ℕ)
    (h : V →ₗ[ℂ] V → ℂ) (e e' g : Fin N → V) (ρ' : ℝ),
    (∀ x y, ‖h x y‖ ≤ ‖x‖ * ‖y‖) →
    (∀ a, ‖e a‖ ≤ ρ') → (∀ a, ‖e' a‖ ≤ ρ') → (∀ a, ‖g a‖ ≤ ρ') →
    ∀ b, ‖GAdjVec h e e' g b‖ ≤ (N + 1).factorial * ρ' ^ (2 * N + 1)

def GIsotropicNorm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (a : NumberField.RingOfIntegers K)
    (H : (K →+* ℂ) → ℝ),
    (∀ τ, 0 ≤ H τ) → (∀ τ, ‖τ (a : K)‖ ≤ H τ) → ∑ τ, H τ < 1 → a = 0

def GSchwarzArith : Prop :=
  ∀ (c s ε q F : ℝ), 0 < c → 0 < s → 0 < ε → 0 < q → 0 < F →
    (∀ t : ℝ, 0 < t → t ≤ c / (s * ε) → 1 ≤ Real.exp (-2 * Real.pi * t / q) * (2 : ℝ) ^ F) →
    2 * Real.pi * c / (s * q * F * Real.log 2) ≤ ε

def GFrequencySign : Prop :=
  ∀ (A ν M : ℝ) (k : ℕ), 0 < A →
    (∀ t : ℝ, 1 ≤ t → A * Real.exp (-2 * Real.pi * ν * t) ≤ M * t ^ k) → 0 ≤ ν

def GCauchyArith : Prop :=
  ∀ (ι : Type) [Fintype ι] (α : ι → ℕ),
    ((∏ i, ((α i).factorial : ℝ)) * Real.exp ((∑ i, (α i : ℝ)) / 2) *
      ∏ i, (Real.pi / (α i : ℝ)) ^ ((α i : ℝ) / 2)) ≤
    (Real.pi * Real.exp 1 * (∑ i, (α i : ℝ))) ^ ((∑ i, (α i : ℝ)) / 2)

def GTorsionFree : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → (∀ l : ℕ, ¬ p ∣ l → ‖(l : K)‖ = 1) →
    ∀ (ζ : K) (n : ℕ), 0 < n → ζ ^ n = 1 →
      ‖ζ - 1‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ζ = 1

def GEigenValuation : Prop :=
  ∀ (r g e : ℕ) (k : ℤ), 1 ≤ r → r + 1 < g → 1 ≤ e → e ≤ r → 0 < k →
    (1 : ℝ) / ((g : ℝ) - 1) < (k : ℝ) / e

def GFiniteOrderUnipotent : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (k : ℕ), 0 < k → A ^ k = 1 →
    A.charpoly = (X - 1) ^ Fintype.card n → A = 1

def GMonomialDet : Prop :=
  ∀ (H : Type) [Group H] [Fintype H] [DecidableEq H] (Y : Type) [MulAction H Y]
    (K : Type) [Field K] (y₀ : Y) (u : Y → K),
    MulAction.IsPretransitive H Y →
    (∀ (h : H) (y : Y), h • y = y → h = 1) →
    u y₀ = 1 → (∀ y, y ≠ y₀ → u y = 0) →
    ∀ y : Y, (Matrix.of fun h h' : H => u ((h * h') • y)).det ≠ 0

def GMarkovIneq : Prop :=
  ∀ (p : ℝ[X]) (a b : ℝ), a < b → ∀ Mx : ℝ, (∀ x ∈ Set.Icc a b, |p.eval x| ≤ Mx) →
    ∀ x ∈ Set.Icc a b, |p.derivative.eval x| ≤ 2 * (p.natDegree : ℝ) ^ 2 / (b - a) * Mx

def GDimDescent : Prop :=
  GMarkovIneq →
  ∀ (p : ℝ[X]) (D n₀ s γ : ℕ), p.natDegree ≤ D → 1 ≤ n₀ → 8 * D ^ 2 * (n₀ + s) ≤ γ →
    (∀ i : ℕ, i ≤ (γ - 1) / n₀ →
      0 ≤ p.eval ((i * n₀ : ℕ) : ℝ) ∧ p.eval ((i * n₀ : ℕ) : ℝ) ≤ p.eval 0) →
    (∀ x ∈ Set.Icc (0 : ℝ) (((γ - 1) / n₀ * n₀ : ℕ) : ℝ),
        |p.derivative.eval x| ≤ 4 * (D : ℝ) ^ 2 * p.eval 0 / γ) ∧
    (1 - 8 * (D : ℝ) ^ 2 * s / γ) * p.eval 0 ≤ p.eval (s : ℝ)

def GPropRJoint : Prop :=
  ∀ (dm d0 dp dpp h B I μρ dimρ ε : ℝ), 0 ≤ ε → ε < 1 → 0 < h → 0 ≤ dimρ →
    (1 - ε) * d0 ≤ dm → (1 - ε) * dp ≤ d0 → (1 - ε) * dpp ≤ dp →
    dm ≤ h * B → h * B ≤ dp → h * I ≤ dpp → μρ ≤ dimρ * I →
    ((1 - ε) * d0 ≤ h * B ∧ h * B ≤ d0 / (1 - ε)) ∧
    μρ ≤ dimρ * d0 / ((1 - ε) ^ 2 * h)

def GSlopeDG : Prop :=
  ∀ (dA dB lam μmin ε' : ℝ) (rA rB : ℕ), 0 < rA → rA ≤ rB → 0 ≤ ε' → 0 ≤ lam →
    (1 - ε') * rB ≤ rA →
    dA - rA * lam + ((rB : ℝ) - rA) * μmin ≤ dB →
    dA / rA - lam - ε' * (|dA / rA| + |μmin|) ≤ dB / rB

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

def GOrthogonalEigen : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type) (U : G → E →L[ℂ] E)
    (χ χ' : G → ℂ) (v w : E),
    (∀ g x y, inner ℂ (U g x) (U g y) = inner ℂ x y) →
    (∀ g, U g v = χ g • v) → (∀ g, U g w = χ' g • w) → (∃ g, χ g ≠ χ' g) →
    inner ℂ v w = 0

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.ParameterInequalities
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix
open scoped RealInnerProductSpace BigOperators

def CompletingSquare : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (q : ℝ), 0 < q → ∀ χ : V,
      (∀ u : V, -(B χ χ / 2) / q ≤ B χ u + q * (B u u / 2)) ∧
      B χ ((-(1 / q)) • χ) + q * (B ((-(1 / q)) • χ) ((-(1 / q)) • χ) / 2) = -(B χ χ / 2) / q

def CosetMinUnique : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (X : AddSubgroup V) (q : ℝ) (χ : V),
      (∀ z : V, B (χ + q • z) (χ + q • z) / 2 - B χ χ / 2 = q * (B χ z + q * (B z z / 2))) ∧
      (0 < q → (∀ z ∈ X, z ≠ 0 → |B χ z| < q * (B z z / 2)) →
        ∀ z ∈ X, z ≠ 0 → B χ χ / 2 < B (χ + q • z) (χ + q • z) / 2)

def ReducedBasisNear : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (S : AddSubgroup V) (b w : V), w ∈ S →
      (∀ s ∈ S, B (b - w) (b - w) ≤ B (b - s) (b - s)) →
      (∀ z ∈ S, |B (b - w) z| ≤ B z z / 2) ∧ B (b - w) (b - w) ≤ B b b

def ReducedBasisBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X S : AddSubgroup V) (b w : V) (d' : ℝ), S ≤ X → b ∈ X → w ∈ S → 1 ≤ d' →
      (∀ s ∈ S, B (b - w) (b - w) ≤ B (b - s) (b - s)) →
      (∀ z ∈ X, z ∉ S → B b b / 2 / d' ≤ B z z / 2) →
      ∀ z ∈ X, |B (b - w) z| ≤ 2 * Real.sqrt d' * (B z z / 2)

def CharacterBounds : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X : AddSubgroup V) (ι : Type) [Fintype ι] (e : ι → ℕ) (b : ι → V) (DF M0 Cφ : ℝ),
      (∑ i, (e i : ℝ)) ≤ DF → 0 ≤ M0 → 0 ≤ Cφ →
      (∀ i, ∀ z ∈ X, |B (b i) z| ≤ M0 * (B z z / 2)) →
      (∀ i, B (b i) (b i) / 2 ≤ Cφ) →
      (∀ z ∈ X, |B (∑ i, (e i : ℝ) • b i) z| ≤ DF * M0 * (B z z / 2)) ∧
      B (∑ i, (e i : ℝ) • b i) (∑ i, (e i : ℝ) • b i) / 2 ≤ DF ^ 2 * Cφ

def JetJoint : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (X : AddSubgroup V) (ι : Type) [Fintype ι] (e : ι → ℕ) (b : ι → V) (DF M0 q : ℝ),
      (∑ i, (e i : ℝ)) ≤ DF → 0 ≤ M0 → 0 < q → DF * M0 < q →
      (∀ z ∈ X, z ≠ 0 → 0 < B z z) →
      (∀ i, ∀ z ∈ X, |B (b i) z| ≤ M0 * (B z z / 2)) →
      ∀ z ∈ X, z ≠ 0 →
        B (∑ i, (e i : ℝ) • b i) (∑ i, (e i : ℝ) • b i) / 2 <
          B ((∑ i, (e i : ℝ) • b i) + q • z) ((∑ i, (e i : ℝ) • b i) + q • z) / 2

def TieBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V) (r : ℝ),
      (∀ g ∈ Γ, B x x / 2 ≤ B (x + g) (x + g) / 2) →
      ∀ g ∈ Γ,
        r ^ 2 * (r ^ 2 - 1) * (B g g / 2) ≤
            B (x + r ^ 2 • g) (x + r ^ 2 • g) / 2 - B x x / 2 ∧
        (1 < r ^ 2 → 0 < B g g → B x x / 2 < B (x + r ^ 2 • g) (x + r ^ 2 • g) / 2)

def EtFactorCount : Prop :=
  ∀ (α : Type) (G : Finset α) (v : α → ℝ) (φ : ℝ) (r1 r : ℕ) (i : ℝ), 0 < r1 → 0 ≤ i →
    (G.card : ℝ) = 2 * (r1 : ℝ) ^ 4 * i →
    (∀ g ∈ G, φ / (r1 : ℝ) ^ 4 ≤ v g) →
    2 * i * φ ≤ ∑ g ∈ G, v g ∧
    (0 < i → ((r : ℝ) * (G.card : ℝ)) / i = 2 * (r1 : ℝ) ^ 4 * (r : ℝ))

def EtCombination : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    (κ : Type) (C : Finset κ) (ℓ : κ → σ → R),
    (∀ c ∈ C, ∃ s, ℓ c s ≠ 0) →
    ∃ x : σ → ℕ, (∀ s, x s ≤ C.card) ∧ ∀ c ∈ C, ∑ s, (x s : R) * ℓ c s ≠ 0

def TraceDomination : Prop :=
  ∀ (n : ℕ) (A P : Matrix (Fin n) (Fin n) ℝ), A.PosSemidef → P.PosDef →
    ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ (P⁻¹ * A).trace * (x ⬝ᵥ (P *ᵥ x))

def OrderChain : Prop :=
  ∀ (lmax2 pairing μ l1sq d' RR : ℝ), 0 ≤ pairing → 0 < RR → 0 < l1sq →
    lmax2 ≤ 2 * pairing * μ → μ * l1sq ≤ d' ^ 2 → 1 / RR ≤ l1sq →
    lmax2 ≤ 2 * RR * d' ^ 2 * pairing

def GaussUnfold : Prop :=
  ∀ (d : ℕ) (q : ℝ), 0 < q → ∀ c : EuclideanSpace ℝ (Fin d),
    ∫ u : EuclideanSpace ℝ (Fin d), Real.exp (-(4 * Real.pi * inner ℝ c u) - 2 * q * Real.pi * ‖u‖ ^ 2) =
      (2 * q) ^ (-(d : ℝ) / 2) * Real.exp (2 * Real.pi * ‖c‖ ^ 2 / q)

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

def RadiusChoice : Prop :=
  ∀ (c q A : ℝ), 0 < c → 0 < q → 0 ≤ A →
    q * Real.pi * (c / (2 * Real.pi * A + Real.sqrt (q * c))) ^ 2 / 2 ≤ Real.pi * c / 2 ∧
    2 * Real.pi * (c / (2 * Real.pi * A + Real.sqrt (q * c))) * A ≤ c

def FloorDivisionGaps : Prop :=
  ∀ (T D r nW c a am : ℤ), 0 < T → 0 ≤ D → 0 ≤ r →
    ((T + D + 2 + 2) * ((c + 2) / (T + D + 2)) - c =
        2 * ((c + 2) / (T + D + 2)) + 2 - (c + 2) % (T + D + 2) ∧
      (T + D + 2 + 2 * r ≤ (c + 2) / (T + D + 2) →
        0 ≤ 2 * ((c + 2) / (T + D + 2)) + 2 - (c + 2) % (T + D + 2))) ∧
    ((T + D + 2 + 2) * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - a =
        2 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - (D + 2) * nW - 2 * r -
          (a - (D + 2) * nW - 2 * r) % (T + D + 2) ∧
      (19 * T ≤ 10 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) → (D + 2) * nW + 2 * r ≤ T →
        5 * (D + 2) ≤ 9 * T →
        1 ≤ 2 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2)) - (D + 2) * nW - 2 * r -
          (a - (D + 2) * nW - 2 * r) % (T + D + 2))) ∧
    ((T + D + 2 + 2) * (am / (T + D + 2)) - am = 2 * (am / (T + D + 2)) - am % (T + D + 2) ∧
      (19 * T ≤ 10 * (am / (T + D + 2)) → 5 * (D + 2) ≤ 9 * T →
        1 ≤ 2 * (am / (T + D + 2)) - am % (T + D + 2)))

def LastEntryL : Prop :=
  ∀ (T D r nW a : ℤ), 0 < T → 0 ≤ D → 0 ≤ r → 0 ≤ nW →
    2 * T ^ 2 ≤ a → (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T →
    19 * T ≤ 10 * ((a - (D + 2) * nW - 2 * r) / (T + D + 2))

def LastEntryLMinus : Prop :=
  ∀ (T D am : ℤ), 0 < T → 0 ≤ D → 2 * T ^ 2 ≤ am → 40 * (D + 2) ≤ T →
    19 * T ≤ 10 * (am / (T + D + 2))

def ParameterInequalities : Prop :=
  ∀ (q RR PP DF M0 T g0 Cd : ℝ), 1 ≤ RR → 1 ≤ PP → 1 ≤ DF → 0 ≤ M0 → 0 ≤ T → 0 ≤ g0 →
    (M0 < PP → RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → DF * M0 < q) ∧
    (0 < q → T * g0 * RR * PP * DF ^ 2 ≤ q → T * (RR * PP * DF ^ 2 / q) * g0 ≤ 1) ∧
    (0 < q → 2 * Cd ≤ RR * PP → 2 * Cd * DF ^ 2 / q ≤ RR * PP * DF ^ 2 / q)

end Formalism.LatticeBaseChangeAlt
end
end

