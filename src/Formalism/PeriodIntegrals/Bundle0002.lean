import Mathlib

-- bundled from Formalism.PeriodIntegrals.ClassNumImQ
section
open NumberField

namespace PI.ClassNumImQ

def kron2 (D : ℤ) : ℤ := if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

def kronSym (D : ℤ) (n : ℕ) : ℤ :=
  jacobiSym D (n / 2 ^ n.factorization 2) * kron2 D ^ n.factorization 2

def kron (D : ℤ) (a : ℕ) : ℂ := (kronSym D a : ℂ)

def chDir (d : ℕ) : ℕ → ℂ := kron (-(d : ℤ))

def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a

def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤

def ClassNumImQ : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ((classNumber K : ℕ) : ℂ) =
        ((Real.sqrt d : ℝ) : ℂ) * DirichletCharacter.LFunction χ 1 / (Real.pi : ℂ)

def ZetaFactor : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ∀ s : ℂ, 1 < s.re →
        dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s

def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)

def Invariants : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    InfinitePlace.nrRealPlaces K = 0 ∧ InfinitePlace.nrComplexPlaces K = 1 ∧
      Units.regulator K = 1 ∧ Units.torsionOrder K = 2 ∧ discr K = -(d : ℤ)

end PI.ClassNumImQ
end

-- bundled from Formalism.PeriodIntegrals.CubicExponentialFactor
section
noncomputable section

open Classical

namespace PI.CubicExponentialFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq l ex E : PowerSeries ℂ_[p])
    (T : MvPowerSeries (Fin 3) ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    T * eAt E (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 * eAt E (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 *
        eAt E (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 =
      eAt wq (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) * eAt wq (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) *
        eAt wq (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) *
        (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * eAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2))) *
        (sub l ex (Xv 0) (Xv 1) * eAt E (sub l ex (Xv 0) (Xv 1))) *
        (sub l ex (Xv 1) (Xv 2) * eAt E (sub l ex (Xv 1) (Xv 2))) *
        (sub l ex (Xv 2) (Xv 0) * eAt E (sub l ex (Xv 2) (Xv 0))) →
    (∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T = add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * sub l ex (Xv 0) (Xv 1) * sub l ex (Xv 1) (Xv 2) *
        sub l ex (Xv 2) (Xv 0) * n) →
    Simeq (phAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt E (sub l ex (Xv 0) (Xv 1)) +
        phAt E (sub l ex (Xv 1) (Xv 2)) + phAt E (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt E (Xv 0) + phAt E (Xv 1) + phAt E (Xv 2)))

end PI.CubicExponentialFactor
end
end

-- bundled from Formalism.PeriodIntegrals.DepthLegendre
section
namespace PI

def DepthLegendre : Prop :=
  (∀ p : ℕ, p.Prime → ∀ c : ℕ, 1 ≤ c → (p - 1) * padicValNat p c.factorial < c) ∧
  (∀ p : ℕ, 2 ≤ p → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ 2 * ((p : ℝ) ^ n - 1) / ((p : ℝ) - 1) ∧
      (n : ℝ) - 1 ≤ 2 * ((p : ℝ) ^ (n - 1) - 1) / ((p : ℝ) - 1))

end PI
end

-- bundled from Formalism.PeriodIntegrals.DetIdPG
section
open NumberField

namespace PI

namespace DetIdPG

def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i

def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range

end DetIdPG

def DetIdPG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (L L₀ : Submodule (𝓞 E) (Fin N → E)), DetIdPG.IsSDLat E N L → DetIdPG.IsSDLat E N L₀ →
    (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : E) • x ∈ L₀) ∧ ∀ x ∈ L₀, (s : E) • x ∈ L) →
    ∃ (h : ℕ) (z : E), 0 < h ∧ star z * z = 1 ∧ z * star z = 1 ∧ (∀ ψ : E →+* ℂ_[p], ‖ψ z‖ = 1) ∧
      (Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}) ^ h =
        Submodule.span (𝓞 E) {z}

end PI
end

-- bundled from Formalism.PeriodIntegrals.DiagRank
section
namespace PI

open Classical in

def DiagRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

end PI
end

-- bundled from Formalism.PeriodIntegrals.DiffGenLoc
section
noncomputable section

namespace PI.DiffGenLoc

open NumberField IsDedekindDomain

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def DiffExists : Prop := ∃ d, IsDiffVal v d

end PI.DiffGenLoc
end
end

-- bundled from Formalism.PeriodIntegrals.DiscIn
section
namespace PI

def DiscFactor : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r R₁ : ℝ), 0 < R₁ → R₁ < r →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
      (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
      ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z

def DiscLog : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DifferentiableOn ℂ f (Metric.ball z₀ R) →
    (∀ z ∈ Metric.ball z₀ R, f z ≠ 0) →
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ Metric.ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ Metric.ball z₀ R, f z = f z₀ * Complex.exp (g z)

def DiscLogDeriv : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R M : ℝ), 0 < R → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ R) → (∀ z ∈ Metric.closedBall z₀ R, f z ≠ 0) →
    (∀ z ∈ Metric.closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∀ z ∈ Metric.closedBall z₀ (R / 2), ‖deriv f z / f z‖ ≤ 24 * Real.log M / R

def DiscLocal : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r

end PI
end

-- bundled from Formalism.PeriodIntegrals.EagonNorthcott
section
noncomputable section

namespace PI.EagonNorthcott

def lin {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (c : Fin D → ℤ) : R :=
  ∑ i, (c i : R) * x i

def dmap {R : Type*} [CommRing R] {D m n : ℕ} (x : Fin D → R) (C : Matrix (Fin m) (Fin n) (Fin D → ℤ)) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin (C.map (lin x))

def aug {R : Type*} [CommRing R] {D m : ℕ} (x : Fin D → R) (e : Fin m → Fin D → ℕ) : (Fin m → R) →ₗ[R] R :=
  ∑ k, (∏ i, x i ^ e k i) • (LinearMap.proj k : (Fin m → R) →ₗ[R] R)

def Shape (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ)
    (_C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  (∀ j, max D 1 ≤ j → n j = 0) ∧ Function.Injective e ∧ ∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a

def Resolves {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (a : ℕ) {n : ℕ → ℕ} (e : Fin (n 0) → Fin D → ℕ)
    (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  LinearMap.range (aug x e) = Ideal.span (Set.range x) ^ a ∧
    LinearMap.ker (aug x e) = LinearMap.range (dmap x (C 0)) ∧
    ∀ j, LinearMap.ker (dmap x (C j)) = LinearMap.range (dmap x (C (j + 1)))

end PI.EagonNorthcott

namespace PI

open EagonNorthcott in

def EagonNorthcott.{u} : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧
      ∀ (R : Type u) [CommRing R] (x : Fin D → R),
        RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) → Resolves x a e C

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.EllipticRegularity2
section
open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace PI.EllRegPr

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure DOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def DOp.tr (A : DOp d) (ψ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (A.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => A.a k w y * ψ y) x

def DOp.symb (A : DOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin A.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * A.a (Fin.last A.ord) w x

def DOp.SmoothOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop := ∀ k w, ContDiffOn ℝ ∞ (A.a k w) X

def DOp.EllipticOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → A.symb x ξ ≠ 0

def DOp.charSet (A : DOp d) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ A.symb p.1 p.2 = 0}

def IsTest (X : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ X

def distOf (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * ψ x

def distApp (A : DOp d) (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * A.tr ψ x

def ftD (T : ((Fin d → ℝ) → ℂ) → ℂ) (φ : (Fin d → ℝ) → ℂ) (ξ : Fin d → ℝ) : ℂ :=
  T (fun x => φ x * Complex.exp (-(Complex.I * ((x ⬝ᵥ ξ : ℝ) : ℂ))))

def wt (s : ℝ) (ξ : Fin d → ℝ) : ℝ := (1 + ξ ⬝ᵥ ξ) ^ s

def WFs (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ ¬ ∃ (φ : (Fin d → ℝ) → ℂ) (Γ : Set (Fin d → ℝ)), IsTest X φ ∧ φ p.1 ≠ 0 ∧
    IsOpen Γ ∧ p.2 ∈ Γ ∧ (∀ η ∈ Γ, η ≠ 0) ∧ (∀ η ∈ Γ, ∀ t : ℝ, 0 < t → t • η ∈ Γ) ∧
    (∫⁻ ξ in Γ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤}

def HsLoc (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ φ, IsTest X φ → (∫⁻ ξ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤

def WFsEmptyIff : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (s : ℝ), IsOpen X → ContinuousOn u X →
    (WFs s (distOf u) X = ∅ ↔ HsLoc s (distOf u) X)

def WFsChar : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → HsLoc s (distApp A u) X → WFs (s + A.ord) (distOf u) X ⊆ A.charSet X

def WFsElliptic : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → A.EllipticOn X → WFs (s - A.ord) (distApp A u) X = WFs s (distOf u) X

end PI.EllRegPr

namespace PI

def EllipticRegularity2 : Prop := EllRegPr.WFsEmptyIff ∧ EllRegPr.WFsChar ∧ EllRegPr.WFsElliptic

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.EmbPerm
section
noncomputable section

namespace PI

open Classical

def EmbPermDefs.liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0

def EmbPermDefs.cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (EmbPermDefs.liftM M x)

def EmbPerm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      (∀ a : K, φ₀ (a : E) ∈ M ∧ EmbPermDefs.cj M ρ (φ₀ (a : E)) = φ₀ (a : E)) → (∀ s x, emb s x ∈ M) →
      ∃ π : Equiv.Perm S, ∀ s x, EmbPermDefs.cj M ρ (emb s x) = emb (π s) x

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.EmbTraceSum
section
namespace PI

def EmbTraceSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ y : E, ∑ s, emb s y = φ₀ ((Algebra.trace K E y : K) : E)

end PI
end

-- bundled from Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.ExistsGaugeMeasureForEachRank

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def IsGaugeOn (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (μ : Measure (Mt k r)) : Prop :=
  IsHaarOn S μ ∧
    Tendsto (fun ρ : ℝ => (μ (expBall S ρ)).toReal / (volume (Metric.ball (0 : lieE S) ρ)).toReal)
      (𝓝[>] 0) (𝓝 1)

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (UWb 0 r) μ

end PI.ExistsGaugeMeasureForEachRank
end
end

