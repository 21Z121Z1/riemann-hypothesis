import Mathlib
import Formalism.LogVandermondeBounds.Bundle0002
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

-- bundled from Formalism.GL3MeanSquares.FourierTransformKernelSurjective
section
namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix

def SumZeroLatticeSpanning : Prop :=
  ∀ n : ℕ,
    (∀ v : Fin (n + 1) → ℤ, ∑ i, v i = 0 →
      v = ∑ i : Fin n, v i.castSucc • (Pi.single i.castSucc (1 : ℤ) - Pi.single (Fin.last n) 1)) ∧
    (Matrix.of fun i j : Fin n =>
        ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ
          (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))).det = n + 1

def SlopeTensorProductAdditive : Prop :=
  ∀ (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (A : Matrix a a ℝ) (B : Matrix b b ℝ), 0 < A.det → 0 < B.det →
    -Real.log (Matrix.kroneckerMap (· * ·) A B).det / ((Fintype.card a : ℝ) * Fintype.card b) =
      -Real.log A.det / Fintype.card a + -Real.log B.det / Fintype.card b

def LemmaB'_avg : Prop :=
  ∀ (k n : ℕ) (S : Finset (Fin k → ℕ)) (mult : (Fin k → ℕ) → ℕ),
    (∀ σ : Equiv.Perm (Fin k), ∀ w ∈ S, w ∘ σ ∈ S) →
    (∀ σ : Equiv.Perm (Fin k), ∀ w, mult (w ∘ σ) = mult w) →
    (∀ w ∈ S, ∑ i, w i = n) →
    ∀ j : Fin k, k * ∑ w ∈ S, mult w * w j = n * ∑ w ∈ S, mult w

def LemmaB'_twist : Prop :=
  ∀ (k : ℕ) (lam : Fin (k + 2) → ℚ) (a W b' : ℚ),
    lam 0 = a → (∀ i : Fin (k + 2), i ≠ 0 → |lam i| ≤ W) → lam (Fin.last (k + 1)) = -b' →
    (∑ i, (lam i + b')) / (k + 2 : ℚ) ≤ a / (k + 2 : ℚ) + 2 * W

def compF {q n n' : ℕ} (fW : Fin n' → ZMod q) (x : Matrix (Fin n') (Fin n) ℤ) : Fin n → ZMod q :=
  fun j => ∑ i, fW i * (x i j : ZMod q)

def SupportCosetStructure : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ZMod q) (f : Fin n → ZMod q), fW ≠ 0 →
    ∃ x0 : Matrix (Fin n') (Fin n) ℤ,
      (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f ↔ compF fW (x - x0) = 0) ∧
      compF fW ((q : ℤ) • x0) = 0 ∧
      (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f →
        ∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
          (∑ i, fW i * ((x.mulVec l) i : ZMod q)) = 0)

def LinearFormIntegralityOnSupport : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ZMod q) (f : Fin n → ZMod q),
    (∀ x : Matrix (Fin n') (Fin n) ℤ, compF fW x = f →
      ∀ l : Fin n → ℤ, (∑ j, f j * (l j : ZMod q)) = 0 →
      ∀ η : Fin n' → ℚ, (∀ μ : Fin n' → ℤ, (∑ i, fW i * (μ i : ZMod q)) = 0 →
          (∑ i, η i * μ i) ∈ Set.range (Int.cast : ℤ → ℚ)) →
        (∑ i, η i * ((x.mulVec l) i : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
    (2 ≤ n → fW ≠ 0 → f ≠ 0 →
      ∃ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ) (η : Fin n' → ℚ),
        (∑ j, f j * (l j : ZMod q)) = 0 ∧
        (∀ μ : Fin n' → ℤ, (∑ i, fW i * (μ i : ZMod q)) = 0 →
          (∑ i, η i * μ i) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
        (∑ i, η i * ((x.mulVec l) i : ℚ)) ∉ Set.range (Int.cast : ℤ → ℚ))

def ExponentLossPerEmbedding : Prop :=
  ∀ (ι : Type) (Ψ : Finset ι) (nonTopP : ι → Prop) [DecidablePred nonTopP]
    (W nu : ι → ℝ) (C N t : ℝ),
    (∀ τ ∈ Ψ, 0 ≤ W τ) → 0 ≤ t → t ≤ N →
    (∀ τ ∈ Ψ, nonTopP τ → nu τ ≤ 2 * W τ + t) →
    ∑ τ ∈ Ψ, (2 * W τ + C * N + if nonTopP τ then nu τ else 0) ≤
      4 * (∑ τ ∈ Ψ, W τ) + (C + 1) * Ψ.card * N

def IndicatorKernelSum : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ) (fW : Fin n' → ℤ) (x0 : Fin n → ℤ)
    (x : Matrix (Fin n') (Fin n) ℚ),
    (fun j => (x0 j : ZMod q)) ≠ 0 →
    let e1 : Fin n → ℚ := fun j => (x0 j : ℚ) / q
    let intMat : Prop := ∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ)
    let rhs : Prop := intMat ∧ ∃ z : ℤ,
      (∑ i, (fW i : ℚ) * (x.mulVec (fun j => (x0 j : ℚ))) i) = z ∧ (z : ZMod q) = 1
    let UKcond : (Fin n' → ZMod q) → Prop := fun xW =>
      (∑ i, (fW i : ZMod q) * xW i) = 1 ∧ intMat ∧
      (∀ i, (x.mulVec e1) i - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      (∀ (l : Fin n → ℤ) (c : ℤ), ∃ (μ : Fin n' → ℤ) (d : ℤ), ∀ i,
        (x.mulVec (fun j => (l j : ℚ) + c * e1 j)) i = μ i + d * ((xW i).val : ℚ) / q)
    let KUcond : (Fin n → ZMod q) → Prop := fun f =>
      (∑ j, f j * (x0 j : ZMod q)) = 1 ∧ intMat ∧
      (∀ j, ∃ z : ℤ, (∑ i, (fW i : ℚ) * x i j) = z ∧ (z : ZMod q) = f j)
    Nat.card {xW // UKcond xW} = Nat.card {f // KUcond f} ∧
    (rhs → Nat.card {f // KUcond f} = 1) ∧ (¬ rhs → Nat.card {f // KUcond f} = 0)

def NonintegralMatrixPreservesThirdOverlattice : Prop :=
  let x : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1/3]
  let e1 : Fin 2 → ℚ := ![1/3, 0]
  (∀ (l : Fin 2 → ℤ) (c : ℤ), ∃ (μ : Fin 1 → ℤ) (d : ℤ), ∀ i,
      (x.mulVec (fun j => (l j : ℚ) + c * e1 j)) i = μ i + d * (1 : ℚ) / 3) ∧
  (∀ i, (x.mulVec e1) i - (1 : ℚ) / 3 ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
  ¬ (∀ i j, x i j ∈ Set.range (Int.cast : ℤ → ℚ))

def SupportVolumeIndex : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (n n' : ℕ),
    (∀ x0 : Fin n → ZMod q, x0 ≠ 0 →
      Nat.card {x : Matrix (Fin n') (Fin n) (ZMod q) // x.mulVec x0 = 0} * q ^ n' = q ^ (n' * n)) ∧
    (∀ fW : Fin n' → ZMod q, fW ≠ 0 →
      Nat.card {x : Matrix (Fin n') (Fin n) (ZMod q) // Matrix.vecMul fW x = 0} * q ^ n =
        q ^ (n' * n))

def OddHalfShiftSignDichotomyBound : Prop :=
  ∀ (t : ℤ), Odd t → 0 ≤ t → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (vchar W C N : ℝ), |vchar| ≤ 2 * W + C * N →
      (((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) = 0 ∨
        ((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) = t + 1) ∧
      |((t : ℝ) + 1) / 2 + ε * (((t : ℝ) + 1) / 2) + vchar| ≤ t + 1 + 2 * W + C * N

def kerK {q n n' : ℕ} [NeZero q] (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ) (fW : Fin n' → ZMod q) : ℂ :=
  ∑ x, w x * ∑ f, if Matrix.vecMul fW x = f then ph f else 0

def HeckeKernelScalarInvariance : Prop :=
  ∀ (q : ℕ) [NeZero q] (n n' : ℕ) (w : Matrix (Fin n') (Fin n) (ZMod q) → ℂ)
    (ph : (Fin n → ZMod q) → ℂ) (c : (ZMod q)ˣ) (fW : Fin n' → ZMod q),
    kerK w (fun f => ph ((c : ZMod q) • f)) fW = kerK w ph ((c : ZMod q) • fW)

def chainK (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (K : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j
  | 0 => LinearMap.id
  | j + 1 => (K j).comp (chainK R M K j)

def chainUK (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (U : ∀ j, Module.End R (M j)) (K : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j
  | 0 => LinearMap.id
  | j + 1 => ((U (j + 1)).comp (K j)).comp (chainUK R M U K j)

def HeckeProductCommutation : Prop :=
  ∀ (R : Type) [CommRing R] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (U : ∀ j, Module.End R (M j)) (K : ∀ j, M j →ₗ[R] M (j + 1)) (c : ℕ → Rˣ),
    (∀ j, (U (j + 1)).comp (K j) = (c j : R) • (K j).comp (U j)) →
    ∀ m : ℕ, (chainK R M K m).comp ((U 0) ^ m) =
      ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j) : Rˣ) : R) • chainUK R M U K m

def LengthQuotientPowerInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (U : Module.End R M),
    Function.Injective U → ∀ m : ℕ,
      Module.length R (M ⧸ LinearMap.range (U ^ m)) = m • Module.length R (M ⧸ LinearMap.range U)

def LengthQuotientTwistFormula : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (T : R),
    (∀ x : M, T • x = 0 → x = 0) → ∀ (N : Submodule R M) (c : ℕ),
      Module.length R (M ⧸ N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))) =
        Module.length R (M ⧸ N) +
          c • Module.length R (N ⧸ LinearMap.range (T • (LinearMap.id : Module.End R N)))

def ConsecutiveRatioPowerBound : Prop :=
  ∀ q f N : ℕ, 2 ≤ N → 1 ≤ f → 2 * f * N + 1 < q →
    (((q : ℝ) - 1) / ((q : ℝ) - 2)) ^ f ≤ 1 + 2 * (f : ℝ) / q

def ExponentTotalBound : Prop :=
  ∀ (ι : Type) (Ψ TT VV : Finset ι) (W bp : ι → ℝ) (m t f N C1 C2 e1 : ℝ),
    VV ⊆ TT → 1 ≤ m → 0 ≤ t → t + 1 ≤ N → 0 ≤ f → 0 ≤ C1 → 0 ≤ C2 →
    (∀ τ ∈ Ψ, 0 ≤ W τ) → (∀ τ ∈ TT, 0 ≤ bp τ) → (∀ τ ∈ VV, W τ ≤ 2 * bp τ) →
    e1 ≤ 4 * (∑ τ ∈ Ψ, W τ) + C1 * f * N →
    m * e1 + (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤
      (C1 + C2 + 9) * m * ((∑ τ ∈ Ψ, W τ) + f * m * N + m * ∑ τ ∈ TT, (bp τ + N))

def KroneckerRootOfUnity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (α : K), IsIntegral ℤ α → α ≠ 0 →
    (∀ σ : K →+* ℂ, ‖σ α‖ ≤ 1) →
    (∀ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ = 1 ∨ ζ = -1) →
    α = 1 ∨ α = -1

def InterlacingDegreeDifference : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ),
    (∀ i : Fin n, sg i ≤ lam i.castSucc ∧ lam i.succ ≤ sg i) →
    (∑ i, lam i - ∑ i, sg i ≤ lam 0) ∧ (lam (Fin.last n) ≤ ∑ i, lam i - ∑ i, sg i) ∧
    (∀ (h : 0 < n) (W : ℤ), sg ⟨0, h⟩ ≤ W → -W ≤ lam (Fin.last n) →
      lam 0 - 2 * W ≤ ∑ i, lam i - ∑ i, sg i)

def Uc {F : Type} [Field F] {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (c : F) :
    Submodule F ((Fin n → F) × F) :=
  (LinearMap.ker fL).map (LinearMap.inl F (Fin n → F) F) ⊔ Submodule.span F {((-c) • e, (1 : F))}

noncomputable def fjCount {F : Type} [Field F] {n g : ℕ} (fL : (Fin n → F) →ₗ[F] F)
    (e : Fin n → F) (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (c : F) : ℕ :=
  Nat.card {fW : Fin (n + g) → F // (∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧
    fW ⬝ᵥ x' (e, 0) = 1 ∧ fW ⬝ᵥ x' (0, 1) = c}

def KernelDimensionCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n g : ℕ), 1 ≤ g →
    ∀ (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F), fL e = 1 →
    ∀ (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (c : F),
      (fjCount fL e x' c : ℤ) * ((Fintype.card F : ℤ) - 1) =
        (Fintype.card F : ℤ) ^ (g + Module.finrank F (Uc fL e c ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F))) -
        (Fintype.card F : ℤ) ^ (g - 1 + Module.finrank F (LinearMap.ker x'))

def CharacterSumCancellation : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n g : ℕ), 1 ≤ g →
    ∀ (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F), fL e = 1 →
    ∀ (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) (ψ : AddChar F ℂ), ψ ≠ 1 →
      ∑ c : F, ψ c * (fjCount fL e x' c : ℂ) =
        (Fintype.card F : ℂ) ^ g * ∑ e' : Fin n → F, ψ (fL e') * (if x' (-e', 1) = 0 then 1 else 0)

def PrimitiveOrbitFunctionalUnique : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (f g e : Fin n → F), f ⬝ᵥ e = 1 →
    (((∀ l, f ⬝ᵥ l = 0 → g ⬝ᵥ l = 0) ∧ g ⬝ᵥ e = 1) ↔ g = f)

def FourierCommutesHeckeScalar : Prop :=
  ∀ (R : Type) [CommRing R] (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (U D G : Module.End R M) (U' D' G' : Module.End R M') (K : M →ₗ[R] M')
    (c a a' : R),
    U' ∘ₗ K = c • (K ∘ₗ U) → D' ∘ₗ U' = a' • LinearMap.id → U ∘ₗ D = a • LinearMap.id →
    K ∘ₗ G = G' ∘ₗ K →
    a' • (K ∘ₗ D ∘ₗ G) = (c * a) • (D' ∘ₗ G' ∘ₗ K)

def FourierTransformKernelSurjective : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (r : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ ψv : (Fin r → k) → ℂ, (∀ x, x ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmV ψv x = 0) →
      ∃ φ : (Fin r → k) → ℂ, (∀ f, f ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP φ f = 0) ∧
        ∀ x, x ≠ 0 → Formalism.LogVandermondeBounds.product_first_zeroth_parts.opFF ψ φ x = ψv x

def QuotientLengthEmbeddingBound : Prop :=
  ∀ (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M] (A N : Submodule R M),
    Module.length R (A ⧸ N.comap A.subtype) ≤ Module.length R (M ⧸ N)

def Joint_coef : Prop :=
  ∀ (ι : Type) (TT : Finset ι) (a W : ι → ℝ)
    (L k m f q e logP muM0 muRam muN EP E0 Eprice : ℝ),
    0 < L → 2 ≤ k → 0 ≤ m → 0 ≤ f → 0 < q → (∀ τ ∈ TT, 0 ≤ a τ ∧ 4 * a τ < q) →
    (∀ τ ∈ TT, 0 ≤ W τ) →
    logP ≤ -(∑ τ ∈ TT, a τ) * L + EP →
    -muM0 ≤ (∑ τ ∈ TT, a τ) / k * L + E0 →
    muM0 - muRam ≤ f →
    muRam - muN + 2 * e * L ≤
      (∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q)) * L + Eprice →
    logP - muN + 2 * e * L ≤
      -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L +
        (∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k))) * L +
        (EP + E0 + f + Eprice)

end Formalism.HermitianLattices.LocalLatticeBases
end

-- bundled from Formalism.GL3MeanSquares.InverseNormLeOfIntegerInner
section
namespace Formalism.HermitianLattices.LatticeEstimates

open Finset MeasureTheory
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder

def Ms_min : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    (Module.finrank ℚ K : ℝ) ≤ ∑ φ : K →+* ℂ, ‖φ (x : K)‖ ^ 2

def Ms_entry : Prop :=
  ∀ (f : ℕ) (p q : Fin f → ℝ) (z : Fin f → ℂ) (R2 : ℝ), (∀ τ, 0 ≤ p τ) → (∀ τ, 0 ≤ q τ) →
    (∀ τ, ‖z τ‖ ^ 2 ≤ p τ * q τ) → ∑ τ, p τ ≤ R2 → ∑ τ, q τ ≤ R2 → ∑ τ, ‖z τ‖ ^ 2 ≤ R2 ^ 2

def Ms_hadamard : Prop :=
  ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), G.PosSemidef → G.det.re ≤ ∏ c, (G c c).re

def Ms_between : Prop :=
  ∀ (R G : Type) [Ring R] [AddCommGroup G] [Module R G] [Finite G] (r : ℕ),
    Nat.card {H : Submodule R G // ∃ s : Fin r → G, Submodule.span R (Set.range s) = H} ≤ Nat.card G ^ r

def MeanValueInequalityRadial : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℂ), Differentiable ℂ F →
    (∀ θ : ℝ, μ.map (fun w : E => Complex.exp (θ * Complex.I) • w) = μ) →
    Integrable (fun w => ‖F w‖ ^ 2) μ → ‖F 0‖ ^ 2 ≤ ∫ w, ‖F w‖ ^ 2 ∂μ

def WeightedCauchySchwarz : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (q c : ι → ℂ) (O : ℝ), (∀ e, 0 < w e) → 0 < O →
    ‖∑ e, q e * (w e : ℂ) * c e‖ ^ 2 ≤ (∑ e, ‖q e‖ ^ 2 * w e) * O⁻¹ * ∑ e, ‖c e‖ ^ 2 * w e * O

def L1LeSqrtCardOfL2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℂ), ∑ e, ‖c e‖ ^ 2 ≤ 1 → ∑ e, ‖c e‖ ≤ Real.sqrt (Fintype.card ι)

def UnitaryMinorNormLeOne : Prop :=
  ∀ (n r : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) (e e' : Fin r → Fin n), U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    ‖(U.submatrix e e').det‖ ≤ 1

def InverseNormLeOfIntegerInner : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x φ : V) (z : ℤ), z ≠ 0 →
    inner ℂ x φ = (z : ℂ) → 1 / ‖x‖ ≤ ‖φ‖

def InterlacingLogSquareBound : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (T c rho : ℝ), Interlace lam nu → 1 ≤ T →
    c ≠ 0 → |c| ≤ (Wnum lam : ℝ) ^ (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) →
    0 < rho → rho ^ 2 ≤ T ^ (-(degZ lam nu)) * weylDim lam →
    Real.log ((c * rho) ^ 2) ≤ MeanSquareTwistBound lam nu (Real.log T)

def MuMaxBoundOfAntitoneWeight : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (muMax dmin cc : ℝ), Antitone lam →
    0 < cc → 0 < dmin → (((κ : ℝ) + 1) ^ (wt (plus lam)).toNat)⁻¹ ≤ dmin →
    cc ≤ ((plus lam 0 : ℝ) + κ + 1) ^ ((κ + 1) ^ 2) → muMax ≤ -Real.log dmin + Real.log cc →
    muMax ≤ MeanSquareWeightBound lam

def AntitoneWeightLogBoundExists : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (v logT logNorm muStd mu : ℝ),
    1 ≤ v → 0 ≤ logT → Antitone lam →
    logNorm ≤ Real.log (C₀ * ((κ : ℝ) + 1) ^ 3 * v ^ 2) → muStd ≤ MeanSquareWeightBound lam →
    mu ≤ (wt (plus lam) : ℝ) * logNorm + muStd - (lam (Fin.last κ) : ℝ) * logT →
    mu ≤ (wt (plus lam) : ℝ) * (C * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1) + |(lam (Fin.last κ) : ℝ)| * logT

def Col_other : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (S : ℤ), (κ : ℤ) + 1 ≤ S → 0 ≤ lam (Fin.last κ) → lam 0 ≤ 3 * S →
    (∀ i, i ≠ 0 → lam i - lam (Fin.last κ) ≤ S + 1) → wt (plus lam) ≤ (κ + 1 + 3) * S

end Formalism.HermitianLattices.LatticeEstimates
end

-- bundled from Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
section
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))

def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))

def SmoothedRemainderLipschitz : Prop :=
  ∀ CM : ℝ, (∀ y : ℝ, 1 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ Real.log y + CM) →
    ∀ (a : ℕ → ℂ) (S : ℂ), (∀ n, ‖a n‖ ≤ Λ n) →
    ∀ y₁ y₂ : ℝ, 1 ≤ y₁ → y₁ ≤ y₂ →
      ‖Gchi a S y₂ - Gchi a S y₁‖ ≤ (Real.log y₂ + CM + ‖S‖) * (y₂ - y₁)

def SmoothedRemainderRealLipschitz : Prop :=
  ∀ (CM : ℝ) (a : ℕ → ℝ),
    (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ) - Real.log y| ≤ CM) →
    ∀ y₁ y₂ : ℝ, 1 ≤ y₁ → y₁ ≤ y₂ →
      |Gone a y₂ - Gone a y₁| ≤ (CM + Real.eulerMascheroniConstant) * (y₂ - y₁)

def ZeroFreeSymmetric : Prop :=
  ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 = 1 → GoodFor Q χ →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ Q → Formalism.ZeroFreeDirichlet.IsLZero χ s →
      1 / 400 ≤ s.re ∧ s.re ≤ 1 - 1 / 400

def ZeroSumBoundSmall : Prop :=
  ∀ C₂ C₃ : ℝ, 0 < C₂ → 0 < C₃ → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (Q u : ℝ) (Zs : Multiset ℂ) (ψ : ℂ), 3 ≤ Q → 2 ≤ u →
      (∀ ρ ∈ Zs, ρ.re ≤ 1 - 1 / 400) →
      (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * Real.log Q ^ 2 →
      ‖ψ + (Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ ≤
        C₃ * (u / Q * Real.log (u * Q) ^ 2 + Real.log (u * Q) ^ 2) →
      ‖ψ‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)

def ZeroSumBoundLarge : Prop :=
  ∀ c C₂ : ℝ, 0 < c → 0 < C₂ → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧
    ∀ (Q u : ℝ) (Zs : Multiset ℂ), 3 ≤ Q → Real.exp (Real.log Q ^ 2) ≤ u →
      (∀ ρ ∈ Zs, |ρ.im| ≤ Real.exp (Real.sqrt (Real.log u)) ∧
        ρ.re ≤ 1 - c / Real.log (Q * (|ρ.im| + 3))) →
      (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * Real.log (Q * Real.exp (Real.sqrt (Real.log u))) ^ 2 →
      ‖(Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))

def PartialSumIntegralBound : Prop :=
  ∀ C₁ c₁ : ℝ, 0 < C₁ → 0 < c₁ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Q : ℝ) (a : ℕ → ℂ), 3 ≤ Q →
      (∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
        C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) →
      (∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
        ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))) →
      ∀ Z U : ℝ, 2 ≤ Z → Z ≤ U →
        ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤
          C * (Z ^ (-(1 : ℝ) / 400) * Real.log (Z * Q) ^ 2 + Q ^ (-c))

def PrimeCountAsymptoticInProgressions (C₀ Cr cr cb : ℝ) : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
    (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
    ∀ Y : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y →
      |(m.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) - Emain θ β Y|
        ≤ rhoErr Cr cr (4 * m) Y * Emain θ β Y

def ShortIntervalImpliesProgressions : Prop :=
  ShortIntervalLowerBound → ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb → PrimeCountAsymptoticInProgressions C₀ Cr cr cb →
    ∃ C₀' c : ℝ, 0 < C₀' ∧ 0 < c ∧ PrimesAPInterval C₀' Cr cr c

def KronOdd : Prop :=
  ∀ q n : ℕ, q % 4 = 3 → Odd n → jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q

def KronTwo : Prop :=
  ∀ q : ℕ, q % 4 = 3 → ZMod.χ₈ ((-(q : ℤ) : ℤ) : ZMod 8) = jacobiSym 2 q

def ClassConst : Prop :=
  ∀ m₀ d q q' : ℕ, 8 ∣ m₀ → d ∣ m₀ → Squarefree d → Odd q → Odd q' → q ≡ q' [MOD m₀] →
    jacobiSym (d : ℤ) q = jacobiSym (d : ℤ) q'

def inPart (m₀ m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => p ∣ m₀ ∧ Odd (m.factorization p)), p

def JacobiInOut : Prop :=
  ∀ m₀ m q : ℕ, 0 < m → Nat.Coprime m q →
    jacobiSym (m : ℤ) q = jacobiSym (inPart m₀ m : ℤ) q * jacobiSym (outPart m₀ m : ℤ) q

def LamSumZero : Prop :=
  ∀ m₀ s a₀ : ℕ, 0 < m₀ → 1 < s → Odd s → Squarefree s → Nat.Coprime s m₀ →
    ∑ b ∈ (range (m₀ * s)).filter (fun b => b ≡ a₀ [MOD m₀]), jacobiSym (b : ℤ) s = 0

def MuConst : Prop :=
  ∀ (F : Finset ℕ) (lam N η : ℕ → ℝ) (M ρ : ℝ), 0 ≤ M → 0 ≤ ρ → ρ < 1 →
    (∀ b ∈ F, |lam b| ≤ 1) → (∑ b ∈ F, lam b) = 0 → (∀ b ∈ F, |η b| ≤ ρ) →
    (∀ b ∈ F, N b = M * (1 + η b)) →
    |∑ b ∈ F, lam b * N b| / (∑ b ∈ F, N b) ≤ ρ / (1 - ρ)

def MuSmall : Prop :=
  ∀ (F : Finset ℕ) (lam N η θ : ℕ → ℝ) (T t δ ρ : ℝ), 0 ≤ T → 0 ≤ t → t ≤ δ → δ < 1 → 0 ≤ ρ → ρ < 1 →
    (∀ b ∈ F, |lam b| ≤ 1) → (∑ b ∈ F, lam b) = 0 → (∀ b ∈ F, |θ b| ≤ 1) → (∀ b ∈ F, |η b| ≤ ρ) →
    (∀ b ∈ F, N b = T * (1 - θ b * t) * (1 + η b)) →
    |∑ b ∈ F, lam b * N b| / (∑ b ∈ F, N b) ≤ (ρ * (1 + δ) + δ) / ((1 - δ) * (1 - ρ))

def MeanRemove : Prop :=
  ∀ (A A' : Finset ℕ) (f : ℕ → ℝ) (X : ℝ), 0 < X → A' ⊆ A →
    ((A \ A').card : ℝ) ≤ X ^ ((1 : ℝ) / 2) → X ^ ((9 : ℝ) / 10) ≤ (A.card : ℝ) → (∀ q ∈ A, |f q| ≤ 1) →
    |(∑ q ∈ A, f q) / (A.card : ℝ) - (∑ q ∈ A', f q) / (A'.card : ℝ)| ≤ 2 * X ^ (-(2 : ℝ) / 5)

def sP (x : ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun i => p ^ i ≤ ⌊x ^ (400 : ℝ)⌋₊), cn x (p ^ i)

def Rsum (x : ℝ) (m₀ : ℕ) : ℝ :=
  (∑ n ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun n => IsSquare n), cn x n) +
    (∑ p ∈ m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊), sP x p)

def SizeSumC : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n ≤ C * x * Real.log x

def SizeSpAll : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ p : ℕ, p.Prime → sP x p ≤ C * Real.log x

def SizeSpLarge : Prop :=
  ∀ x : ℝ, 0 < x → ∀ p : ℕ, p.Prime → x < p → sP x p ≤ 2 * x * Real.log p / p

def SizeR : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ x : ℝ, 2 ≤ x → ∀ m₀ : ℕ, 0 < m₀ →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ (400 : ℝ) < p) →
      Rsum x m₀ ≤ C * (x ^ ((1 : ℝ) / 2) + x ^ (ε / 5) * Real.log x)

def SizeSpSq : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 ≤ C * x * Real.log x

end Formalism.HermitianLattices.GL2a2
end
end

