import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform

noncomputable section

def gaussLattice {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin g)) :=
  Submodule.span ℤ (Set.range fun i : Fin g => WithLp.toLp 2 (B *ᵥ Pi.single i 1))

def gaussShellConst (n : ℕ) : ℝ :=
  3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π))

def GaussSqrt.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ * B = Y

def GaussLatticeIsLattice.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    DiscreteTopology (gaussLattice B) ∧ ∀ [DiscreteTopology (gaussLattice B)], IsZLattice ℝ (gaussLattice B)

def GaussLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ZLattice.covolume (gaussLattice B) = |B.det|

def GaussLatticeCoords.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    (∀ k : Fin g → ℤ, WithLp.toLp 2 (B *ᵥ intVec k) ∈ gaussLattice B) ∧
    (∀ x ∈ gaussLattice B, ∃ k : Fin g → ℤ, x = WithLp.toLp 2 (B *ᵥ intVec k)) ∧
    Function.Injective fun k : Fin g → ℤ => B *ᵥ intVec k

def GaussFourierSelf.Statement : Prop :=
  ∀ (g : ℕ) (w : EuclideanSpace ℝ (Fin g)),
    𝓕 (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) w =
      ((Real.exp (-π * ‖w‖ ^ 2) : ℝ) : ℂ)

def GaussPoissonBound.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 → ∀ a : Fin g → ℝ,
    Summable (fun k : Fin g → ℤ =>
      Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))) ∧
    Summable (fun μ : GroundTheory.Global.dualLattice (gaussLattice B) =>
      Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)) ∧
    ∑' k : Fin g → ℤ, Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a)))) ≤
      |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
        Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussDualMin.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ∀ μ ∈ GroundTheory.Global.dualLattice (gaussLattice B), μ ≠ 0 →
      ∃ l : Fin g → ℤ, l ≠ 0 ∧ qf (Bᵀ * B)⁻¹ (intVec l) ≤ ‖μ‖ ^ 2

def GaussDetFactor.Statement : Prop :=
  ∀ (g : ℕ) (Y B : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → Bᵀ * B = (1 / 2 : ℝ) • Y →
    |B.det|⁻¹ = √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))

def GaussPoissonDual.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∃ Λ : Submodule ℤ (EuclideanSpace ℝ (Fin g)), (∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖) ∧
        ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) ≤
          √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussPacking.Statement : Prop :=
  ∀ (n : ℕ) (s : Finset (EuclideanSpace ℝ (Fin n))) (δ r : ℝ), 0 < δ → 0 ≤ r →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) → (∀ x ∈ s, ‖x‖ ≤ r) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ n

def GaussTermBound.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
    ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2) ≤
      √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))

def GaussShell.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) → ∀ (F : Finset Λ) (m : ℕ),
      ∑ μ ∈ F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ))

def GaussShellSum.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) →
      Summable (fun μ : Λ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)) ∧
      ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        2 * gaussShellConst n * (1 + 1 / δ) ^ n

def GaussConstant.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → √2 ^ n * (2 * gaussShellConst n) ≤ (72 * Real.exp 4 * n) ^ ((n : ℝ) / 2)

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 :=
  ⟨Matrix.PosDef.one, by simp⟩

example : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by simp

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧
    ((√2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ * ((√2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      (1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  refine ⟨Matrix.PosDef.one, ?_⟩
  rw [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one]
  congr 1
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

abbrev gaussUnit : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (Pi.single 0 1)

theorem gaussUnit_norm : ‖gaussUnit‖ = 1 := by
  simp [gaussUnit]

theorem mem_gaussLattice_one {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ) ↔ ∃ a : ℤ, a • gaussUnit = x := by
  have h : (Set.range fun i : Fin 1 => WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      Pi.single i 1)) = {gaussUnit} := by
    rw [Set.range_unique, Matrix.one_mulVec]
    rfl
  rw [gaussLattice, h, Submodule.mem_span_singleton]

theorem gaussLattice_one_min : ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 →
    (1 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hv
  have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, gaussUnit_norm, mul_one, Real.norm_eq_abs]
  exact_mod_cast Int.one_le_abs ha

example : 1 ≤ 1 ∧ (0 : ℝ) < 1 ∧
    ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 → (1 : ℝ) ≤ ‖v‖ :=
  ⟨le_rfl, one_pos, gaussLattice_one_min⟩

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 ∧
    gaussUnit ∈ GroundTheory.Global.dualLattice (gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    gaussUnit ≠ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [GroundTheory.Global.mem_dualLattice]
    intro x hx
    obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hx
    refine ⟨a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, real_inner_self_eq_norm_sq, gaussUnit_norm]
    simp
  · intro h
    have := gaussUnit_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this

example : ∀ x ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))),
    ∀ y ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))), x ≠ y → (1 : ℝ) ≤ ‖x - y‖ := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · simp
  · simp
  · exact absurd rfl hxy

example : ∀ x ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))), ‖x‖ ≤ (1 : ℝ) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp
  · simp

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : ℝ) < 1 ∧
    ∀ l : Fin 1 → ℤ, l ≠ 0 → (1 : ℝ) ^ 2 ≤ qf (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ (intVec l) :=
  ⟨Matrix.PosDef.one, one_pos, isReducedImaginaryPart_one.min⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def symplOmega {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) : R :=
  u ⬝ᵥ (J l R *ᵥ v)

def symplCons {R : Type*} {n : ℕ} (p q : R) (w : Fin n ⊕ Fin n → R) :
    Fin (n + 1) ⊕ Fin (n + 1) → R :=
  Sum.elim (vecCons p fun j => w (Sum.inl j)) (vecCons q fun j => w (Sum.inr j))

def symplTail {R : Type*} {n : ℕ} (u : Fin (n + 1) ⊕ Fin (n + 1) → R) : Fin n ⊕ Fin n → R :=
  fun x => u (Sum.map Fin.succ Fin.succ x)

def symplExt {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  Matrix.of (Sum.elim (vecCons (symplCons α β 0) fun i => symplCons 0 0 (Q (Sum.inl i)))
    (vecCons (symplCons γ δ 0) fun i => symplCons 0 0 (Q (Sum.inr i))))

def symplReduce {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun a b => H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
    H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
      H (Sum.inl 0) (Sum.inl 0)

def symplGram {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) : Matrix l l ℝ :=
  P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ

def SymplOmegaMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R),
    M ∈ symplecticGroup l R ↔ ∀ x y, symplOmega (M x) (M y) = J l R x y

def SymplCons.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    (∀ u : Fin (n + 1) ⊕ Fin (n + 1) → R,
      symplCons (u (Sum.inl 0)) (u (Sum.inr 0)) (symplTail u) = u) ∧
    ∀ (p q p' q' : R) (w w' : Fin n ⊕ Fin n → R),
      symplOmega (symplCons p q w) (symplCons p' q' w') = q * p' - p * q' + symplOmega w w'

def SymplExtMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    α * δ - β * γ = 1 → Q ∈ symplecticGroup (Fin n) R →
    symplExt α β γ δ Q ∈ symplecticGroup (Fin (n + 1)) R

def SymplExtVecMul.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ p q : R)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (w : Fin n ⊕ Fin n → R),
    symplCons p q w ᵥ* symplExt α β γ δ Q = symplCons (p * α + q * γ) (p * β + q * δ) (w ᵥ* Q)

def SymplTwoRow.Statement : Prop :=
  ∀ (n : ℕ) (c d x y : ℤ), x * c + y * d = 1 →
    ∃ P ∈ symplecticGroup (Fin (n + 1 + 1)) ℤ, P (Sum.inl 0) = symplCons c 0 (symplCons d 0 0)

def SymplGcd.Statement : Prop :=
  ∀ a b : ℤ, ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1

def SymplOrbit.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ),
    ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, ∃ m : ℤ, v = m • P (Sum.inl 0)

def SymplQuadDiag.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ (O : Matrix ι ι ℝ) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧ |O.det| = 1 ∧ ∏ i, lam i = G.det ∧
      ∀ x : ι → ℝ, qf G x = ∑ i, lam i * (O *ᵥ x) i ^ 2

def SymplBoxVolume.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), A.det ≠ 0 →
    (∀ i, 0 < a i) →
    MeasureTheory.volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      ENNReal.ofReal ((∏ i, 2 * a i) / |A.det|)

def SymplMinkowskiBox.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), |A.det| = 1 →
    (∀ i, 0 < a i) → 1 < ∏ i, a i →
    ∃ v : ι → ℤ, v ≠ 0 ∧ ∀ i, |(A *ᵥ intVec v) i| < a i

def SymplMinExists.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m

def SymplMinBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef → G.det = 1 →
    ∀ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m → m ≤ Fintype.card ι

def SymplShortPrim.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∀ (v w : ι → ℤ) (m : ℤ), v = m • w → v ≠ 0 →
    (∀ u : ι → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)) → m = 1 ∨ m = -1

def SymplGramMem.Statement : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    P ∈ symplecticGroup (Fin n) ℤ → G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    symplGram P G ∈ symplecticGroup (Fin n) ℝ ∧ (symplGram P G).PosDef ∧
      (∀ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ,
        symplGram (Q * P) G = symplGram Q (symplGram P G)) ∧
      ∀ x, symplGram P G x x = qf G (intVec (P x))

def SymplFirstRow.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq

def SymplReduceMem.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H ∈ symplecticGroup (Fin (n + 1)) ℝ → H (Sum.inl 0) (Sum.inl 0) ≠ 0 →
    symplReduce H ∈ symplecticGroup (Fin n) ℝ

def SymplReducePosDef.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H.PosDef → (symplReduce H).PosDef

def SymplReduceConj.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
        H (Sum.inl 0) (Sum.inl 0) ∧
      symplReduce (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) = Q * symplReduce H * Qᵀ

def SymplDetSchur.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 →
    A.det = A 0 0 * (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0).det

def SymplReduceStep.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
    H (Sum.inl 0) (Sum.inl 0) ≠ 0 → Q ∈ symplecticGroup (Fin n) ℤ →
    ∃ Q' ∈ symplecticGroup (Fin (n + 1)) ℤ,
      symplGram Q' H (Sum.inl 0) (Sum.inl 0) = H (Sum.inl 0) (Sum.inl 0) ∧
      (symplGram Q' H).toBlocks₁₁.det =
        H (Sum.inl 0) (Sum.inl 0) * (symplGram Q (symplReduce H)).toBlocks₁₁.det

def SymplStep.Statement : Prop :=
  ∀ (n : ℕ) (B : ℝ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    (∀ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, H ∈ symplecticGroup (Fin n) ℝ → H.PosDef →
      ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P H).toBlocks₁₁.det ≤ B) →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (symplGram P G).toBlocks₁₁.det ≤ ρsq * B

def SymplDetBound.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P G).toBlocks₁₁.det ≤ (2 * (n : ℝ)) ^ n

example (n : ℕ) :
    (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) ∈
        symplecticGroup (Fin (n + 1)) ℝ ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ).PosDef ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) (Sum.inl 0) (Sum.inl 0) ≠ 0 ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℤ) ∈
        symplecticGroup (Fin (n + 1)) ℤ :=
  ⟨Submonoid.one_mem _, Matrix.PosDef.one, by simp, Submonoid.one_mem _⟩

example : siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 1 ∧
    siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
    simp [siegelGram] at this
  · simp [siegelGram]

example (n : ℕ) : (1 : ℤ) * 1 - 0 * 0 = 1 ∧ (2 : ℤ) * 1 - 1 * 1 = 1 ∧
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) ∈ symplecticGroup (Fin n) ℤ :=
  ⟨by norm_num, by norm_num, Submonoid.one_mem _⟩

example : (-1 : ℤ) * 2 + 1 * 3 = 1 := by norm_num

example : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 ∧ |(1 : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 ∧
    (∀ i : Fin 2, (0 : ℝ) < (fun _ => 2) i) ∧ (1 : ℝ) < ∏ _i : Fin 2, (2 : ℝ) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧ (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  refine ⟨by simp, by simp, fun _ => by norm_num, by norm_num, Matrix.PosDef.one, by simp⟩

example : (fun _ : Fin 1 => (1 : ℤ)) = (1 : ℤ) • (fun _ : Fin 1 => (1 : ℤ)) ∧
    (fun _ : Fin 1 => (1 : ℤ)) ≠ 0 ∧
    ∀ u : Fin 1 → ℤ, u ≠ 0 →
      qf (1 : Matrix (Fin 1) (Fin 1) ℝ) (intVec fun _ => (1 : ℤ)) ≤ qf 1 (intVec u) := by
  refine ⟨by simp, fun h => by simpa using congrFun h 0, ?_⟩
  intro u hu
  have h0 : u 0 ≠ 0 := by
    intro h; apply hu; funext i; fin_cases i; exact h
  have h1 : (1 : ℝ) ≤ |(u 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 : (1 : ℝ) ≤ (u 0 : ℝ) * (u 0 : ℝ) := by
    nlinarith [abs_mul_abs_self (u 0 : ℝ), abs_nonneg (u 0 : ℝ)]
  simpa [qf, intVec, dotProduct] using h2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def thetaSummand {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ)
    (k : Fin g → ℤ) : ℂ :=
  Complex.exp (π * Complex.I *
      ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
    2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (u i : ℂ))

def ThetaSummandNorm.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) (k : Fin g → ℤ), Y.IsSymm →
    ‖thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ *
        exp (-π * qf Y u₁) = exp (-π * qf Y (intVec k + a + u₁))

def ThetaNormMajorant.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ), Y.PosDef →
    thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁))

def ThetaCharIntegral.Statement : Prop :=
  ∀ (g : ℕ) (m : Fin g → ℤ),
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, torusChar m u = if m = 0 then 1 else 0

def ThetaCubeParseval.Statement : Prop :=
  ∀ (g : ℕ) (c : (Fin g → ℤ) → ℂ), Summable (fun k => ‖c k‖) →
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ‖∑' k, c k * torusChar k u‖ ^ 2 = ∑' k, ‖c k‖ ^ 2

def ThetaInnerMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ : Fin g → ℝ), Y.PosDef →
    ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
      ∑' k : Fin g → ℤ, exp (-(2 * π) * qf Y (intVec k + a + u₁))

def ThetaMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ), Y.PosDef →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ))

def ThetaFirstCoordSplit.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ), Y.PosDef → 0 < ρ →
    Y⁻¹ 0 0 = ρ ^ 2 →
    ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁)))

def ThetaConstants.Statement : Prop :=
  ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (ρ d : ℝ), 1 ≤ g → 0 < ρ → 0 < d → ρ ^ 2 ≤ 2 * g → d⁻¹ ≤ ρ ^ 2 * (2 * g) ^ (g - 1) →
      (C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g ≤
        ((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) * exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))

example {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) :
    thetaChar X Y a b z = ∑' k, thetaSummand X Y a b z k := rfl

example {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) :
    thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
      (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * exp (-π * qf Y u₁) := rfl

example : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := Matrix.isSymm_one

example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, fun x hx => ?_⟩
  have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; push_neg at h; apply hx; ext i; fin_cases i <;> simp [h.1, h.2]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    star_trivial]
  rcases h with h | h
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 0)]
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 1)]

example : Summable (fun k : Fin 1 → ℤ => ‖(if k = 0 then (1 : ℂ) else 0)‖) :=
  summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp_all)

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : ℝ) < 1 ∧
    (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ 0 0 = 1 ^ 2 :=
  ⟨Matrix.PosDef.one, one_pos, isReducedImaginaryPart_one.first⟩

example : (0 : ℝ) < 1 ∧ 1 ≤ (2 : ℕ) ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧
    (1 : ℝ) ^ 2 ≤ 2 * ((2 : ℕ) : ℝ) ∧ (1 / 2 : ℝ)⁻¹ ≤ 1 ^ 2 * (2 * ((2 : ℕ) : ℝ)) ^ (2 - 1) := by
  norm_num

end

end GroundTheory.Heights₂.Heights
end

