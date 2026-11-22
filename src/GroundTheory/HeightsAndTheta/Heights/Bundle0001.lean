import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.CovolumeGram
section
namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix Module

theorem covolume_eq_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by
  have hcard : Fintype.card ι = finrank ℝ V := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hcard).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, gram_eq_conjTranspose_mul o, det_mul, det_conjTranspose, star_trivial,
    ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding Matrix Real
open scoped ComplexOrder nonZeroDivisors

noncomputable section

def genIndex {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

variable {K : Type*} [Field K]

def embVec (σ : K →+* ℂ) {n : ℕ} (v : Fin n → K) : Fin n → ℂ := fun j => σ (v j)

def gramAt {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} (u : ι → Fin n → K) :
    Matrix ι ι ℂ :=
  fun a b => star (embVec σ (u a)) ⬝ᵥ (h *ᵥ embVec σ (u b))

variable [NumberField K]

structure HermLattice (K : Type*) [Field K] [NumberField K] (n : ℕ) where

  lattice : Submodule (𝓞 K) (Fin n → K)
  fg : lattice.FG
  span_eq : Submodule.span K (lattice : Set (Fin n → K)) = ⊤

  metric : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ
  posDef : ∀ σ, (metric σ).PosDef
  conj : ∀ σ, metric (conjugate σ) = (metric σ).map (starRingEnd ℂ)

def subDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) : ℝ :=
  log (genIndex (L ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ, log (gramAt (h σ) σ u).det.re

def quotDegree {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K)) (h : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (b : ι → Fin n → K) (c : κ → Fin n → K) : ℝ :=
  log (genIndex (L ⊔ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range c) ⊔
        (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)).toAddSubgroup) -
    1 / 2 * ∑ σ : K →+* ℂ,
      (log (gramAt (h σ) σ (Sum.elim b c)).det.re - log (gramAt (h σ) σ b).det.re)

variable (K) in

def normalise (x : ℝ) : ℝ := x / Module.finrank ℚ K

namespace HermLattice

variable {n : ℕ}

def degree (F : HermLattice K n) : ℝ :=
  subDegree F.lattice F.metric (fun j : Fin n => (Pi.single j 1 : Fin n → K))

def slope (F : HermLattice K n) : ℝ := normalise K F.degree / n

def lineDegree (F : HermLattice K n) (K' : Type*) [Field K'] [NumberField K'] [Algebra K K']
    (v : Fin n → K') : ℝ :=
  normalise K' (subDegree
    (Submodule.span (𝓞 K') ((fun w : Fin n → K => fun j => algebraMap K K' (w j)) '' F.lattice))
    (fun σ' => F.metric (σ'.comp (algebraMap K K'))) (fun _ : Fin 1 => v))

end HermLattice

def idealLattice {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.pi Set.univ fun x => (a x : Submodule (𝓞 K) K)

def diagMetric {n : ℕ} (d : (K →+* ℂ) → Fin n → ℝ) : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => Matrix.diagonal fun x => (d σ x : ℂ)

def OrthogonalLines.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ),
    (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) → (∀ σ x, d (conjugate σ) x = d σ x) → ∀ μ : ℝ,
    (∀ x, μ ≤ normalise K (subDegree (idealLattice a) (diagMetric d)
      (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)))) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      k * μ ≤ normalise K (quotDegree (idealLattice a) (diagMetric d) b c)

def LineOfLargeDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), 1 ≤ i → ∀ (F : HermLattice K i) (ε : ℝ), 0 < ε →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
      v ≠ 0 ∧ F.slope - 1 / 2 * log i - ε ≤ F.lineDegree K' v

def HermLattice.standard (K : Type*) [Field K] [NumberField K] (n : ℕ) : HermLattice K n where
  lattice := Submodule.span (𝓞 K) (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    have h : (Set.range fun j : Fin n => (Pi.single j 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

example : 1 ≤ 2 ∧ (0 : ℝ) < 1 ∧ (HermLattice.standard ℚ 2).metric = fun _ => 1 :=
  ⟨by norm_num, one_pos, rfl⟩

example :
    let a : Fin 2 → FractionalIdeal (𝓞 ℚ)⁰ ℚ := fun _ => 1
    let d : (ℚ →+* ℂ) → Fin 2 → ℝ := fun _ _ => 1
    let deg : Fin 2 → ℝ := fun x => normalise ℚ (subDegree (idealLattice a) (diagMetric d)
      (fun _ : Fin 1 => (Pi.single x 1 : Fin 2 → ℚ)))
    (∀ x, a x ≠ 0) ∧ (∀ σ x, 0 < d σ x) ∧ (∀ σ x, d (conjugate σ) x = d σ x) ∧
      ∀ x, min (deg 0) (deg 1) ≤ deg x := by
  intro a d deg
  refine ⟨fun _ => one_ne_zero, fun _ _ => one_pos, fun _ _ => rfl, ?_⟩
  intro x
  fin_cases x
  · exact min_le_left _ _
  · exact min_le_right _ _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def SymplecticReduction.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      ρsq ≤ 2 * g ∧
      ∃ P ∈ symplecticGroup (Fin g) ℤ,
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁.det ≤
          ρsq * (2 * g) ^ (g - 1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def SiegelCoordinates.Statement : Prop :=
  ∀ g : ℕ,
    (∀ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm → Y.PosDef →
      siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef) ∧
    ∀ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
      ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
        XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2

def FirstCoordinateBound.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∀ v : Fin g → ℝ,
    v 0 ^ 2 / Y⁻¹ 0 0 ≤ qf Y v

def GaussianSum.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) →
    ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (↑) + Complex.I • Y.map (↑)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (π * Complex.I *
        ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
          (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
      2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def thetaNorm {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ))‖ *
    exp (-π * qf Y u₁)

structure IsReducedImaginaryPart {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  sq_le : ρ ^ 2 ≤ 2 * g
  first : Y⁻¹ 0 0 = ρ ^ 2
  min : ∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)
  det_le : Y⁻¹.det ≤ ρ ^ 2 * (2 * g) ^ (g - 1)

def ThetaBound.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) [NeZero g] (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ)
    (a b : Fin g → ℝ), X.IsSymm → Y.PosDef → IsReducedImaginaryPart Y ρ →
    (∀ i, ∃ m : ℤ, a i = m / 2) → (∀ i, ∃ m : ℤ, b i = m / 2) →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) ∧
    ∀ u₁ u₂ : Fin g → ℝ,
      thetaNorm X Y a b u₁ u₂ ≤ ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
        exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2 +
          (g * log (1 + 1 / ρ) + C * g * log (2 * g)))

def finMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S

def WeakMatrixArithmetic.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) [NeZero g] (S : Type) [Fintype S] [Nonempty S] (ρ : S → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ √(2 * g)) → 0 ≤ Φ →
      finMean (fun s => π / 96 * (ρ s ^ 2)⁻¹ - (g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g))) ≤ Φ →
      finMean (fun s => (ρ s ^ 2)⁻¹) ≤ C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g)) ≤
        C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => posLog (1 / ρ s)) ≤ 1 / 2 * log (1 + finMean (fun s => (ρ s ^ 2)⁻¹))

def ShortVectors.Statement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L],
    ∃ lam : ℝ, IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam ∧
      (lam / √n) ^ n ≤ ZLattice.covolume L ∧
      ∀ (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ), lam ≤ r →
        {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite ∧
        (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.ncard : ℕ) : ℝ) ≤
          (3 * r / lam) ^ Module.finrank ℝ U - 1

example : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) ∈ symplecticGroup (Fin 1) ℝ ∧
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).PosDef :=
  ⟨Submonoid.one_mem _, Matrix.PosDef.one⟩

example : siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 1 := by
  intro h
  have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
  simp [siegelGram] at this

theorem isReducedImaginaryPart_one : IsReducedImaginaryPart (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 where
  pos := one_pos
  sq_le := by norm_num
  first := by simp
  min := by
    intro l hl
    have h0 : l 0 ≠ 0 := by
      intro h; apply hl; funext i; fin_cases i; exact h
    have h : (1 : ℝ) ≤ |(l 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    have h2 : (1 : ℝ) ≤ (l 0 : ℝ) * (l 0 : ℝ) := by
      nlinarith [abs_mul_abs_self (l 0 : ℝ), abs_nonneg (l 0 : ℝ)]
    simpa [qf, intVec, dotProduct] using h2
  det_le := by simp

example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : Matrix (Fin 1) (Fin 1) ℝ).IsSymm ∧
    ∀ l : Fin 1 → ℤ, l ≠ 0 → (1 : ℝ) ^ 2 ≤ qf (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ (intVec l) :=
  ⟨Matrix.PosDef.one, Matrix.isSymm_zero, isReducedImaginaryPart_one.min⟩

example : (∀ s : Unit, 0 < (fun _ => (1 : ℝ)) s ∧ (fun _ => (1 : ℝ)) s ≤ √(2 * (1 : ℕ))) ∧
    finMean (fun _ : Unit => π / 96 * ((1 : ℝ) ^ 2)⁻¹ -
      ((1 : ℕ) * log (1 + 1 / 1) + 0 * (1 : ℕ) * log (2 * (1 : ℕ)))) ≤ 1 := by
  refine ⟨fun _ => ⟨one_pos, ?_⟩, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · simp only [finMean, Finset.univ_unique, Finset.sum_singleton, Fintype.card_unit]
    have h2 : (0 : ℝ) ≤ log 2 := log_nonneg (by norm_num)
    have hp : π / 96 ≤ 1 := by linarith [pi_lt_four]
    norm_num
    linarith

example (n : ℕ) : IsZLattice ℝ
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) := inferInstance

example (n : ℕ) : DiscreteTopology
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) := inferInstance

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KernelsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Real

noncomputable section

def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det

def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H

def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)

def AlternantRowRule.Statement : Prop :=
  ∀ (r q : ℕ) (μ : Fin r → ℕ),
    psum (Fin r) ℚ q * alternant μ = ∑ i, alternant (μ + Pi.single i q)

def AlternantPush.Statement : Prop :=
  ∀ r s : ℕ, ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ la : Fin r → ℕ, Antitone la →
    antisym (rename Sum.inl (alternant fun a : Fin r => la a + (r - 1 - a)) *
        rename Sum.inr (alternant fun b : Fin s => s - 1 - b)) =
      if ∀ a, s ≤ la a then
        (ε * r.factorial * s.factorial) •
          alternant (Sum.elim (fun a : Fin r => la a + (r - 1 - a)) fun b : Fin s => s - 1 - b)
      else 0

def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν

abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ

variable (f j k : ℕ)

def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)

def rootPsum (m : ℕ) (τ : Fin f) : RootPoly f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) : Fin f × Bool → RootPoly f j k
  | (τ, false) => ∑ a : Fin j, X (τ, Sum.inl a) ^ m
  | (τ, true) => (-1) ^ m * ∑ b : Fin k, X (τ, Sum.inr b) ^ m

def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det

def smallMu : RootPoly f j k :=
  ∑ τ : Fin f, if k ≤ j then ∑ b : Fin k, X (τ, Sum.inr b) else ∑ a : Fin j, -X (τ, Sum.inl a)

def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))

def restInput : RootPoly f j k := smallMu f j k ^ (f * j * k + 1) * fibre f j k

def degreeInput : RootPoly f j k := smallMu f j k ^ (f * j * k) * fibre f j k

structure IsFlagIntegral (I : RootPoly f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : RootPoly f j k), 1 ≤ m → m ≤ flagDim f j k →
    G.IsHomogeneous (flagDim f j k - m) → I (rootPsum f j k m τ * G) = 0
  ne_zero : ∃ G : RootPoly f j k, G.IsHomogeneous (flagDim f j k) ∧ I G ≠ 0

def IsPowerSumDecomposition (F : RootPoly f j k) (Q : Fin f → ℕ → RootPoly f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (flagDim f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), rootPsum f j k m τ * Q τ m

def restAt (I : RootPoly f j k →ₗ[ℝ] ℝ) (vol : ℝ) (φ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → RootPoly f j k) (p : ℕ) : ℝ :=
  log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ,
    (((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m))

def primesAbove (P : Set ℕ) (B₀ : ℝ) : Type := {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}

def RestTerm.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f j k : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ k →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ (vol : ℝ), 0 < vol → ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) →
    ∀ (B₀ : ℝ), 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      (∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q) ∧
      ∀ Q, IsPowerSumDecomposition f j k (restInput f j k) Q →
        Summable (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) ∧
        |∑' p : primesAbove P B₀, restAt f j k I vol φ Q p.1| ≤
          C * (min j k : ℕ) * ((f * j * k : ℕ) + 1) * vol * |I (degreeInput f j k)|

def RestTermSharp.Statement : Prop :=
  ∀ (f j k : ℕ), 1 ≤ f → 1 ≤ j → 1 ≤ k →
    ∀ I : RootPoly f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ (vol : ℝ), 0 < vol → ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) →
    ∀ (B₀ : ℝ), 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ φ : ℕ → ℕ → Fin f → Fin f × Bool,
      (∃ Q, IsPowerSumDecomposition f j k (restInput f j k) Q) ∧
      ∀ Q, IsPowerSumDecomposition f j k (restInput f j k) Q →
        Summable (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) ∧
        |∑' p : primesAbove P B₀, restAt f j k I vol φ Q p.1| ≤
          1.6 * ((f * j * k : ℕ) + 1) * vol * |I (degreeInput f j k)|

def flagIntegralOne : RootPoly 1 1 1 →ₗ[ℝ] ℝ :=
  lcoeff ℝ (Finsupp.single (0, Sum.inl 0) 1) - lcoeff ℝ (Finsupp.single (0, Sum.inr 0) 1)

theorem isFlagIntegral_one : IsFlagIntegral 1 1 1 flagIntegralOne where
  kills := by
    intro m τ G h1 h2 _
    have hD : flagDim 1 1 1 = 1 := by decide
    have hm : m = 1 := by omega
    subst hm
    fin_cases τ
    simp [flagIntegralOne, rootPsum, Fintype.sum_sum_type, add_mul, coeff_X_mul']
  ne_zero := by
    refine ⟨X (0, Sum.inl 0), ?_, ?_⟩
    · have hD : flagDim 1 1 1 = 1 := by decide
      rw [hD]; exact isHomogeneous_X _ _
    · simp [flagIntegralOne, coeff_X, Finsupp.single_eq_single_iff]

example : (0 : ℝ) < 1 ∧ (∀ p ∈ {p : ℕ | p.Prime}, p.Prime) ∧
    4 * (1 : ℕ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 :=
  ⟨one_pos, fun _ h => h, by norm_num⟩

example : Antitone (![2, 1] : Fin 2 → ℕ) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all

end

end GroundTheory.Heights₂.Heights
end

