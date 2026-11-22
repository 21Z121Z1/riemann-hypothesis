import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ

open Classical in

structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

example : dualPar (GlobalTheory.Chain.signed [2] [-3] (1 / 2)) = {(-5 / 2, true), (5 / 2, false)} := by
  simp [dualPar, GlobalTheory.Chain.signed]
  norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

def IsIsoBilin (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ x x' y y', ⟪Tm x y, Tm x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ

def IsEquivBilin {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ g h x y, Tm (π₁ g x) (π₂ h y) = ρ (g, h) (Tm x y)

def IsContr (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop :=
  ∀ φ y x, ⟪x, It φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ

def HasWeakDer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : ℝ → H) (v' : H) : Prop :=
  ∀ w : H, HasDerivAt (fun t : ℝ => ⟪w, c t⟫_ℂ) ⟪w, v'⟫_ℂ 0

def IsFiniteVec {G H : Type} [Group G] [AddCommGroup H] [Module ℂ H] (K : Subgroup G) (π : G → H → H) (v : H) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π k v))

def imSpan (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Submodule ℂ FF :=
  Submodule.span ℂ (Set.range fun p : H₁ × H₂ => Tm p.1 p.2)

structure ContrProps {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁))
    (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)) (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF)
    (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop where

  norm_le : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖

  equiv : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y)

  inv : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y

  der₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasDerivAt (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' 0 →
      HasDerivAt (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y) 0

  weakDer₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasWeakDer (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' →
      HasWeakDer (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y)

  der₂ : ∀ (c : Multiplicative ℝ →* G₂) φ φ' y y',
    HasWeakDer (fun t : ℝ => ρ (1, c (Multiplicative.ofAdd t)) φ) φ' →
      HasWeakDer (fun t : ℝ => π₂ (c (Multiplicative.ofAdd t)) y) y' → It φ' y + It φ y' = 0

  ne : ∀ φ, φ ∉ (imSpan Tm)ᗮ → ∀ Y : Set H₂, Dense Y → ∃ y ∈ Y, It φ y ≠ 0

  fin : ∀ (K : Subgroup G₁) φ y, IsFiniteVec K (fun g => ρ (g, 1)) φ → IsFiniteVec K (fun g => π₁ g) (It φ y)

end Hilbert

def ContrHilbert : Prop :=
  ∀ (H₁ H₂ FF : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]
    (G₁ G₂ : Type) [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF),
    IsIsoBilin Tm → IsEquivBilin π₁ π₂ ρ Tm →
      (∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It) ∧
      ∀ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It → ContrProps π₁ π₂ ρ Tm It

def IsTensorIt {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var) {A B : ι → Type}
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ)
    (It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ) : Prop :=
  ∀ (P : ∀ τ, MvPolynomial (σ τ) ℂ) (v : ∀ τ, A τ),
    It (∏ τ, MvPolynomial.rename (fun s => e ⟨τ, s⟩) (P τ)) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)

def ContrTensor : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : ι → Type) (Var : Type) (e : (Σ τ, σ τ) ≃ Var) (A B : ι → Type)
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ),
    ∃ It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ,
      IsTensorIt e Itl It ∧ ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

def Contraction : Prop := ContrHilbert ∧ ContrTensor

section Models

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContrTensorModels : Prop :=
  ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (Itl : ∀ τ, MvPolynomial (Fin W.rank × Fin V.rank) ℂ →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ),
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      (∀ (P : D.what₂.Tau → MvPolynomial (Fin W.rank × Fin V.rank) ℂ) (v : M'.Vec),
        It (∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)) (PiTensorProduct.tprod ℂ v) =
          PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)) ∧
      ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

theorem contrTensorModels_of (h : ContrTensor) : ContrTensorModels := fun D V W _ _ M M' Itl =>
  h D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) _ (Equiv.sigmaEquivProd _ _) (fun τ => M'.sm τ)
    (fun τ => M.sm τ) Itl

end Models

example (a b x y : ℂ) : LinearMap.mul ℂ ℂ (a * x) (b * y) = (a * b) * LinearMap.mul ℂ ℂ x y := by
  simp only [LinearMap.mul_apply']; ring

example (It : ℂ →ₗ[ℂ] ℂ →ₛₗ[starRingEnd ℂ] ℂ) (h : IsContr (LinearMap.mul ℂ ℂ) It) (φ y : ℂ) :
    It φ y = φ * starRingEnd ℂ y := by
  have := h φ y 1
  simpa using this

theorem contrProps_of {H₁ H₂ FF : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)} {π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)}
    {ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)} {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm)
    (hE : IsEquivBilin π₁ π₂ ρ Tm) {It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁} (hC : IsContr Tm It) :
    ContrProps π₁ π₂ ρ Tm It := by
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hb : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖ := by
    intro φ y
    have h := hC φ y (It φ y)
    have h1 : ‖It φ y‖ * ‖It φ y‖ ≤ ‖It φ y‖ * (‖φ‖ * ‖y‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm (It φ y) y) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (It φ y)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  have hall : ∀ g h φ y, It (ρ (g, h) φ) (π₂ h y) = π₁ g (It φ y) := by
    intro g h φ y
    apply ext_inner_left ℂ
    intro x
    obtain ⟨x, rfl⟩ := (π₁ g).surjective x
    rw [hC, hE, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, hC]
  have he : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y) := fun g φ y => by simpa using hall g 1 φ y
  have hi : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y := fun h φ y => by simpa using hall 1 h φ y
  refine ⟨hb, he, hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro c φ φ' y hd
    let L : FF →L[ℂ] H₁ := (It.flip y).mkContinuous ‖y‖ fun φ => by simpa [mul_comm] using hb φ y
    have := ((L.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hd
    simpa [L, Function.comp_def, he] using this
  · intro c φ φ' y hd w
    simpa only [← he, hC _ _ _] using hd (Tm w y)
  · intro c φ φ' y y' hd hd'
    apply ext_inner_left ℂ
    intro x
    let ℓ : H₂ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm x).mkContinuous (‖φ‖ * ‖x‖) fun y => by
      simpa [hn, mul_assoc] using norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₂).surjective ℓ
    have hw' : ∀ z, ⟪w, z⟫_ℂ = ⟪φ, Tm x z⟫_ℂ := fun z => by
      have := congrArg (fun f : H₂ →L[ℂ] ℂ => f z) hw
      simpa [ℓ] using this
    have h1 := hd (Tm x y)
    have h2 := ((hd' w).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)).star
    have h3 : (fun t : ℝ => ⟪Tm x y, ρ (1, c (Multiplicative.ofAdd t)) φ⟫_ℂ) =
        fun t : ℝ => star (((fun t : ℝ => ⟪w, π₂ (c (Multiplicative.ofAdd t)) y⟫_ℂ) ∘ Neg.neg) t) := by
      funext t
      have hy : y = π₂ (c (Multiplicative.ofAdd t)) (π₂ (c (Multiplicative.ofAdd (-t))) y) := by
        change y = (π₂ _ * π₂ _) y
        rw [← map_mul, ← map_mul, ← ofAdd_add]; simp
      simp only [Function.comp, hw']
      rw [← hC, Complex.star_def, inner_conj_symm, ← hC]
      conv_lhs => rw [hy, hi]
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [inner_add_right, hC, hC, h4, hw']
    simp
  · intro φ hφ Y hY
    by_contra hcon
    push_neg at hcon
    apply hφ
    let L : H₂ →SL[starRingEnd ℂ] H₁ := (It φ).mkContinuous ‖φ‖ (hb φ)
    have h0 : ∀ y, It φ y = 0 := fun y =>
      congrFun (Continuous.ext_on hY L.continuous (continuous_const (y := (0 : H₁))) hcon) y
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨p, rfl⟩ := hu; simp [← hC φ, h0]
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul a b _ hb => simp [inner_smul_left, hb]
  · intro K φ y hf
    unfold IsFiniteVec at *
    have : (Set.range fun k : K => π₁ k (It φ y)) = It.flip y '' Set.range fun k : K => ρ (k, 1) φ := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance

def contrMul : ℂ →ₗ[ℂ] ℂ →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun φ y => φ * starRingEnd ℂ y)
    (fun a b y => by ring) (fun c a y => by simp [mul_assoc]) (fun a y z => by simp [mul_add])
    (fun c a y => by simp; ring)

def circ : Circle →* (ℂ ≃ₗᵢ[ℂ] ℂ) where
  toFun a := { LinearEquiv.smulOfNeZero ℂ ℂ (a : ℂ) a.coe_ne_zero with norm_map' := fun z => by simp [Circle.norm_coe a] }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteUnitaryAction
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def classSumAt (f f' : S.Forms) : ℂ :=
  ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ ((f : S.Cl → S.V) c) ((f' : S.Cl → S.V) c)

def IsUnitaryAt {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (g : G) (f f' : S.Forms), classSumAt S σ (r g f) (r g f') = classSumAt S σ f f'

theorem wt_ne_zero (c : S.Cl) : (S.wt c : ℂ) ≠ 0 := by
  have : 0 < S.wt c := Fintype.card_pos
  exact_mod_cast this.ne'

theorem pairAt_smul_left (a : K) (x y : S.V) : pairAt S σ (a • x) y = starRingEnd ℂ (σ a) * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) : pairAt S σ x (a • y) = σ a * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pairAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) : pairAt S σ x y = σ (S.pair x y) := by
  have e : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply, CSD.gramV, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  simp only [pairAt, map_sum, map_mul, h]

theorem classSumAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (f f' : S.Forms) :
    classSumAt S σ f f' = σ (S.csum f f') := by
  simp only [classSumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, pairAt_eq S σ h]

theorem isUnitaryAt_iff (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {G : Type} [Group G] (r : Representation K G S.Forms) :
    IsUnitaryAt S σ r ↔ ∀ (g : G) (f f' : S.Forms),
      S.csum (r g f : S.Cl → S.V) (r g f' : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (f' : S.Cl → S.V) := by
  simp only [IsUnitaryAt, classSumAt_eq S σ h, σ.injective.eq_iff]

end ClassSum

section Statement

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

structure DefiniteUnitary (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop where

  what₂ : ∀ (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtildeCSD t) σ (A.leftGroupActionRight t)

  lifts : ∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtCSD i t) σ (A.leftGroupActionLift i t)

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ActsUnitarily (R : RealDat D A Ks) : Prop where

  what₂ : IsUnitaryRep R.gE

  formsW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

  definite : DefiniteUnitary A

def UnitaryOfChar (R : RealDat D A Ks) (F : Face D A) : Prop := R.Char F → ActsUnitarily R

end Statement

def UnitaryAction : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), UnitaryOfChar R F

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem IsUnitaryRep.tw {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Representation ℂ G H}
    (h : IsUnitaryRep ρ) (s : Bool) : IsUnitaryRep (Tw.rep s ρ) := fun g x y =>
  congrArg (cj s) (h g (Tw.out x) (Tw.out y))

theorem DefiniteUnitary.csum (h : DefiniteUnitary A) :
    (∀ t g (f f' : (A.MtildeCSD t).Forms), (A.MtildeCSD t).csum (A.leftGroupActionRight t g f : _ → _) (A.leftGroupActionRight t g f' : _ → _) =
      (A.MtildeCSD t).csum (f : _ → _) (f' : _ → _)) ∧
    ∀ i t g (f f' : (A.MtCSD i t).Forms), (A.MtCSD i t).csum (A.leftGroupActionLift i t g f : _ → _) (A.leftGroupActionLift i t g f' : _ → _) =
      (A.MtCSD i t).csum (f : _ → _) (f' : _ → _) :=
  ⟨fun t => (isUnitaryAt_iff _ _ D.starLL_cx _).1 (h.what₂ t _), fun i t => (isUnitaryAt_iff _ _ D.starLL_cx _).1 (h.lifts i t _)⟩

theorem rows_iff (R : RealDat D A Ks) (F : Face D A) (h : R.Char F) :
    IsUnitaryRep R.gE ↔ ∀ (g : G), ∀ x ∈ R.EEat R.triv, ∀ y ∈ R.EEat R.triv,
      Formalism.IndefR.Mult.ipM (R.MY 0) R.ν0 R.fd0
                (Formalism.IndefR.Mult.postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) x)
                (Formalism.IndefR.Mult.postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) y) =
        Formalism.IndefR.Mult.ipM (R.MY 0) R.ν0 R.fd0 x y := by
  obtain ⟨-, hr, hip⟩ := h.models.HE
  constructor
  · intro hu g x hx y hy
    rw [← hr] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    rw [← h.models.gE, ← h.models.gE, ← hip, ← hip, hu]
  · intro hu g x y
    rw [hip, hip, h.models.gE, h.models.gE]
    exact hu g _ (hr ▸ LinearMap.mem_range_self _ x) _ (hr ▸ LinearMap.mem_range_self _ y)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def signCard (S : SPar) (b : Bool) : ℕ := (S.filter fun x => x.2 = b).card

def SigLowered (S : D.what₂.Tau → SPar) (i : ℕ) (V' : HSp D) : Prop :=
  ∀ τ, ∃ p' q' : ℕ, p' + i = signCard (S τ) true ∧ q' + i = signCard (S τ) false ∧
    Formalism.UG.HasSignature (gramAt D V' τ) p' q'

def LowVanish (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def LowVanishConv (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → ∀ g, IntegrableOn (fun h => thetaKO ω' g h f' * F v h) 𝓕 ν ∧
        ∫ h in 𝓕, thetaKO ω' g h f' * F v h ∂ν = 0

theorem signCard_dualPar (S : SPar) (b : Bool) : signCard (dualPar S) b = signCard S b := by
  unfold signCard dualPar
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro x y h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

example : signCard {((5 : ℚ), true), (3, false), (-4, true)} true = 2 := by decide +kernel

end GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

end
end

