import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsElemDiv {v : HeightOneSpectrum (𝓞 F)} (x : GL (Fin n) (Fv F v)) (d : Fin n → (Fv F v)ˣ) : Prop :=
  ∃ k₁ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
    ∃ k₂ ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring,
      x.1 = k₁.1 * Matrix.diagonal (fun i => (d i : Fv F v)) * k₂.1

def IsInertUnder (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  (v : HeightOneSpectrum (𝓞 F))

def latMoved (g : GLoc σ J v) : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
  (latLoc F L v).comap ((Matrix.mulVecLin (matHom (Fv F v) σ J g⁻¹).1).restrictScalars (intLoc F E v))

def latLength (g : GLoc σ J v) : ℕ∞ :=
  Module.length (intLoc F E v)
    (latLoc F L v ⧸ (latLoc F L v ⊓ latMoved σ J L v g).submoduleOf (latLoc F L v))

def graphHgt (g : GLoc σ J v) : ℝ≥0 :=
  hgtFin σ (dblGram finSumFinEquiv J) L v (ioH (Fv F v) σ rfl (g, 1))

def SplitAt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : Prop :=
  ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ g : GLoc σ J v,
    (∃ d, IsElemDiv (splitEquivIn h hJ τ β g) d) ∧
    (∀ d, IsElemDiv (splitEquivIn h hJ τ β g) d →
      graphHgt σ J L v g = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹) ∧
    graphHgt σ J L v g ≤ 1

def InertAt : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v,
    (∃ l : ℕ, latLength σ J L v g = l ∧
      graphHgt σ J L v g = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ))) ∧
    graphHgt σ J L v g ≤ 1

def GraphNormFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)),
    IsSelfDualAt σ J L v → SplitAt σ J L v h hJ ∧ InertAt σ J L v

omit [NumberField E] in
theorem mem_latMoved {g : GLoc σ J v} {x : Fin n → Fv F v ⊗[F] E} :
    x ∈ latMoved σ J L v g ↔ (matHom (Fv F v) σ J g⁻¹).1 *ᵥ x ∈ latLoc F L v := Iff.rfl

omit [NumberField E] in

example : latLength σ J L v 1 = 0 := by
  rw [latLength, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  refine ⟨x.2, (mem_latMoved σ J L v).2 ?_⟩
  simp

example (x : GL (Fin n) (Fv F v)) (d : Fin n → (Fv F v)ˣ) (hx : x.1 = Matrix.diagonal fun i => (d i : Fv F v)) :
    IsElemDiv x d := ⟨1, one_mem _, 1, one_mem _, by simp [hx]⟩

example [Submodule.IsLattice E L] : graphHgt σ J L v 1 = 1 := by
  have : ((1 : GLoc σ J v), (1 : GLoc σ J v)) = 1 := rfl
  rw [graphHgt, this, map_one]
  exact hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) (one_mem _)

end GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def signMat : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if ε i then 1 else -1

def IsInU (g : Matrix (Fin n) (Fin n) ℂ) : Prop := gᴴ * signMat ε * g = signMat ε

def IsInK (k : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ i j, ε i ≠ ε j → k i j = 0

def IsInP (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X.IsHermitian ∧ ∀ i j, ε i = ε j → X i j = 0

def realRank : ℕ := min (Fintype.card {i // ε i = true}) (Fintype.card {i // ε i = false})

def offBlock (X : Matrix (Fin n) (Fin n) ℂ) : Matrix {i // ε i = true} {i // ε i = false} ℂ :=
  Matrix.of fun i j => X i.1 j.1

def singVal (X : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin (offBlock ε X) :
    EuclideanSpace ℂ {i // ε i = false} →ₗ[ℂ] EuclideanSpace ℂ {i // ε i = true}).singularValues i

def coshProd (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∏ i ∈ Finset.range (realRank ε), Real.cosh (singVal ε X i)

def IsCartan (g X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsInP ε X ∧ ∃ k₁ k₂, IsInK ε k₁ ∧ IsInK ε k₂ ∧ g = k₁ * NormedSpace.exp X * k₂

theorem one_le_coshProd (X : Matrix (Fin n) (Fin n) ℂ) : 1 ≤ coshProd ε X :=
  Finset.prod_induction _ (fun r => 1 ≤ r) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl
    fun _ _ => Real.one_le_cosh _

example : IsInP ![true, false] !![0, 1; 1, 0] ∧ realRank ![true, false] = 1 := by
  refine ⟨⟨?_, fun i j h => ?_⟩, by decide⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · fin_cases i <;> fin_cases j <;> simp_all

end Matrices

def GramDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), IsInU ε g →
    (∃ X, IsCartan ε g X) ∧
    ∀ X, IsCartan ε g X → ((2 : ℂ)⁻¹ • (1 + g * gᴴ)).det = ((coshProd ε X ^ 2 : ℝ) : ℂ)

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

example : IsSignFrame σ (1 : Matrix (Fin n) (Fin n) E) (w := w) (fun _ => true) 1 := by
  simp [IsSignFrame, JR, cT_one]

end Place

def DoubledAbs : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (h : Q = dblGram finSumFinEquiv J)
      (w : InfinitePlace F) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)),
      IsSignFrame σ J ε b → ∀ g : GArch σ J w,
      (∃ p : siegelH w.Completion σ Q, ∃ k ∈ KArch σ Q w b, ioH w.Completion σ h (g, 1) = p * k) ∧
      hgtArch σ Q w b (ioH w.Completion σ h (g, 1)) ≤ 1 ∧
      (∃ X, IsCartan ε (inFrame σ J τ b g) X) ∧
      ∀ X, IsCartan ε (inFrame σ J τ b g) X →
        (hgtArch σ Q w b (ioH w.Completion σ h (g, 1)) : ℝ) = (coshProd ε X ^ 2)⁻¹ ∧
        (∀ (p : siegelH w.Completion σ Q), ∀ k ∈ KArch σ Q w b, ioH w.Completion σ h (g, 1) = p * k →
          ‖infEmb τ (aH w.Completion σ Q p).1‖ = (coshProd ε X)⁻¹) ∧
        ∀ (μ : (w.Completion ⊗[F] E)ˣ →* Circle) (s₀ s : ℂ) (Φ : GArch σ Q w → ℂ), Φ ∈ degPSArch σ Q w b μ s₀ →
          ∀ C : ℝ, (∀ k ∈ KArch σ Q w b, ‖Φ k‖ ≤ C) →
            ‖flatArch σ Q w b Φ s₀ s (ioH w.Completion σ h (g, 1))‖ ≤ C * coshProd ε X ^ (-(2 * s.re + (n : ℝ)))

def RealDoublingNorm : Prop := GramDet ∧ DoubledAbs

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end
end

