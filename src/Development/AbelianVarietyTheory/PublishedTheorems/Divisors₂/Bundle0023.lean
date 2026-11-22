import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinFunctionalEquation
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE npow)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j : ℕ}

def IsEisCont (C : Matrix (Fin n) (Fin j) E) (h : GAd σ J → ℝ≥0) (φ : GAd σ J → ℂ) (Eis : ℂ → GAd σ J → ℂ) : Prop :=
  (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → ∀ g,
    GlobalTheory.Eis.CosetConv (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g ∧
    Eis s g = GlobalTheory.Eis.cosetSum (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g) ∧
  ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
    (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
    ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def Exchanges (C D : Matrix (Fin n) (Fin j) E) (w : GAd σ J) : Prop :=
  (∃ b : GL (Fin j) (AF F ⊗[F] E), (matHom _ σ J w).1 * adMat F C = adMat F D * b.1) ∧
  ∃ b : GL (Fin j) (AF F ⊗[F] E), (matHom _ σ J w).1 * adMat F D = adMat F C * b.1

end GlobalTheory.EisLine

namespace GlobalTheory.Published

def EisensteinFunctionalEquation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (j : ℕ) (hj : j ≤ r) (C D : Matrix (Fin n) (Fin j) E), C = X.submatrix id (Fin.castLE hj) →
        D = Y.submatrix id (Fin.castLE hj) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ≥0,
        (∀ (p : GAd σ J) (b : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * b.1 →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det b)) →
      ∀ w ∈ ratPts σ J, Exchanges σ J C D w →
      ∀ (μ : Measure (unipRad σ J C)) (𝓕 : Set (unipRad σ J C)), μ.IsHaarMeasure →
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J C)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ φ : GAd σ J → ℂ, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) φ →
      ∃ (m : ℕ) (ψ : Fin m → GAd σ J → ℂ) (c : Fin m → ℂ → ℂ) (σ₁ : ℝ),
        (∀ i, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) (ψ i)) ∧ (∀ i, MeromorphicOn (c i) Set.univ) ∧
        (∀ s : ℂ, σ₁ < s.re → ∀ g,
          Integrable (fun u : unipRad σ J C => φ (w * u * g) * npow (h (w * u * g)) s) μ ∧
          ∫ u : unipRad σ J C, φ (w * u * g) * npow (h (w * u * g)) s ∂μ = (∑ i, c i s * ψ i g) * npow (h g) (-s)) ∧
        ∀ (Eis : ℂ → GAd σ J → ℂ) (Es : Fin m → ℂ → GAd σ J → ℂ), IsEisCont σ J C h φ Eis →
          (∀ i, IsEisCont σ J C h (ψ i) (Es i)) →
          ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, ∀ g, Eis s g = ∑ i, c i s * Es i (-s) g

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreFiniteUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y.J.det ≠ 0 →
    Y₁.J.det ≠ 0 → ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    (∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
        FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})) →
    ∀ (h : UA σ Y.J) (g : UA σ Y₁.J → ℂ), (∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = ψ (m * h)) →
    ∀ φ₁ : GAd σ (c • Y₁.J.map σ) → ℂ, (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 → φ₁ g' = g g₁) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁})

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreInducedUnitary
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreInducedUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J →
    ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ χ : Chr F E, Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
    (∀ t m, IsLevi (W₁ := Y₁) H t 1 m → ∀ x, ψ (m * x) = (χ t : ℂ) * ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ →
    ∀ V : Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ), FiniteDimensional ℂ V → (∀ v ∈ V, GlobalTheory.UAut.IsSm σ (c • Y₁.J.map σ) v) →
      (∀ v ∈ V, ∀ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z → GlobalTheory.UAut.dop z v ∈ V) →
    ∀ Kc : Set (UA σ Y.J), (∀ x : UA σ Y.J, ∃ u ∈ unip σ Y H, ∃ t h₁ m, IsLevi (W₁ := Y₁) H t h₁ m ∧ ∃ k ∈ Kc, x = u * m * k) →
      (∀ k ∈ Kc, ∃ v ∈ V, ∀ (h₁ : UA σ Y₁.J) (m : UA σ Y.J) (g' : GAd σ (c • Y₁.J.map σ)),
        IsLevi (W₁ := Y₁) H 1 h₁ m → h₁.1 = g'.1 → v g' = ψ (m * k)) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})

end GlobalTheory.Published

end
end

