import ReciprocityTheory.SemistableReduction.SemiDegG
import ReciprocityTheory.SemistableReduction.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IndependentSectionsUpperCount

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegT
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def matLin {K : Type} [Field K] [NumberField K] {r : ℕ} (Q : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) →ₗ[𝓞 K] (Fin r → K) :=
  (Matrix.mulVecLin Q).restrictScalars (𝓞 K)

theorem matLin_apply {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (x : Fin r → K) : matLin Q x = Q *ᵥ x := rfl

theorem matLin_injective {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) : Function.Injective (matLin Q) := by
  intro x y hxy
  rw [matLin_apply, matLin_apply] at hxy
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hxy

theorem span_mulVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) :
    Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i) =
      (Submodule.span (𝓞 K) (Set.range b)).map (matLin Q) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem latDeg_transport {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) :
    latDeg (fun σ => (Q.map σ)ᴴ * D σ * Q.map σ) B b =
      latDeg D (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  unfold latDeg
  have hinj : Function.Injective (matLin Q) := matLin_injective Q hQ
  have h1 : (Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i)).toAddSubgroup.relIndex
      (B.map (matLin Q)).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [span_mulVec, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hemb : ∀ (σ : K →+* ℂ) (x : Fin r → K), embVec σ (Q *ᵥ x) = Q.map σ *ᵥ embVec σ x := by
    intro σ x
    funext a
    exact RingHom.map_mulVec σ Q x a
  have h2 : ∀ σ : K →+* ℂ, gramC ((Q.map σ)ᴴ * D σ * Q.map σ) σ b = gramC (D σ) σ (fun i => Q *ᵥ b i) := by
    intro σ
    ext i j
    simp only [gramC, Matrix.of_apply, hemb]
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [h2]

theorem kBasisIn_map {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hb : IsKBasisIn B b) :
    IsKBasisIn (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  obtain ⟨h1, h2, h3⟩ := hb
  have hinj : Function.Injective (Matrix.mulVecLin Q) := fun x y h => matLin_injective Q hQ h
  refine ⟨fun i => ⟨b i, h1 i, rfl⟩, ?_, ?_⟩
  · have e : (fun i => Q *ᵥ b i) = (Matrix.mulVecLin Q) ∘ b := rfl
    rw [e]
    exact h2.map' _ (LinearMap.ker_eq_bot.2 hinj)
  · rintro x ⟨y, hy, rfl⟩
    have h4 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin Q) (h3 y hy)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

def formM {K : Type} [Field K] {r : ℕ} (c : K →+* K) (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) : K :=
  (fun a => c (x a)) ⬝ᵥ (M *ᵥ y)

theorem hermForm_h_eq {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by
  unfold HermForm.h formM
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem formM_change {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    formM S.c ((P.map S.c)ᵀ * S.G * P) x y = S.h (P *ᵥ x) (P *ᵥ y) := by
  rw [hermForm_h_eq]
  unfold formM
  have e1 : (fun a => S.c ((P *ᵥ x) a)) = (P.map S.c) *ᵥ (fun a => S.c (x a)) := by
    funext a
    exact RingHom.map_mulVec S.c P x a
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem formM_witt {K : Type} [Field K] {r : ℕ} (c : K →+* K) (m : ℕ) (g : Fin r → K)
    (x y : Fin r → K) :
    formM c (wittMat r m g) x y = ∑ a, c (x a) * (wVal r m g a * y (wPart r m a)) := by
  unfold formM
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  have ha := a.isLt
  by_cases h : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m
  · have hw : wVal r m g a = 1 := if_pos h
    have hp : wPart r m a = Fin.rev a := if_pos h
    rw [hw, hp, one_mul, Finset.sum_eq_single (Fin.rev a)]
    · rw [wittMat, Matrix.of_apply, if_pos, one_mul]
      rw [Fin.val_rev]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, h2, h3⟩
        omega
      · rintro ⟨h1, -⟩
        apply hj
        ext
        rw [Fin.val_rev]
        omega
    · simp
  · have hw : wVal r m g a = g a := if_neg h
    have hp : wPart r m a = a := if_neg h
    rw [hw, hp, Finset.sum_eq_single a]
    · rw [wittMat, Matrix.of_apply, if_neg, if_pos ⟨rfl, by omega, by omega⟩]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, -⟩
        exact hj rfl
      · have hj' := j.isLt
        omega
    · simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ShareSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder

def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))

def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k

def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u

def NearMaj {K : Type} [Field K] [NumberField K] {r : ℕ} {S : HermForm K r}
    (M0 M : Majorant S) (c : ℝ) : Prop :=
  ∀ (σ : K →+* ℂ) (u : Fin r → ℂ),
    hq (M.H σ) u ≤ c * hq (M0.H σ) u ∧ hq (M0.H σ) u ≤ c * hq (M.H σ) u

def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0

def BallTrivialStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (M0 M1 M2 : Majorant S) (γ : Matrix (Fin r) (Fin r) K),
    NoContraction M0.H L → NearMaj M0 M1 (ballRatio r) → NearMaj M0 M2 (ballRatio r) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), hq (M2.H σ) (γ.map σ *ᵥ u) = hq (M1.H σ) u) →
    (∀ x ∈ L, γ *ᵥ x ∈ L) →
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) → 3 * r < g →
    γ = 1

def orbitMat {U Z : Type} [Group U] [MulAction U Z] (u0 : Z → ℂ) (z : Z) : Matrix U U ℂ :=
  Matrix.of fun a b => u0 ((a * b) • z)

def MonomialDetStatement : Prop :=
  ∀ (U : Type) [Group U] [Fintype U] [DecidableEq U] (Z : Type) [MulAction U Z]
    (u0 : Z → ℂ) (z0 : Z),
    u0 z0 ≠ 0 → (∀ a : U, a ≠ 1 → u0 (a • z0) = 0) →
    ∀ h : U, (orbitMat (U := U) u0 (h • z0)).det ≠ 0

def ZeroByDetStatement : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (U : Type) [Fintype U] [DecidableEq U]
    (la la' : La) (M : U → U → ι → Y → ℂ) (x : ι → Y → ℂ),
    (∀ a b, A.IsSec la (M a b)) → A.IsSec la' x →
    (∀ y, ∃ y' ∈ connectedComponent y,
      (Matrix.of fun a b => M a b (A.pick y') y').det ≠ 0) →
    (∀ y, (Matrix.of fun a b => M a b (A.pick y) y).det ≠ 0 → x (A.pick y) y = 0) →
    ∀ j y, y ∈ (A.chart j).source → x j y = 0

def CountStatement : Prop :=
  ∀ (V W R R' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup R] [Module ℂ R] [AddCommGroup R'] [Module ℂ R'] (U : Type) [Fintype U]
    (m d0 : ℕ) (g : Fin m → V) (res : V →ₗ[ℂ] R) (resW : W →ₗ[ℂ] R')
    (Φ : V →ₗ[ℂ] (U → W)) (Wψ : Submodule ℂ W),
    LinearIndependent ℂ (res ∘ g) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), ∀ h, Φ v h ∈ Wψ) →
    (∀ v ∈ Submodule.span ℂ (Set.range g), (∀ h, resW (Φ v h) = 0) → res v = 0) →
    (∀ (k : ℕ) (f : Fin k → W), (∀ i, f i ∈ Wψ) → LinearIndependent ℂ (resW ∘ f) → k ≤ d0) →
    m ≤ Fintype.card U * d0

def psiPart {K U V : Type} [Field K] [Monoid U] [AddCommGroup V] [Module K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) : Submodule K V :=
  ⨅ u : U, LinearMap.ker (ρ u - ((χ u : Kˣ) : K) • LinearMap.id)

def psiPartBC {K L U V : Type} [Field K] [Field L] [Algebra K L] [Monoid U] [AddCommGroup V]
    [Module K V] (ρ : Representation K U V) (χ : U →* Kˣ) :
    Submodule L (TensorProduct K L V) :=
  ⨅ u : U, LinearMap.ker ((ρ u).baseChange L - algebraMap K L ((χ u : Kˣ) : K) • LinearMap.id)

def FreePsiStatement : Prop :=
  ∀ (K : Type) [Field K] (U : Type) [Group U] [Fintype U] [DecidableEq U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ) (W0 : Submodule K V),
    DirectSum.IsInternal (fun u : U => W0.map (ρ u)) →
    Fintype.card U * finrank K (psiPart ρ χ) = finrank K V

def PsiBaseChangeStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (U : Type) [Group U] [Fintype U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K U V) (χ : U →* Kˣ),
    finrank L (psiPartBC (L := L) ρ χ) = finrank K (psiPart ρ χ)

def ShareNumbersStatement : Prop :=
  ∀ (D T P f k : ℕ), 6 ≤ D → P ^ 3 * D ^ 3 * k * f ≤ T → f * k ≤ P → 2 ≤ f * k →
    ((D * (D + 6) : ℕ) : ℝ) / T ≤ 1 / (4 * ((f * k : ℕ) : ℝ) ^ 3)

end ReciprocityTheory.MultiplicativeHeights
end
end

