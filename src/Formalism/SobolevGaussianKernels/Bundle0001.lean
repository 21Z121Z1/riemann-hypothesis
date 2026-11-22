import Mathlib

-- bundled from Formalism.SobolevGaussianKernels.StatementCS
section
namespace Formalism.SL.CS

open Finset

def KernelBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → ι → ℝ) (w : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i j, P i j = P j i) → (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ j, P i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (P i j : ℂ) * w j‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)

def OrbitVanish : Prop :=
  ∀ (G S : Type) [Group G] [Fintype S] [MulAction G S] (f : S → ℂ) (χ : G →* ℂ),
    (∀ g s, f (g • s) = χ g * f s) → (∃ g, χ g ≠ 1) → ∑ s, f s = 0

def PowerSum : Prop :=
  ∀ (p N c : ℕ), p.Prime → 1 ≤ c → c ≤ N →
    ∑ t ∈ range (p ^ N), Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) / (p : ℂ) ^ c)) = 0

def CharExpandEq : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ),
    (Fintype.card T : ℂ) * ∑ u ∈ univ.filter (fun u => Q u = 0), χ u
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * χ u

def CharExpand : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ),
    ∑ u, χ u = 0 →
    ‖∑ u ∈ univ.filter (fun u => Q u = 0), χ u‖ ≤
      (1 / (Fintype.card T : ℝ)) * ∑ ψ ∈ univ.filter (fun ψ : AddChar T ℂ => ψ ≠ 0), ‖∑ u, ψ (Q u) * χ u‖

def SqSum : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (φ : A → ℂ),
    (∀ y, ‖φ y‖ = 1) →
    (∀ d, d ≠ 0 → ∃ (c : ℂ) (χ : AddChar A ℂ), (∃ y, χ y ≠ 1) ∧ ∀ y, φ (y + d) * star (φ y) = c * χ y) →
    ‖∑ y, φ y‖ ^ 2 = (Fintype.card A : ℝ)

def SqSumRad : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (φ : A → ℂ) (K : Finset A),
    (∀ y, ‖φ y‖ = 1) →
    (∀ d, d ∉ K → ∃ (c : ℂ) (χ : AddChar A ℂ), (∃ y, χ y ≠ 1) ∧ ∀ y, φ (y + d) * star (φ y) = c * χ y) →
    ‖∑ y, φ y‖ ^ 2 ≤ (Fintype.card A : ℝ) * (K.card : ℝ)

def KernelBoundRel : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → ι → ℝ) (w : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i j, P i j = P j i) →
    (∀ i, |(∑ j, P i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (P i j : ℂ) * w j‖ ≤ ε₂ * ‖w i‖) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * ∑ i, ‖w i‖

end Formalism.SL.CS
end

-- bundled from Formalism.SobolevGaussianKernels.StatementEI
section
namespace Formalism.SL.IwahoriBlocks

variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]

def IsHerm (h : V →ₗ[E] V →ₗ⋆[E] E) : Prop := ∀ v w, h w v = star (h v w)

def eich (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v : V) : V :=
  v + h v u • x - h v x • (u + s • x)

def EichIsom : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v w, h (eich h x u s v) (eich h x u s w) = h v w

def EichInv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v, eich h x (-u) (star s) (eich h x u s v) = v ∧ eich h x u s (eich h x (-u) (star s) v) = v

def EichComp : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x a b : V) (s t : E),
    IsHerm h → h x x = 0 → h a x = 0 → h b x = 0 →
    ∀ v, eich h x a s (eich h x b t v) = eich h x (a + b) (s + t + h b a) v

def EichShift : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s c : E),
    ∀ v, eich h x (u + c • x) s v = eich h x u (s + c - star c) v

def EichEquiv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (g : V →ₗ[E] V), (∀ v w, h (g v) (g w) = h v w) →
    ∀ (x u : V) (s : E) (v : V), g (eich h x u s v) = eich h (g x) (g u) s (g v)

def EichMove : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ v, h v x' = 0 →
      eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x)

def EichNew : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    (h u x = 0 → eich h x u s u = u + h u u • x) ∧
    (h x' u = 0 → eich h x u s x' = x' - h x' x • (u + s • x))

def EichPair : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ y z, h y x = 0 → h y u = 0 → h z x' = 0 →
      h y (eich h x u s (eich h x' u s z)) = h y z + star (h z u) * h y x'

def EichInt : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (x x' u : V) (s : E),
    IsHerm h →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    u ∈ abelian₂ → x + x' ∈ abelian₂ → s • x ∈ abelian₂ → h x' x ∈ O → h u x = 0 → h u x' = 0 →
    ∀ v ∈ abelian₂, h v x' = 0 → eich h x u s (eich h x' u s v) ∈ abelian₂

end Formalism.SL.IwahoriBlocks
end

-- bundled from Formalism.SobolevGaussianKernels.StatementLF
section
namespace Formalism.SL.LF

open scoped NumberField
open NumberField InfinitePlace Finset

def ProdBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K) (H : ℝ), x ≠ 0 → 1 ≤ H →
    (∀ w : InfinitePlace K, w (x : K) ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w (x : K))⁻¹) ^ w.mult ≤ H ^ Module.finrank ℚ K

def ProdBoundFrac : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K) (a : 𝓞 K) (H : ℝ), x ≠ 0 → a ≠ 0 → 1 ≤ H →
    (∃ y : 𝓞 K, (y : K) = (a : K) * x) →
    (∀ w : InfinitePlace K, w x ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w x)⁻¹) ^ w.mult
      ≤ H ^ Module.finrank ℚ K * |Algebra.norm ℚ (a : K)|

def ProdBoundIdeal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K) (I : Ideal (𝓞 K)) (H : ℝ), x ≠ 0 → I ≠ ⊥ → 1 ≤ H →
    (∀ y ∈ I, ∃ z : 𝓞 K, (z : K) = (y : K) * x) →
    (∀ w : InfinitePlace K, w x ≤ H) →
    ∏ w : InfinitePlace K, (max 1 (w x)⁻¹) ^ w.mult ≤ H ^ Module.finrank ℚ K * (Ideal.absNorm I : ℝ)

def ProdInv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : 𝓞 K), D ≠ 0 →
    ∏ w : InfinitePlace K, (max 1 (w (D : K))⁻¹) ^ w.mult
      ≤ ∏ w : InfinitePlace K, (max 1 (w (D : K))) ^ w.mult

def ProdRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : 𝓞 K), A ≠ 0 → B ≠ 0 →
    ∏ w : InfinitePlace K, (max 1 (w ((A : K) / (B : K)))) ^ w.mult
      ≤ ∏ w : InfinitePlace K, (max 1 (w (A : K)) * max 1 (w (B : K))) ^ w.mult

def BoxCount : Prop :=
  ∀ (f : ℕ) (S : Finset (Fin f → ℂ)) (y : Fin f → ℂ) (ρ : Fin f → ℝ),
    (∀ z ∈ S, ∀ v, ‖z v - y v‖ ≤ ρ v) →
    (∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → 1 ≤ ∏ v, ‖z v - z' v‖ ^ 2) →
    (S.card : ℝ) ≤ 16 ^ f * max 1 (∏ v, (2 * ρ v) ^ 2)

def BoxRing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], (∀ w : InfinitePlace K, w.IsComplex) →
    ∀ (y : InfinitePlace K → ℂ) (ρ : InfinitePlace K → ℝ),
      {x : 𝓞 K | ∀ w, ‖w.embedding (x : K) - y w‖ ≤ ρ w}.Finite ∧
      ({x : 𝓞 K | ∀ w, ‖w.embedding (x : K) - y w‖ ≤ ρ w}.ncard : ℝ)
        ≤ 16 ^ Fintype.card (InfinitePlace K) * max 1 (∏ w, (2 * ρ w) ^ 2)

def Sobolev1 : Prop :=
  ∀ (φ φ' : ℝ → ℂ) (a δ : ℝ), 0 < δ →
    (∀ t ∈ Set.Icc a (a + δ), HasDerivAt φ (φ' t) t) →
    ContinuousOn φ' (Set.Icc a (a + δ)) →
    ∀ x ∈ Set.Icc a (a + δ),
      ‖φ x‖ ^ 2 ≤ 2 / δ * ∫ t in a..(a + δ), (‖φ t‖ ^ 2 + δ ^ 2 * ‖φ' t‖ ^ 2)

def BinaryCode : Prop :=
  ∀ (k : ℕ) (v : Fin k → ℝ) (Δ : ℝ), 0 < Δ →
    Fintype.card (Fin k → Bool) = 2 ^ k ∧
    (∀ w w' : Fin k → Bool, w ≠ w' →
      (∃ i, |(v i - 1 / 2 - (if w i then Δ else 0)) - (v i - 1 / 2 - (if w' i then Δ else 0))| = Δ) ∧
      Δ ≤ ∑ i, |(v i - 1 / 2 - (if w i then Δ else 0)) - (v i - 1 / 2 - (if w' i then Δ else 0))|) ∧
    (∀ X : ℝ, Real.exp X ≤ 2 ^ k ↔ X ≤ k * Real.log 2)

def PrimesOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ), p.Prime →
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.Finite ∧
    {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P}.ncard ≤ Module.finrank ℚ K

end Formalism.SL.LF
end

-- bundled from Formalism.SobolevGaussianKernels.StatementMV
section
namespace Formalism.SL.MV

open Finset

noncomputable def kern {ι Mv : Type} [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (i j : ι) : ℝ :=
  ∑ m ∈ univ.filter (fun m => src m = i ∧ tgt m = j), μ m

def MoveKernel : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    ∀ i j, kern src tgt μ i j = kern src tgt μ j i

def MoveBound : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv)
    (w : ι → ℂ) (χ : Mv → ℂ) (ε₁ ε₂ : ℝ),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    (∀ m, w (tgt m) = w (src m) * χ m) →
    (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ m ∈ univ.filter (fun m => src m = i), μ m) - 1| ≤ ε₁) →
    (∀ i, ‖∑ m ∈ univ.filter (fun m => src m = i), (μ m : ℂ) * χ m‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)

end Formalism.SL.MV
end

-- bundled from Formalism.SobolevGaussianKernels.StatementNC
section
namespace Formalism.SL.NC

open Finset

def NormCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (c : K),
      |((univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = c)).card : ℝ)
          - (Fintype.card L : ℝ) ^ n / (Fintype.card K : ℝ)|
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

def NormCharMean : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (ψ : AddChar K ℂ), (∃ c, ψ c ≠ 1) →
    ∀ (n : ℕ) (ℓ : Fin n → L), ℓ ≠ 0 →
      ‖∑ y ∈ univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = 0),
          ψ (∑ i, Algebra.trace K L (ℓ i * y i))‖
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

end Formalism.SL.NC
end

-- bundled from Formalism.SobolevGaussianKernels.StatementSB
section
namespace Formalism.SL.SB

open MeasureTheory
open scoped ContDiff

noncomputable def pd {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun y => fderiv ℝ g y (Pi.single i 1)

noncomputable def mixed {n : ℕ} (α : Finset (Fin n)) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (α.sort (· ≤ ·)).foldr pd g

def cube {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (a i) (a i + δ))

def SobolevN : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (a : Fin n → ℝ) (δ : ℝ),
    ContDiff ℝ ∞ φ → 0 < δ →
    ∀ x ∈ cube a δ,
      ‖φ x‖ ^ 2 ≤ 2 ^ n / δ ^ n *
        ∫ y in cube a δ, (∑ α : Finset (Fin n), δ ^ (2 * α.card) * ‖mixed α φ y‖ ^ 2)

end Formalism.SL.SB
end

