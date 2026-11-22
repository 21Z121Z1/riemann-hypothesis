import Formalism.RankGapBounds.Bundle0002
import Formalism.RankGapBounds.Bundle0001
import Mathlib
import Formalism.SatakeDualWeyl.Statement

-- bundled from Formalism.RankGapBounds.GridNumericalHypotheses
section
namespace Formalism.RankGapBounds.V4

open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer

def RankGapPrintedLemma : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def ConjInOrbitAll : Prop :=
  ∀ (e : ℕ) (φ : GG e), cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e

def RankGapDecayHypothesis : Prop :=
  ∀ n m γ : ℝ, 3 ≤ n → 1 ≤ m → m ≤ n → n ^ 7 ≤ γ →
    120 * n * (m / 2) ^ ((3 : ℝ) / 2) ≤ γ

structure GridNumericalHypotheses (k m t r : ℕ) (h₀ : ℝ) : Prop where
  k_even : Even k
  m_even : Even m
  m_pos : 1 ≤ m
  r_def : r + 1 = k + m
  k_ge : m + 3 ≤ k
  t_odd : Odd t
  t_gt_m : 3 * m < t
  t_gt_r : r + 4 < t
  h₀_big : (t : ℝ) + 2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < h₀

def RankGapBoundPair : Prop :=
  ∀ (k m t r : ℕ) (h₀ γ : ℝ), GridNumericalHypotheses k m t r h₀ →
    2 * ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 + 2 * ((r + 6 : ℕ) : ℝ) + 2 < γ →
    (∀ i j : ℕ, i ≤ m → j ≤ m → r + j * t + i * (r + 6) < k + m * (t + (r + 6) + 1)) ∧
    (∀ i : ℕ, i ≤ m → (r + 1) + i * (r + 5) < k + m * (t + (r + 6) + 1)) ∧
    (∀ M : ℕ, M < k + m * (t + (r + 6) + 1) →
      (M : ℝ) ^ 3 < (h₀ - t) / 2 ∧ (M : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ)) ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < (h₀ - t) / 2 ∧
    ((k + m * (t + (r + 6) + 1) : ℕ) : ℝ) ^ 3 < γ / 2 - ((r + 6 : ℕ) : ℝ) ∧
    (((r + 6 : ℕ) : ℝ) + 1) / 2 ≤ γ / 2 - 1 ∧ ((r + 6 : ℕ) : ℝ) / 2 ≤ γ / 2 - 1 ∧
    γ / 2 - ((r + 6 : ℕ) : ℝ) ≤ γ / 2 - 1 - (((r + 6 : ℕ) : ℝ) - 1) / 2

end Formalism.RankGapBounds.V4
end

-- bundled from Formalism.RankGapBounds.TheoremALocOfLemmaA
section
noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

def LatIncl {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  ∀ x : A, l ^ e • x ∈ B

def tensSub {k : Type} [CommRing k] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) : Submodule k (⨂[k] i, A i) :=
  LinearMap.range (PiTensorProduct.map fun i => (B i).subtype)

def formsIn {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρK : Representation k K W) (U : Submodule k W) :
    Submodule k (G → W) :=
  AMFK k Γ K ρK ⊓ Submodule.pi Set.univ (fun _ => U)

def IsStable {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] {K : Subgroup G} (ρK : Representation k K W) (U : Submodule k W) : Prop :=
  ∀ κ : K, ∀ x ∈ U, ρK κ x ∈ U

def resRep {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] {K : Subgroup G} (ρK : Representation k K W) (U : Submodule k W)
    (hU : IsStable ρK U) : Representation k K U where
  toFun κ := (ρK κ).restrict (hU κ)
  map_one' := by ext x; simp
  map_mul' κ κ' := by ext x; simp [map_mul]

def locSet {T : Type} [CommRing T] {M : Type} [AddCommGroup M] [Module T M]
    (S : Submonoid T) (N : Set M) : Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}

def LemmaA {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  LatIncl l B e

def TensorStep : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) (l : k) (e : ι → ℕ),
    (∀ i, LatIncl l (B i) (e i)) → ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B

def FunctStep : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type)
    [AddCommGroup W] [Module k W] (ρK : Representation k K W) (U V : Submodule k W) (l : k)
    (e : ℕ), (∀ x ∈ V, l ^ e • x ∈ U) → ∀ f ∈ formsIn Γ K ρK V, l ^ e • f ∈ formsIn Γ K ρK U

def FormsInEquiv : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type)
    [AddCommGroup W] [Module k W] (ρK : Representation k K W) (U : Submodule k W)
    (hU : IsStable ρK U),
    ∃ e : AMFK k Γ K (resRep ρK U hU) ≃ₗ[k] formsIn Γ K ρK U,
      ∀ f g, (e f : G → W) g = ((f : G → U) g : W)

def HeckeValStep : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (k : Type) [CommRing k]
    (W : Type) [AddCommGroup W] [Module k W] (U : Submodule k W) (f : G₁ → k)
    (φ : G₁ × G₂ → W), (∀ g, φ g ∈ U) → ∀ g, hActK K₁ f φ g ∈ U

def LocStep : Prop :=
  ∀ (T : Type) [CommRing T] (M : Type) [AddCommGroup M] [Module T M] (S : Submonoid T)
    (N : Set M) (t : T) (e : ℕ), (∀ x : M, t ^ e • x ∈ N) →
    ∀ y : LocalizedModule S M, t ^ e • y ∈ locSet S N

def TheoremA_of_LemmaA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k) (e : ι → ℕ),
    (∀ i, LemmaA l (B i) (e i)) →
    ∀ f ∈ AMFK k Γ K ρK, l ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (tensSub B)

def TheoremA_loc_of_LemmaA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k) (e : ι → ℕ)
    (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ρK)]
    [IsScalarTower k T (AMFK k Γ K ρK)] (S : Submonoid T),
    (∀ i, LemmaA l (B i) (e i)) →
    ∀ y : LocalizedModule S (AMFK k Γ K ρK),
      (algebraMap k T l) ^ (∑ i, e i) • y ∈
        locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}

end Formalism.RankGapBounds.FormsTensorLocalization
end
end

-- bundled from Formalism.RankGapBounds.UniformMeanBound
section
open Real

namespace Formalism.RankGapBounds.UniformMeanTopLine

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

def Lo4 (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u) + 1

def SlopesNv4 : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lo4 D C u0 u ≤ D.muN u0 u

def MLo4 : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + 1

def UBar4 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + MLo4 D C

def uniformMeanError : ℝ :=
  D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + 2 * D.logGam / ((f : ℝ) * D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo4 D C
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar4 D C + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def UniformMeanBound : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → D.EComp C → D.HComp C → D.Count C → D.Slopes C →
    SlopesNv4 D C → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + uniformMeanError D C

end

end Formalism.RankGapBounds.UniformMeanTopLine
end

