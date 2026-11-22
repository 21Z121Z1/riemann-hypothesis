import Formalism.FrobeniusContraction.Bundle0001

-- bundled from Formalism.FrobeniusContraction.EulerC
section
noncomputable section

namespace Formalism.WachCohomologyFacts.Top2

def EulerC : Prop :=
  ∀ (K D : Type) [Field K] [AddCommGroup D] [Module K D] (v φ γ : D →ₗ[K] D)
    (N B G : Submodule K D) (A : ℕ),
    Function.Injective v → (∀ x, φ (γ x) = γ (φ x)) →
    N ≤ B → (∀ x ∈ N, φ x ∈ B) → (∀ x ∈ N, γ x - x ∈ G) →
    (∀ y ∈ B, γ y - y ∈ B.map v) → (∀ z ∈ G, φ z - z ∈ B.map v) →
    N.map (v ^ (A + 1)) ≤ G → G ≤ N.map v →
    (∀ x ∈ N.map (v ^ A), φ x ∈ N.map (v ^ A)) →
    (∀ y ∈ N.map (v ^ A), ∃ x ∈ N.map (v ^ A), φ x - x = y) →
    (∀ x ∈ N.map (v ^ A), φ x = x → x = 0) →
    (∀ x ∈ N.map (v ^ (A + 1)), φ x ∈ N.map (v ^ (A + 1))) →
    (∀ y ∈ N.map (v ^ (A + 1)), ∃ x ∈ N.map (v ^ (A + 1)), φ x - x = y) →
    (∀ x ∈ N.map (v ^ (A + 1)), φ x = x → x = 0) →
    (∀ x ∈ N.map (v ^ A), γ x - x ∈ N.map (v ^ (A + 1))) →
    Module.length K (↥N ⧸ (N.map (v ^ A)).comap N.subtype) < ⊤ →
    Module.length K (↥B ⧸ N.comap B.subtype) < ⊤ →
    let Z0 : Submodule K D := N ⊓ LinearMap.ker (φ - 1) ⊓ LinearMap.ker (γ - 1)
    let C1 : Submodule K (D × D) := B.prod G
    let d1 : D × D →ₗ[K] D := (γ - 1).coprod (-(φ - 1))
    let Z1 : Submodule K (D × D) := C1 ⊓ LinearMap.ker d1
    let B1 : Submodule K (D × D) := N.map ((φ - 1).prod (γ - 1))
    let vB : Submodule K D := B.map v
    let vN : Submodule K D := N.map v
    let h0 := Module.length K ↥Z0
    let h1 := Module.length K (↥Z1 ⧸ B1.comap Z1.subtype)
    let h2 := Module.length K (↥vB ⧸ (C1.map d1).comap vB.subtype)
    h0 < ⊤ ∧ h1 < ⊤ ∧ h2 < ⊤ ∧
      h0 + h2 = h1 + Module.length K (↥vN ⧸ G.comap vN.subtype) ∧
      N.map (v ^ (A + 1)) ≤ C1.map d1

def IneqI : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    Formalism.WachCohomologyFacts.Top.sg f ℓ h i < (ℓ : ℤ) * (Formalism.WachCohomologyFacts.Top.sg f ℓ h (i + 1) + 1) - h i

end Formalism.WachCohomologyFacts.Top2
end
end

-- bundled from Formalism.FrobeniusContraction.HighestWeightResidueAvoids
section
noncomputable section

open Classical

namespace Formalism.WachCohomologyFacts.V2

open Formalism.WachCohomologyFacts

def FrobContractsSharp : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    h < (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    (∀ x ∈ W.XMN M, W.Φ x ∈ Ideal.span {B.q} • W.XMN M) ∧
      ∀ k : ℕ, ∀ x ∈ B.I ^ k • W.XMN M, W.Φ x ∈ B.I ^ (k + 1) • W.XMN M

def FrobSubIdUniqueSharp : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    h < (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    IsAdicComplete B.I ↥(W.XMN M) →
    (∀ y ∈ W.XMN M, ∃! x, x ∈ W.XMN M ∧ W.Φ x - x = y) ∧
      ∀ y ∈ W.XMN M, ∀ z ∈ W.XMN M, W.Φ z - z = W.Γ y - y → (y, z) ∈ W.B1

def Sat : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (ι : Type) [Fintype ι]
    (ℓ f f' : A), IsRelPrime ℓ (f * f') →
    ∀ x : ι → FractionRing A,
      (∀ i, ∃ a : A, algebraMap A (FractionRing A) f' * x i = algebraMap A (FractionRing A) a) →
      (∃ k : ℕ, ∀ i, ∃ a : A,
        algebraMap A (FractionRing A) (ℓ ^ k) * x i = algebraMap A (FractionRing A) (f * a)) →
      ∀ i, ∃ a : A, x i = algebraMap A (FractionRing A) (f * a)

def sgN (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def SgBoundN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (m : ZMod f → ℤ),
    2 ≤ ℓ → (∀ i, (ℓ : ℤ) * m (i - 1) ≤ m i + h i) → ∀ i, m i ≤ sgN f ℓ h i

def IneqIN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    sgN f ℓ h i < (ℓ : ℤ) * (sgN f ℓ h (i - 1) + 1) - h i

def LemmaSN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t M : ℕ) (h w η σ : ZMod f → ℕ) (G : ZMod f → Bool)
    (k : ℕ → ℕ → ZMod f → ℤ),
    1 ≤ t → 1 ≤ M →
    (∀ i, G i = true → 1 ≤ w i ∧ w i + t - 1 ≤ η i) →
    (∀ i, G i = false → (h i : ℤ) - η i ≤ w i ∧ w i + t ≤ h i) →
    (∀ i, η i + 4 * σ i + 6 < ℓ) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → |k c μ i| ≤ σ i) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M →
      0 ≤ (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ∧
      (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ≤ h i) →
    (∀ i, (Finset.Icc 1 t ×ˢ Finset.Icc 1 M).val.map
        (fun cμ : ℕ × ℕ => (((w i : ℤ) + cμ.1 - 1 - k cμ.1 cμ.2 i : ℤ) : ZMod ℓ)) =
      M • (Finset.Icc 1 t).val.map (fun c : ℕ => (((w i : ℤ) + c - 1 : ℤ) : ZMod ℓ))) →
    ∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → k c μ i = 0

def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1

def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)

def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)

def HighestWeightResidueAvoids : Prop :=
  (∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ), 0 ≤ σ →
    (∀ x ∈ U, 0 ≤ x ∧ x ≤ h) → (h : ℤ) + 2 * σ + η + 5 < ℓ →
    (∀ x ∈ ClN G h η U, (η : ℤ) + 2 * σ + 3 < (if G then x else (h : ℤ) - x)) →
    ResidueAvoidance ℓ G h η σ U) ∧
  (∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), (∀ i, h i + 2 < ℓ) → ∀ i, sgN f ℓ h i = 0)

end Formalism.WachCohomologyFacts.V2
end
end

