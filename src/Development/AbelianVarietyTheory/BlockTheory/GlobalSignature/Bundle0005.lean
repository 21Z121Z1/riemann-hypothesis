import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

open NumberField Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

theorem mem_perp (W : HSpace E) (x y : W.V) : y ∈ perp W x ↔ W.hD y x = 0 := Iff.rfl

def IsSelfDualLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.SigOK ∧ W.rank = M ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def Step (β : E) (P Q P' Q' : ℕ) : Prop :=
  (β = 1 ∧ 1 ≤ P ∧ P' = P - 1 ∧ Q' = Q) ∨ (β = -1 ∧ 1 ≤ Q ∧ P' = P ∧ Q' = Q - 1)

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ (L : Submodule (𝓞 E) W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V),
    IsSelfDualLattice W L ∧ x ∈ L ∧
    OfKind W' M' P' Q' ∧
    HSpace.IsIsomEmb W' W ι ∧
    LinearMap.range ι = perp W x ∧
    W'.L0.map (ι.restrictScalars (𝓞 E)) = L ⊓ (perp W x).restrictScalars (𝓞 E) ∧
    L = Submodule.span (𝓞 E) {x} ⊔ (L ⊓ (perp W x).restrictScalars (𝓞 E))

def ExistsPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    ∀ (β : E) (P' Q' : ℕ), Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ HasComplement W x (M - 1) P' Q'

def ForallPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    ∀ (β : E) (P' Q' : ℕ), Step β P Q P' Q' →
      (∃ x : W.V, W.hD x x = β) ∧ ∀ x : W.V, W.hD x x = β → HasComplement W x (M - 1) P' Q'

theorem ForallPerpOver.exists (h : ForallPerpOver E) : ExistsPerpOver E := by
  intro W M P Q hW hM β P' Q' hs
  obtain ⟨⟨x, hx⟩, hall⟩ := h W M P Q hW hM β P' Q' hs
  exact ⟨x, hx, hall x hx⟩

example (W : HSpace E) : IsSelfDualLattice W W.L0 := ⟨W.standardTuple_isLattice, W.baseLattice_isUnimodular⟩

theorem injective_of_isIsomEmb {W' W : HSpace E} {ι : W'.V →ₗ[E] W.V}
    (h : HSpace.IsIsomEmb W' W ι) : Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine W'.nondeg.1 y fun z => ?_
  rw [← h y z, hy]
  simp

example (W : HSpace E) (x : W.V) (hx : W.hD x x = 1) : x ∉ perp W x := by
  rw [mem_perp, hx]; exact one_ne_zero

end General

def UnitVectorPerp (D : D7) : Prop :=
  @ExistsPerpOver D.host.E _ _ D.host.cmStar

def UnitVectorPerpAll (D : D7) : Prop :=
  @ForallPerpOver D.host.E _ _ D.host.cmStar

theorem UnitVectorPerpAll.unitVectorPerp {D : D7} (h : UnitVectorPerpAll D) : UnitVectorPerp D :=
  @ForallPerpOver.exists D.host.E _ _ D.host.cmStar h

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnitVectorOrthogonal
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

open NumberField Formalism.BasicNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

def perpLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) : Submodule (𝓞 E) W.V :=
  L ⊓ (perp W x).restrictScalars (𝓞 E)

def IsSelfDualLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ L : Submodule (𝓞 E) W.V, IsSelfDualLat W L ∧ x ∈ L ∧
    L = Submodule.span (𝓞 E) {x} ⊔ perpLat W L x ∧
    ∃ (W' : HSpace E) (ι : W'.V →ₗ[E] W.V), OfKind W' M' P' Q' ∧
      HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = perp W x ∧
      W'.L0.map (ι.restrictScalars (𝓞 E)) = perpLat W L x

def UnitVectorPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ HasComplement W x (M - 1) P (Q - 1))

def UnitVectorPerpEveryOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    (1 ≤ P → (∃ x : W.V, W.hD x x = 1) ∧
      ∀ x : W.V, W.hD x x = 1 → HasComplement W x (M - 1) (P - 1) Q) ∧
    (1 ≤ Q → (∃ x : W.V, W.hD x x = -1) ∧
      ∀ x : W.V, W.hD x x = -1 → HasComplement W x (M - 1) P (Q - 1))

end Generic

def UnitVectorPerp (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpOver D.host.E

def UnitVectorPerpEvery (D : D7) : Prop :=
  letI := D.host.cmStar
  UnitVectorPerpEveryOver D.host.E

end GlobalTheory.IndefiniteRowSideFullHecke.UnitVectorOrthogonal

end
end

