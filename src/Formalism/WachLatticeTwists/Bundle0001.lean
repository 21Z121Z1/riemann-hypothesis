import Formalism.CharacterColumnKernels.Bundle0001

-- bundled from Formalism.WachLatticeTwists.Statement
section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

def negCount (s : Multiset ℤ) : ℕ := Multiset.card (s.filter (fun u => u < 0))

def StatRowColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (I : Submodule O M) (ℓ e : ℕ),
    (∀ m : M, ((ℓ : O) ^ e) • m ∈ I) →
    Module.length O (M ⧸ I) ≤
      (Module.finrank O M : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) +
        Module.length O (Submodule.torsion O M)

def SubmoduleLengthBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] (N : Submodule O (d → Formalism.NG.KO O)) (ℓ c : ℕ),
    (∀ x ∈ N, ((ℓ : O) ^ c) • x = 0) →
    Module.length O N ≤
      (Fintype.card d : ℕ∞) * ((c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))

def StatJumpsColumn : Prop :=
  ∀ (ι : Type*) [Fintype ι] (cloud lows : ι → Multiset ℤ) (m j h0 : ℕ),
    (∀ τ, ∀ u ∈ cloud τ, 0 < u) → (∀ τ, Multiset.card (lows τ) ≤ m) →
    j = h0 + ∑ τ, negCount (cloud τ + lows τ) → h0 = 0 →
    j ≤ Fintype.card ι * m

def StatJumpsRow : Prop :=
  ∀ (ι : Type*) [Fintype ι] (cloud lows : ι → Multiset ℤ) (m j h0 : ℕ),
    (∀ τ, ∀ u ∈ cloud τ, u < 0) → (∀ τ, Multiset.card (lows τ) ≤ m) →
    j = h0 + ∑ τ, negCount ((cloud τ + lows τ).map (fun u => -u - 1)) → h0 = 0 →
    j ≤ Fintype.card ι * m

end Formalism.RepresentationBoundsCohomology
end
end

-- bundled from Formalism.WachLatticeTwists.StatementDual
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology

def annKO (O : Type*) [CommRing O] [IsDomain O] {H : Type*} [AddCommGroup H] [Module O H]
    (S : Submodule O H) : Submodule O (H →ₗ[O] Formalism.NG.KO O) where
  carrier := {φ | ∀ x ∈ S, φ x = 0}
  add_mem' := by intro a b ha hb x hx; simp [ha x hx, hb x hx]
  zero_mem' := by intro x _; rfl
  smul_mem' := by intro c a ha x hx; simp [ha x hx]

def StatDualColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (H : Type*) [AddCommGroup H] [Module O H] [Module.Finite O H] (I M : Submodule O H), I ≤ M →
    Module.length O (annKO O I ⧸ (annKO O M).comap (annKO O I).subtype) =
      Module.length O (M ⧸ I.comap M.subtype)

end Formalism.RepresentationBoundsCohomology
end
end

