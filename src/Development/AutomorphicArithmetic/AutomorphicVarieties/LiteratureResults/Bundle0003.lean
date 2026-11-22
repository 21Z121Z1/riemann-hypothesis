import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd

namespace UpperTheory.V.Lit

def OneUse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (ι : Qbar p ≃+* ℂ) (B : ℕ),
    ∃ k ≥ B, 0 < k ∧ p - 1 ∣ k ∧ ∃ (φ : TR.Sm F 2) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ),
      IsHol k (fun _ => 0) 1 φ ∧ HasExp φ.1 k c₀ c ∧ (∀ y, ‖ι.symm (c₀ y) - 1‖ < 1) ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (c 𝔪)‖ < 1

theorem oneUse_of (h : Published.HilbertOne) : OneUse := by
  intro F _ _ _ p hp hl ι B
  obtain ⟨N, hN⟩ := h F p hl ι
  have hpos : 0 < (p - 1) * p ^ N := Nat.mul_pos (Nat.sub_pos_of_lt hp.out.one_lt) (pow_pos hp.out.pos N)
  exact ⟨(p - 1) * p ^ N * (B + 1), (Nat.le_succ B).trans (Nat.le_mul_of_pos_left _ hpos), Nat.mul_pos hpos B.succ_pos,
    (dvd_mul_right _ _).mul_right _, hN _ (Nat.mul_pos hpos B.succ_pos) (dvd_mul_right _ _)⟩

end UpperTheory.V.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymLow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Lit

def SymSqQ : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) →
    ∃ P : TR.CuspSub ℚ 3, P.IsRegAlg ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      P.HasSat w {α ^ 2, α * β, β ^ 2}

def SymCubeQ : Prop :=
  ∀ π : TR.CuspSub ℚ 2, π.IsRegAlg → (∀ χ : HChar ℚ, χ ≠ 1 → ¬ π.Iso (π.twist χ)) →
    (∀ μ : HChar ℚ, μ ≠ 1 → μ ^ 3 = 1 → ¬ SelfTw (adSys π.HasSat) μ) →
    ∃ P : TR.CuspSub ℚ 4, P.IsRegAlg ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      P.HasSat w {α ^ 3, α ^ 2 * β, α * β ^ 2, β ^ 3}

theorem SymSat.sq (h : SymSat) : SymSqQ := fun π hr hn => by
  obtain ⟨P, hP, hs⟩ := h π hr hn 2 one_le_two
  refine ⟨P, hP, hs.mono fun w ⟨α, β, h1, h2⟩ => ⟨α, β, h1, ?_⟩⟩
  have e0 : (Finset.range (2 + 1)).val = ({0, 1, 2} : Multiset ℕ) := by decide
  rw [e0] at h2
  simpa using h2

end UpperTheory.V.Lit
end
end

