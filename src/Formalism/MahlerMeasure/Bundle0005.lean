import Formalism.MahlerMeasure.Bundle0004

-- bundled from Formalism.MahlerMeasure.CsSaturated
section
namespace Formalism.GM.M

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def WtSpC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | ∀ c ∈ Cs, wt LL j c m = la c}

def GlStableC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S

noncomputable def HWC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  WtSpC p LL j Cs la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ c < d), LinearMap.ker (glAct p LL j c d)

noncomputable def IsoC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | HWC p LL j Cs la ≤ S ∧ GlStableC p LL j Cs S}

def CsSaturated {r : ℕ} (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) : Prop :=
  ∀ la la', (∀ c ∈ Cs, la c = la' c) → (la ∈ T ↔ la' ∈ T)

def IsTypeProj (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  P ∘ₗ P = P ∧ LinearMap.range P = ⨆ (la : Fin r → ℤ) (_ : la ∈ T), IsoC p LL j Cs la ∧
    LinearMap.ker P = ⨆ (la : Fin r → ℤ) (_ : la ∉ T), IsoC p LL j Cs la

noncomputable def WeylLat (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {L | h ∈ L ∧ ∀ c d : Fin r, c ≠ d → ∀ k : ℕ, ∀ x ∈ L,
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ L}

def Primitive' (p : ℕ) [Fact p.Prime] {σ : Type} (h : MvPolynomial σ ℚ_[p]) : Prop :=
  h ∈ IntPol p σ ∧ ∃ m, ‖h.coeff m‖ = 1

def Letters.take (LL : Letters N) (k : ℕ) (hk : k ≤ N) : Letters k where
  vec := fun i => LL.vec (Fin.castLE hk i)
  deg := fun i => LL.deg (Fin.castLE hk i)

noncomputable def MMw (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Y p LLw J M ⊓ HWC p LLw K (univ.erase ρ) w ⊓ WtSpC p LLw K univ w

noncomputable def MMwZ (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  (MMw p LLw J M ρ w).restrictScalars ℤ_[p] ⊓ IntPol p (Fin K × Fin r)

noncomputable def FilE (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  MMwZ p LLw J M ρ w ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]

noncomputable def grLat (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Submodule.span ℤ_[p] (initPart v e '' (FilE p LLw J M ρ w v e : Set (MvPolynomial (Fin K × Fin r) ℚ_[p])))

end Formalism.GM.M
end

-- bundled from Formalism.MahlerMeasure.GamInt
section
namespace Formalism.GM.M

open MvPolynomial Finset

def GamInt : Prop :=
  ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ PolZ p r LL → f' ∈ PolZ p r LL →
    ∃ c : ℕ → ℤ_[p], ∀ n, LL.total ≤ n →
      ((p : ℚ_[p]) ^ (C * (N + 3) * r ^ 2 * (Nat.log p (LL.total + LL.deg (Fin.last N) + r) + 1))) *
          tieGam p LL ρ z n f f' =
        ∑ i ∈ range (LL.total + LL.deg (Fin.last N) + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])

end Formalism.GM.M
end

-- bundled from Formalism.MahlerMeasure.LevelConst
section
namespace Formalism.GM

def LevelConst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a r o n z j : ℕ), 1 ≤ a → 1 ≤ r → o + n + z + 1 ≤ 8 * a →
    j ≤ o → j ≤ n →
    |((padicValRat p
        (((j.factorial ^ 2 * (o + n + r + z + 1 - 2 * j + j - 1).choose j * z.factorial *
            (o - j).factorial * (n - j).factorial : ℕ) : ℚ) /
          (((z + o).factorial * n.factorial : ℕ) : ℚ)) : ℤ) : ℝ)| ≤ 3 * lgV2 p a r

end Formalism.GM
end

