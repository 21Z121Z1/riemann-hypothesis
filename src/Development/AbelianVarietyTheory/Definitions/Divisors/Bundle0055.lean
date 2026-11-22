import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CongWtLvLac
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def CongWtLvLac : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IsIntegralOpW ι lam w₀ (t j)) → (∀ j, ∀ g ∈ (t j).support, ∀ u, ¬ Apart u v' → cLoc u g = 1) →
      ActsBy (K ⊓ Kv.comap (cLoc v')) t η →
    ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ (τ₀ : E →+* ℂ), OverPair ι v' τ₀ → ∀ (μ₀ : Fin a → ℤ), Antitone μ₀ → ∀ (M : ℕ), 0 < M →
    ∀ U, OfType lam (K ⊓ Kv.comap (cLoc v')) U → HasTypeVec w₀ (K ⊓ Kv.comap (cLoc v')) J θ 1 U →
      ∃ d : ℕ, ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ M ∣ N ∧
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ (U' : Submodule ℂ (UA E a → ℂ)) (mu : (E →+* ℂ) → DomWeight a),
          (∀ τ, mu τ ≠ lam τ → OverPair ι v' τ) ∧ (∀ k, |(mu τ₀).w k - (N : ℤ) * μ₀ k| ≤ d) ∧ OfType mu K U' ∧
          (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def GenTyL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ), (∀ j, IsIntegralOpW ι lam w₀ (t j)) → ActsBy K t η →
    ∀ (Fam : ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ), (J →* Multiplicative (ZMod (l ^ m))) → Prop),
      (∀ J m θ, Fam J m θ → IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
        IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
        Function.Surjective θ) →
      (∀ N : Set (GL (Fin a) (w₀.adicCompletion E)), IsOpen N → 1 ∈ N → ∀ m₀ : ℕ,
        ∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧ (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ Fam J m θ) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ S, IsSplitAt w ∧ Apart w w₀ ∧
        ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → x ∈ K) →
    ∀ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric → D ≠ 0 →
    ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {ϑ | ∃ U', OfType lam K U' ∧
        (∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Fam J m θ ∧ ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U') ∧
        (∀ w ∈ S, GenAt D U' w) ∧ ϑ = fun j => ι.symm (η U' j)}

end GlobalTheory.CongW
end
end

