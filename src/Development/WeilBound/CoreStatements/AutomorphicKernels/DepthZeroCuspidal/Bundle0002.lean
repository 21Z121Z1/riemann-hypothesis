import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.DzcDegOneFwd
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem dzc_deg_one_fwd (rc : IrrGL (w.adicCompletion E) → WD h) (hrc : IsRecLit h rc)
    (x : IrrGL (w.adicCompletion E)) (hx : x.1 = 1) :
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x) := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨χ, hχ, rfl⟩ := deg_one_ofChar x hx
  rw [ofChar_fixed_iff, H.one, tame_lpOfChar_iff]
  exact fun h1 σ hσ => h1 _ (wild_to_unitsOne a ha σ hσ)

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsArtinCond
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.G2

variable {Ω : Type} [Field Ω]

variable (A : ValuationSubring Ω) in

abbrev CondFamily : Type 1 :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v), WD h → ℤ

variable {A : ValuationSubring Ω}

structure IsArtinCond (c : CondFamily A) : Prop where
  add : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (x y : WD h), c L v h (x.lpSum y) = c L v h x + c L v h y
  charPol : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (x y : WD h), (∀ σ, x.charPol σ = y.charPol σ) → c L v h x = c L v h y
  char : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ) (ha : IsLocalArtin h a)
    (χ : (v.adicCompletion L)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (m : ℕ), HasExponent χ m →
    c L v h (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) = m
  ind : ∀ (K L : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'),
    IsLocalExt L h → ∀ f : ℕ, normV v' = normV v ^ f →
      ∀ (x₁ x₂ : WD h') (y₁ y₂ : WD h), Induces x₁ y₁ → Induces x₂ y₂ → x₁.lpDim = 1 → x₂.lpDim = 1 →
        c K v h y₁ - c K v h y₂ = f * (c L v' h' x₁ - c L v' h' x₂)
  tame : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (y : WD h), IsIrrWD y → 2 ≤ y.lpDim → c L v h y ≤ y.lpDim → IsTameWD y

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.G2

end
end

