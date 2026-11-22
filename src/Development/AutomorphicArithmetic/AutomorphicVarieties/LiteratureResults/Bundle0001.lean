import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ClozelConjCOf
section
noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Lit

def ConjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ τ : SmIrr (GL (Fin a) (Af E)), IsFinComp π τ → ∀ σ : ℂ ≃+* ℂ,
      ∃ π' : CuspSub E a, (∀ τ', IsFinComp π' τ' → IsConjBy σ τ τ') ∧
        ∀ (t : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (σ.symm.toRingHom.comp t) m → π'.HasInfChar t m

def ConjR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a), π.IsRegAlg → ∀ τ : SmIrr (GL (Fin a) (Af F)), π.IsFinComp τ → ∀ σ : ℂ ≃+* ℂ,
      ∃ π' : TR.CuspSub F a, (∀ τ', π'.IsFinComp τ' → IsConjBy σ τ τ') ∧
        ∀ (t : F →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (σ.symm.toRingHom.comp t)) m →
          π'.HasInfChar (InfinitePlace.mk t) m

def FinExC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ τ, IsFinComp π τ

def FinExR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∃ τ, π.IsFinComp τ

theorem clozelConjC_of (hF : FinExC) (h : ConjC) : Published.ClozelConjC := by
  intro E _ _ _ a ha π hπ σ
  obtain ⟨τ, hτ⟩ := hF E a π
  obtain ⟨π', h1, h2⟩ := h E a ha π hπ τ hτ σ
  obtain ⟨τ', hτ'⟩ := hF E a π'
  refine ⟨π', τ, τ', hτ, hτ', h1 τ' hτ', fun φ m hm => h2 _ m ?_⟩
  convert hm using 1
  exact RingHom.ext fun x => σ.symm_apply_apply _

theorem clozelConjR_of (hF : FinExR) (h : ConjR) : Published.ClozelConjR := by
  intro F _ _ _ a ha π hπ σ
  obtain ⟨τ, hτ⟩ := hF F a π
  obtain ⟨π', h1, h2⟩ := h F a ha π hπ τ hτ σ
  obtain ⟨τ', hτ'⟩ := hF F a π'
  refine ⟨π', τ, τ', hτ, hτ', h1 τ' hτ', fun φ m hm => h2 _ m ?_⟩
  convert hm using 2
  exact RingHom.ext fun x => σ.symm_apply_apply _

end UpperTheory.V.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.IsRelCochain
section
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

def smK (k : Kinf E a) : Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (act (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def smLie : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lie E a X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lie E a X), ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

def IsLevelFn (φ : Sm E a) : Prop :=
  (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ u ∈ U, act (.fin u) φ = φ) ∧
    ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) → lie E a (oneL E a) φ = -m • φ

def IsSqIntMod (φ : Sm E a) : Prop :=
  ∃ (s : ℝ) (χ : HChar E), χ.IsAbsPow s ∧ GlobalTheory.UnitaryBC.IsSqInt fun g => ((chiDet a χ g : ℂˣ) : ℂ) * φ.1 g

def IsCuspFn (φ : Sm E a) : Prop :=
  IsLevelFn U Ξ φ ∧ IsCuspidal φ.1 ∧ ∀ l : List (Lie E a), IsSqIntMod ((l.map (lie E a)).prod φ)

variable {U} in

structure IsRelCochain (P : Sm E a → Prop) {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) : Prop where
  equiv : IsCochain (smK Ξ) ω
  basic : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → ω X = 0
  val : ∀ X, ω X ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}

end Defs

def BorelC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    (∀ (γ : GL (Fin a) E) (g : GL (Fin a) (Af E)),
      g⁻¹ * GeneralLinearGroup.map (algebraMap E (Af E)) γ * g ∈ U → IsOfFinOrder γ → γ = 1) →
    ∀ Ξ : AlgRep E a, (∃ N : ℕ, 0 < N ∧ ∀ u : (𝓞 E)ˣ,
      ratC Ξ (GeneralLinearGroup.scalar (Fin a) (Units.map (algebraMap (𝓞 E) E).toMonoidHom (u ^ N))) = 1) →
    ∀ (q : ℕ) (η : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))), IsRelCochain Ξ (IsLevelFn U Ξ) η →
      IsRelCochain Ξ (IsCuspFn U Ξ) (dCo (smLie Ξ) η) →
      ∃ η' : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)),
        IsRelCochain Ξ (IsCuspFn U Ξ) η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η

end UpperTheory.V.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af
open CategoryTheory
open scoped Matrix
open UpperTheory.V.Published.Kato

namespace UpperTheory.V.Lit

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

structure IsBKS (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation C (G F Ω) V) (c : G F Ω → V) : Prop where
  infl : ∀ s ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), c s = 0
  away : ∀ w ∈ S, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∃ x : V, ∀ s ∈ Ine (F := F) A, c s = ρ s x - x
  above : ∀ j : Ω →+* Formalism.BasicNotions.Loc.Om l, (fun x : ↥(decJ F j) => c x.1.1) ∈ Loc.finiteCocycles ((MonoidHom.snd _ _).comp (decJ F j).subtype)
    (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype))

def H1fSelmerVanishing (ρ : Representation C (G F Ω) V) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → (∀ s ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ρ s = 1) →
    ∀ c ∈ Z1 ρ, IsBKS l S ρ c → c ∈ ReciprocityTheory.Gal.B1 ρ

end

def ThorneLit : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (n : ℕ), 2 ≤ n →
    ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
    ∀ (μ : G (maximalRealSubfield F) Ω →* (Qbar p)ˣ), IsLAdicCharOf ι χ μ →
    ∃ (E : IntermediateField ℚ_[p] (Qbar p)) (_ : FiniteDimensional ℚ_[p] ↥E) (r : G F Ω →* GL (Fin n) ↥E),
      Continuous r ∧ AttC ι (toBar r) π ∧ (IsIrr ((toBar r).comp (cycBar F Ω p).ker.subtype) →
      ∀ c : G (maximalRealSubfield F) Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) →
      ∃ (P : GL (Fin n) ↥E) (ν : G F Ω →* (↥E)ˣ)
        (ρ : Representation ↥E (G (maximalRealSubfield F) Ω) (Matrix (Fin n) (Fin n) ↥E)),
        (P : Matrix (Fin n) (Fin n) ↥E)ᵀ = P ∧
        (∀ s, (((ν s : (↥E)ˣ) : ↥E) : Qbar p) =
          ((cycBar F Ω p s ^ (1 - (n : ℤ)) * μ (s.restrictScalars (maximalRealSubfield F)) : (Qbar p)ˣ) : Qbar p)) ∧
        (∀ s s' : G F Ω, s'.restrictScalars (maximalRealSubfield F) = c * s.restrictScalars (maximalRealSubfield F) * c⁻¹ →
          (r s : Matrix (Fin n) (Fin n) ↥E)ᵀ * (P : Matrix (Fin n) (Fin n) ↥E) * (r s' : Matrix (Fin n) (Fin n) ↥E) =
            (ν s : ↥E) • (P : Matrix (Fin n) (Fin n) ↥E)) ∧
        (∀ (s : G F Ω) (Y : Matrix (Fin n) (Fin n) ↥E), ρ (s.restrictScalars (maximalRealSubfield F)) Y =
          (r s : Matrix (Fin n) (Fin n) ↥E) * Y * ((r s)⁻¹ : GL (Fin n) ↥E)) ∧
        (∀ Y : Matrix (Fin n) (Fin n) ↥E, ρ c Y = -((P⁻¹ : GL (Fin n) ↥E) * Yᵀ * (P : Matrix (Fin n) (Fin n) ↥E))) ∧
        H1fSelmerVanishing p ρ)

end UpperTheory.V.Lit
end
end

