import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.EndoscopicGroupCriteria.UnitaryUp3OfUpAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

namespace UpperTheory.GalN.V

def PropEGN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ

def PropEGuN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ ∧ Unlinked (ad0 ρ)

def PropEGadN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ ∧ Unlinked (ad0 ρ) ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹))

def MixedAdmissibleResidueMembership : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) →
    (∀ c, IsConjEl c → ξ c = -1) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) → (∃ g, ¬ Cong (ξ g ^ 2) 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (k t : ℕ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧
      Continuous r ∧ IrrOpen r ∧ AttR ι r π ∧ Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ k * ξ ∧ ResSum r ![1, ξ] ∧
      (TypeAway r ![1, ξ] ∧ RW ι r) ∧ ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        (w ∈ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ) + t, -(t : ℤ)])) ∧
        (w ∉ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ), 0] ![1, ξ] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ), 0]))

def MixOfN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ),
    Hyp T k₀ φ → CharDat T k₀ φ → ∃ k t r, MixDat k₀ ι (up D.ξ) k t r ∧ RW ι r

def IndAutLN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → RW ι r → IsAutC ι (R.comp (resQ T.L))

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

def Wts0 (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

def WtsN (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  Wts0 T h P ∧ (h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits)

variable {T} {h : Fin 4 → ℤ} {P : PD T.ι (G T.F Ω) (PadicAlgCl l)}

theorem mkWts (k : Wts0 T h P) (_ : h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits) : T.Wts h P := k
theorem mkWts4 (k : Wts0 T (fun i => 2 * D.wts4 i) P) : T.Wts (fun i => 2 * D.wts4 i) P :=
  mkWts k fun hb => absurd hb (by simp [Raw.wts4]; omega)
end

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinFreePU
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hint : A.valuation.Integers A :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => A.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).1 hr⟩, rfl⟩ }
  have hle : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ F Ω)
    exact hint.mem_of_integral (h1.tower_top (A := A))
  let I : Ideal (𝓞 F) :=
    { carrier := {x | A.valuation (algebraMap F Ω (x : F)) < 1}
      add_mem' := by
        intro a b ha hb
        show A.valuation (algebraMap F Ω ((a : F) + (b : F))) < 1
        rw [map_add]
        exact A.valuation.map_add_lt ha hb
      zero_mem' := by
        show A.valuation (algebraMap F Ω (0 : F)) < 1
        rw [map_zero, map_zero]
        exact lt_of_le_of_lt zero_le' hp
      smul_mem' := by
        intro c a ha
        show A.valuation (algebraMap F Ω ((c : F) * (a : F))) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) ha }
  have hI : I.IsPrime := by
    refine Ideal.isPrime_iff.2 ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ A.valuation (algebraMap F Ω (1 : F)) < 1
      rw [map_one, map_one]
      exact lt_irrefl _
    · intro a b hab
      show A.valuation (algebraMap F Ω (a : F)) < 1 ∨ A.valuation (algebraMap F Ω (b : F)) < 1
      have hab' : A.valuation (algebraMap F Ω (a : F)) * A.valuation (algebraMap F Ω (b : F)) < 1 := by
        have h0 : A.valuation (algebraMap F Ω ((a : F) * (b : F))) < 1 := hab
        rwa [map_mul, map_mul] at h0
      by_contra hne
      push_neg at hne
      have ha1 := le_antisymm (hle a) hne.1
      have hb1 := le_antisymm (hle b) hne.2
      rw [ha1, hb1, mul_one] at hab'
      exact lt_irrefl _ hab'
  have hpI : ((p : ℕ) : 𝓞 F) ∈ I := by
    show A.valuation (algebraMap F Ω (((p : ℕ) : 𝓞 F) : F)) < 1
    simpa using hp
  have hne : I ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpI
    exact hp0 (by exact_mod_cast hpI)
  exact ⟨⟨I, hI, hne⟩, fun x => Iff.rfl, hpI⟩

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  classical
  refine ⟨M.factorial, Nat.factorial_pos M, ?_⟩
  intro C _ χ hχ s
  rw [← map_pow]
  refine hχ _ (fun ζ hζ => ?_)
  have hmem : ∀ z : Ω, z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ z ^ M = 1 :=
    fun z => Polynomial.mem_nthRootsFinset hM 1
  have hcard : (Polynomial.nthRootsFinset M (1 : Ω)).card ≤ M :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  let σ : Equiv.Perm (Polynomial.nthRootsFinset M (1 : Ω)) :=
    Equiv.subtypeEquiv s.toEquiv (fun z => by
      show z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ s z ∈ Polynomial.nthRootsFinset M (1 : Ω)
      rw [hmem, hmem, ← map_pow, map_eq_one_iff _ s.injective])
  have hpow : σ ^ M.factorial = 1 := by
    have h1 := pow_card_eq_one (x := σ)
    rw [Fintype.card_perm, Fintype.card_coe] at h1
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hcard
    rw [hc, pow_mul, h1, one_pow]
  have hit : ∀ (m : ℕ) (z : Polynomial.nthRootsFinset M (1 : Ω)),
      (((σ ^ m) z : Polynomial.nthRootsFinset M (1 : Ω)) : Ω) = (s ^ m) (z : Ω) := by
    intro m
    induction m with
    | zero =>
      intro z
      rfl
    | succ m ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
      rfl
  have h2 := hit M.factorial ⟨ζ, (hmem ζ).2 hζ⟩
  rw [hpow] at h2
  exact h2.symm

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  rw [show b * r s * b⁻¹ = (b * g⁻¹) * (g * r s * g⁻¹) * (b * g⁻¹)⁻¹ by group]
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
    Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
  exact Finset.prod_congr rfl (fun i _ => by rw [(hg s).2 i])
end

