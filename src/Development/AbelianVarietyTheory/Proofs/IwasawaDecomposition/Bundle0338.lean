import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualMeasureGlobalConstRankOnly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨ψ, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomials
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.OSplitCore

theorem mem_mul_of_mem {A : Type} [CommRing A] (R : Subring A) {m n q : ℕ} (X : Matrix (Fin m) (Fin n) A)
    (Y : Matrix (Fin n) (Fin q) A) (hX : ∀ i j, X i j ∈ R) (hY : ∀ i j, Y i j ∈ R) :
    ∀ i j, (X * Y) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R.mul_mem (hX _ _) (hY _ _)

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f :=
  rfl

theorem mapped_props (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (U : Set Γ) (p : Γ → ℂ[X]) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hadic : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (r : Γ →* GL (Fin a) O) (hr : Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)))
    (hss : IsSSRep (mapRep (algebraMap O (FractionRing O)) r))
    (hp : ∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map
      (ι.toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) :
    IsSSRep (mapRep iq (mapRep (algebraMap O (FractionRing O)) r)) ∧
    Continuous (fun g => ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l))) ∧
    (∀ σ ∈ U, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) σ : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
      (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j,
      ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R := by
  have hcz : CharZero (FractionRing O) := ⟨fun m n h => by
    have := congrArg iq h
    simpa using this⟩
  have hcoe : ∀ g, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)) =
      ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (iq.comp (algebraMap O (FractionRing O))) := by
    intro g
    rw [coe_mapRep, coe_mapRep, Matrix.map_map]
    rfl
  refine ⟨GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ iq a _ hss, ?_, ?_, ?_⟩
  · simp only [hcoe]
    exact hr.matrix_map (GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure l O hadic iq hiq)
  · intro σ hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map]
    exact hp σ hσ
  · obtain ⟨T, hT⟩ := GlobalTheory.T.exists_finset_image_mem_subring l O iq hiq
    refine ⟨T, fun R hR hTR g i j => ?_⟩
    rw [hcoe]
    exact hT R hR hTR _

theorem exists_splitting_set : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ (ρ₀ : G E Ω →* GL (Fin a) (Qbar l)) (T : Finset (Qbar l)), IsSSRep ρ₀ ∧
      Continuous (fun g => ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
      ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
        (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j, ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R
  swap
  · refine ⟨∅, ?_⟩
    intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq _ r hr hss hp
    subst h
    exfalso
    obtain ⟨h1, h2, h3, T, h4⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
    exact hex ⟨_, T, h1, h2, h3, h4⟩
  obtain ⟨ρ₀, T, hss₀, hc₀, hp₀, hT⟩ := hex
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.semisimple_matrix_rep_decomp ρ₀ hss₀
  choose b E D σ₀ hDE hran hσ₀ using fun j => GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep ρ₀ (Vs j) (hirr j).2.1
  let T' : Finset (Qbar l) := T ∪ Finset.univ.biUnion (fun j : Fin n =>
    Finset.univ.image (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) ∪
      Finset.univ.image (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2))
  refine ⟨T'.image ι, ?_⟩
  intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq hS r hr hss hp
  subst h
  obtain ⟨hss', hc', hp', -⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
  have hT'R : ∀ t ∈ T', t ∈ iq.range := by
    intro t ht
    obtain ⟨x, hx⟩ := hS (ι t) (Finset.mem_image_of_mem _ ht)
    exact ⟨x, ι.injective hx⟩
  have hRz : ∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ iq.range := fun z => ⟨_, hiq z⟩
  have hTR : (↑T : Set (Qbar l)) ⊆ (iq.range : Set (Qbar l)) := fun t ht => hT'R t (Finset.mem_union_left _ ht)
  have hER : ∀ j i s, E j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hDR : ∀ j i s, D j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hρ₀R := hT iq.range hRz hTR
  set ρ := mapRep (algebraMap O (FractionRing O)) r with hρ
  have hcp : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
    GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense _ _ hc' hc₀ U hU fun x hx =>
      Polynomial.map_injective _ ι.injective (by rw [hp' x hx, hp₀ x hx])
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (mapRep iq ρ) ρ₀ hss' hss₀ hcp
  have hint' : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) =
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g
    rw [hPm g]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  apply GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models iq ρ
  intro V hV
  obtain ⟨j, M, hM, hMV, hMd⟩ := GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub (mapRep iq ρ) ρ₀ Pm hint' hss' Vs
    hint.submodule_iSup_eq_top hirr V hV
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_rep_lift_of_entries_mem_range iq (σ₀ j) fun g i s => by
    have : ((σ₀ j g : GL (Fin (b j)) (Qbar l)) : Matrix (Fin (b j)) (Fin (b j)) (Qbar l)) i s ∈ iq.range := by
      rw [(hσ₀ j g).1]
      exact mem_mul_of_mem _ _ _ (mem_mul_of_mem _ _ _ (hDR j) (hρ₀R g)) (hER j) i s
    exact this
  refine ⟨b j, σ, M * E j, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [← Matrix.mulVec_mulVec] at hvw
    have hv : (E j).mulVec v ∈ Vs j := hran j ▸ ⟨v, rfl⟩
    have hw : (E j).mulVec w ∈ Vs j := hran j ▸ ⟨w, rfl⟩
    have hsub : (E j).mulVec v - (E j).mulVec w ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hvw
    have h0 := hMd.le_bot ⟨hsub, Submodule.sub_mem _ hv hw⟩
    have hEq : (E j).mulVec v = (E j).mulVec w := sub_eq_zero.1 h0
    have := congrArg (D j).mulVec hEq
    simpa [Matrix.mulVec_mulVec, hDE j] using this
  · rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hran j, hMV]
  · intro g
    rw [hσ, ← Matrix.mul_assoc, hM g, Matrix.mul_assoc, (hσ₀ j g).2, Matrix.mul_assoc]

end GlobalTheory.OSplitCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemIsot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowFix

open Formalism.L2.NG Formalism.IndefR.principalLevelFrame

theorem exists_fixed_of_mem_isot {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A)
    (π : FinTyp L n) (Q : (π.S →ₗ[ℂ] A) → Prop) (Kp : Formalism.AUTREP.GAf L n → Prop) {y : A}
    (hy : y ∈ ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ Q Φ), LinearMap.range Φ) (hy0 : y ≠ 0)
    (hfix : ∀ κ, Kp κ → ρ κ y = y) :
    ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
  classical
  let ι := {Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}
  have hy' : y ∈ ⨆ j : ι, LinearMap.range j.1 := by
    rwa [iSup_subtype'] at hy
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy'
  let Y : Finset ι → Submodule ℂ A := fun t => ⨆ j ∈ t, LinearMap.range j.1
  have hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap, ← j.2.1 g v]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) →
      ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range j.1 ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨_, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := ((Y t).comap j.1).map π.S.subtype
      have hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U := by
        rintro h _ ⟨a, ha, rfl⟩
        refine ⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩
        have ha' : j.1 a ∈ Y t := ha
        show j.1 _ ∈ Y t
        rw [j.2.1 h a]
        exact hYst t h _ ha'
      rcases π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU
      ·
        have hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v := by
          intro κ hκ
          let v' : π.S := ⟨rt L n κ v, π.stable κ v v.2⟩
          have hmem : v' - v ∈ (Y t).comap j.1 := by
            rw [Submodule.mem_comap, map_sub, j.2.1 κ v]
            have h1 := hxfix κ hκ
            rw [map_add] at h1
            have h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z := by
              rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t κ z hz)
          have hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U := ⟨_, hmem, rfl⟩
          rw [hU, Submodule.mem_bot] at hU'
          exact sub_eq_zero.1 hU'
        by_cases hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0
        · have hv' : v = 0 := Subtype.ext hv
          subst hv'
          simp only [map_zero, zero_add] at hx0 hxfix
          exact ih z hz hx0 hxfix
        · exact ⟨v, v.2, hv, hvfix⟩
      · have hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U := by rw [hU]; exact v.2
        obtain ⟨a, ha, hav⟩ := hvU
        have : a = v := Subtype.ext hav
        subst this
        exact ih _ (add_mem ha hz) hx0 hxfix
  exact key s y (by simpa [Y] using hs) hy0 hfix

theorem exists_fixed_rowRep : ∀ (D : D7) (V : HSp D) (n : ℕ) (Sp : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (σ : principalLevelFrame.FTR θ P M J χ e) (Kp : Formalism.AUTREP.GAf D.host.E n → Prop), (∀ b κ, Kp κ → P.ψ κ ∈ J b ∧ χ b (P.ψ κ) = 1) → ∃ f ∈ (principalLevelFrame.rowRepR θ σ).S, f ≠ 0 ∧ ∀ κ, Kp κ → NG.rt D.host.E n κ f = f := by
  intro D V n Sp θ P M J χ e σ Kp hK
  obtain ⟨b, hb⟩ := rowRepR_occ θ σ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓
      isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ)) := hy
  rw [Submodule.mem_inf] at hy'
  have hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b) := (Submodule.mem_inf.1 hy'.1).1
  have hfixY : ∀ κ, Kp κ → actM P M κ y = y := by
    intro κ hκ
    have hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      intro T hT
      have hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T := hT
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      rw [actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]
    have h := hle hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h
  obtain ⟨f, hf, hf0, hffix⟩ := exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ))
    (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY
  refine ⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hf0
    funext g
    have := congrFun h0 g
    simpa using this
  · rw [← conj_rt, hffix κ hκ]

end GlobalTheory.RowFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReOfDiv
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

section Trans

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def LocIso.trans {A B C : Formalism.MainNotions.S.Loc.LocAt F E sig p} (a : Formalism.L2.S.LocIso A B) (b : Formalism.L2.S.LocIso B C) :
    Formalism.L2.S.LocIso A C where
  eF := a.eF.trans b.eF
  eF_ι x := (congrArg b.eF (a.eF_ι x)).trans (b.eF_ι x)
  eF_val x y := (a.eF_val x y).trans (b.eF_val _ _)
  eF_cont := b.eF_cont.comp a.eF_cont
  eF_symm_cont := a.eF_symm_cont.comp b.eF_symm_cont
  eF_ql x := (congrArg b.eF (a.eF_ql x)).trans (b.eF_ql x)
  eE := a.eE.trans b.eE
  eE_alg x := (congrArg b.eE (a.eE_alg x)).trans (b.eE_alg _)
  eE_ι x := (congrArg b.eE (a.eE_ι x)).trans (b.eE_ι x)
  eE_cont := b.eE_cont.comp a.eE_cont
  eE_symm_cont := a.eE_symm_cont.comp b.eE_symm_cont
  eE_cj y := (congrArg b.eE (a.eE_cj y)).trans (b.eE_cj _)
  eE_O y := (a.eE_O y).trans (b.eE_O _)
  eE_psi y := (a.eE_psi y).trans (b.eE_psi _)

variable {R : Ranks} {Word Tau : Type} {hc : Word → Tau → HCParam R}

def SIso.trans {s s' s'' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc} (a : SIso s s') (b : SIso s' s'') : SIso s s'' where
  cd := a.cd.trans b.cd
  del := a.del.trans b.del
  letter := a.letter.trans b.letter
  eHH := a.eHH.trans b.eHH
  eCu u := (a.eCu u).trans (b.eCu u)
  Pu_eq u x := (congrArg b.eHH (a.Pu_eq u x)).trans (b.Pu_eq u _)
  volN := a.volN.trans b.volN
  volH := a.volH.trans b.volH
  eT u u' := (a.eT u u').trans (b.eT u u')
  aTerm_eq u u' t x := (congrArg (b.eCu u) (a.aTerm_eq u u' t x)).trans (b.aTerm_eq u u' _ _)
  isId t := (a.isId t).trans (b.isId _)
  inS t := (a.inS t).trans (b.inS _)
  relevant t := (a.relevant t).trans (b.relevant _)
  FeqF t := (a.FeqF t).trans (b.FeqF _)
  Gterm t := (a.Gterm t).trans (b.Gterm _)
  atP p := LocIso.trans (a.atP p) (b.atP p)
  ePl := a.ePl.trans b.ePl
  BBne t q := (a.BBne t q).trans (b.BBne _ _)
  generic t := (a.generic t).trans (b.generic _)
  eP u u' := (a.eP u u').trans (b.eP u u')
  pfst p := (congrArg (b.eT _ _) (a.pfst p)).trans (b.pfst _)
  psnd p := (congrArg (b.eT _ _) (a.psnd p)).trans (b.psnd _)
  s0 p := (a.s0 p).trans (b.s0 _)
  scalarPair p := (a.scalarPair p).trans (b.scalarPair _)
  pval p := (a.pval p).trans (b.pval _)
  ptOf t := (a.ptOf t).trans (b.ptOf _)
  cTerm t := (a.cTerm t).trans (b.cTerm _)
  massPair p := (a.massPair p).trans (b.massPair _)
  meanCount := a.meanCount.trans b.meanCount

end Trans

section Move

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)

theorem SRest.exists_re_ofDiv {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P)
    {F' : ∀ u, Forms0 (reD D (New.ofDiv D N hh)) u} (h : SameForms0LevelsAndValues (New.ofDiv D N hh) F F')
    (hF : FinX (reY (New.ofDiv D N hh) P.Y)) :
    ∃ S' : SRest (P.re (New.ofDiv D N hh) h hF), HEq S'.j S.j := by
  obtain ⟨e, heH, heC⟩ := sIso_reD D (New.ofDiv D N hh) P.X P.Y P.fin hF
  let hI' : SIso (reD D (New.ofDiv D N hh)).s (sOf (P.re (New.ofDiv D N hh) h hF).fin) := (by with_unfolding_all exact (SIso.trans S.hI e :))
  let aT : Formalism.MainNotions.S.AutTie (reD D (New.ofDiv D N hh)) (P.re (New.ofDiv D N hh) h hF).X.B
      (P.re (New.ofDiv D N hh) h hF).X.pl :=
    ⟨(by with_unfolding_all exact (S.autTie.n_eq :)), (by with_unfolding_all exact (S.autTie.f_eq :)), (by with_unfolding_all exact (S.autTie.rd_eq :)), (by with_unfolding_all exact (S.autTie.eps_eq :)),
      (by with_unfolding_all exact (S.autTie.lam_eq :)), (by with_unfolding_all exact (S.autTie.ds :)), (by with_unfolding_all exact (S.autTie.low :)), (by with_unfolding_all exact (S.autTie.g_eq :)),
      (by with_unfolding_all exact (S.autTie.g0_eq :)), (by with_unfolding_all exact (S.autTie.D_eq :)), (by with_unfolding_all exact (S.autTie.Dstar_eq :))⟩
  let jj : (reD D (New.ofDiv D N hh)).what₂.EE ≃ₗᵢ[ℂ] EEC (P.re (New.ofDiv D N hh) h hF).X
      (P.re (New.ofDiv D N hh) h hF).G := (by with_unfolding_all exact (S.j :))
  have lT : Formalism.L2.SG.Pf.LocCP.LocTied (reD D (New.ofDiv D N hh)) := (by with_unfolding_all exact (S.locTied :))
  have cP : ∀ (u : (reD D (New.ofDiv D N hh)).what₂.Word) (x : (reD D (New.ofDiv D N hh)).s.Cu u),
      colDict (P.re (New.ofDiv D N hh) h hF).X ((P.re (New.ofDiv D N hh) h hF).tr u)
        (P.re (New.ofDiv D N hh) h hF).Y.hK ((P.re (New.ofDiv D N hh) h hF).into u)
        ((P.re (New.ofDiv D N hh) h hF).bij u) (hI'.eCu u x) = (reD D (New.ofDiv D N hh)).s_Cu u x := by
    intro u x
    have hx : hI'.eCu u x = ((by with_unfolding_all exact (S.hI.eCu u x :))) := (by with_unfolding_all exact (congrArg (fun f => f (S.hI.eCu u x)) (eq_of_heq (heC u)) :))
    rw [hx]
    apply Subtype.ext
    exact (by with_unfolding_all exact ((colDictL_reTr (New.ofDiv D N hh) (P.tr u) (h u).2.1 (h u).2.2 P.Y.hK
      (toCu (cs := P.Y.cs u) (hinj := P.fin.shInj u) P.X P.Y.hK (S.hI.eCu u x))).trans (congrArg Subtype.val (S.colPin u x)) :))
  have rP : ∀ x : (reD D (New.ofDiv D N hh)).what₂.EE,
      hI'.eHH ((reD D (New.ofDiv D N hh)).sEE x) =
        conjHH (P.re (New.ofDiv D N hh) h hF).X (P.re (New.ofDiv D N hh) h hF).G (jj x) := by
    intro x
    exact (by with_unfolding_all exact ((congrArg (fun f => f (S.hI.eHH (D.sEE x))) (eq_of_heq heH)).trans (S.rowPin x) :))
  exact ⟨⟨hI', aT, cP, jj, rP, lT⟩, (by with_unfolding_all exact (HEq.refl S.j :))⟩

end Move

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualMeasureGlobalConstRankOnlyStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualMeasure_global_const_rank_only : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ), ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ (ψ : AddChar (AF F) ℂ) (J : Matrix (Fin M) (Fin M) E), IsCharAF F ψ → IsHermND σ J → ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F)) (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi → SdR (Ainf F) (psiInf F ψ) νi → (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) → (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) → ∃ (ri ti : ℝ≥0) (r t : HeightOneSpectrum (𝓞 F) → ℝ≥0), μi = ri • tupMeas s.lamI 1 M ∧ νi = ti • s.nuI ∧ (∀ v, μv v = r v • tupMeas (s.lamV v) 1 M) ∧ (∀ v, νv v = t v • s.nuV v) ∧ ri ≠ 0 ∧ ti ≠ 0 ∧ (∀ v, r v ≠ 0) ∧ (∀ v, t v ≠ 0) ∧ (Function.mulSupport fun v => r v / t v).Finite ∧ ri / ti * ∏ᶠ v, r v / t v = κ := by
  first | exact @GlobalTheory.GaugeSdMain.selfDual_const | exact GlobalTheory.GaugeSdMain.selfDual_const | (intros; apply GlobalTheory.GaugeSdMain.selfDual_const <;> assumption)
end

