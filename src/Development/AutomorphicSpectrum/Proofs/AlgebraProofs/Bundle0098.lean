import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0093
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Num.TopRel

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem relations : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ ϖ hϖ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hD Lie W Om OmHT hB lie om hflag
  have hck := GlobalTheory.T.lattice_family_ckRelations O Ω K ι x d hmod hfn p hp w χ φ D hD Lie W Om OmHT hB
  have hp0 : (p : O) ≠ 0 := hD.char.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, he⟩ := hD.char.2.1
    have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    rw [zero_pow h1] at he
    exact hp0 (by
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hu.ne_zero
      · exact h)
  have hsame : ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ
    constructor
    · intro c hc
      obtain ⟨h1, h2, -, -⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h1, h2]
      refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
      · simpa using hinc.1 hv
      · exact hinc.2.1 hv
    · intro c hc
      obtain ⟨-, -, h3, h4⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h3, h4]
      refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · exact hinc.2.2.2 hv
      · simpa using hinc.2.2.1 hv
  exact GlobalTheory.T.uniformizer_model_perm_module_lattice O Ω K ι x ϖ hϖ d hmod p hp0 φ (VL := fun τ => Fin (r τ) → Ω)
    (VO := fun τ => Fin (s τ) → Ω) Lie W Om OmHT hsame hck lie om hflag

end GlobalTheory.CompanionTheory.Ar.Num.TopRel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.CommAlg.OrderEtale

theorem formallyUnramified_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] [Field K] [Algebra k K] [IsFractionRing k K] [Algebra ℤ K] :
    Algebra.FormallyUnramified ℤ K := by
  have hinj : Function.Injective (algebraMap k K) := IsFractionRing.injective k K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (RingHom.ext_int _ _)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := k) (A := K) (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hint : ∀ a : k, IsIntegral ℚ (algebraMap k K a) := fun a =>
    IsIntegral.tower_top (A := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap (B := K))
  haveI : Algebra.IsAlgebraic ℚ K := by
    constructor
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k) x
    rw [div_eq_mul_inv]
    have hb : IsIntegral ℚ (algebraMap k K b)⁻¹ :=
      (IsAlgebraic.inv_iff.mpr (hint b).isAlgebraic).isIntegral
    exact ((hint a).mul hb).isAlgebraic
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallyUnramified.comp ℤ ℚ K

theorem isUnramifiedAt_bot (k : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] : Algebra.IsUnramifiedAt ℤ (⊥ : Ideal k) := by
  have hM : (⊥ : Ideal k).primeCompl = nonZeroDivisors k := by
    ext x
    simp [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsFractionRing k (Localization.AtPrime (⊥ : Ideal k)) := by
    unfold IsFractionRing
    rw [← hM]
    infer_instance
  letI : Field (Localization.AtPrime (⊥ : Ideal k)) := IsFractionRing.toField k
  exact formallyUnramified_fractionRing k (Localization.AtPrime (⊥ : Ideal k))

theorem exists_etale_away (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  have hU : IsOpen (Algebra.unramifiedLocus ℤ k) := Algebra.isOpen_unramifiedLocus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∈ Algebra.unramifiedLocus ℤ k :=
    isUnramifiedAt_bot k
  obtain ⟨V, ⟨f, rfl⟩, hfV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hU
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hfV
  have hint : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hne : Ideal.comap (algebraMap ℤ k) (Ideal.span {f}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, eq_intCast] at hm
  have hmN : (m : k) ∣ ((m.natAbs : ℤ) : k) := map_dvd (Int.castRingHom k) (Int.dvd_natAbs.mpr dvd_rfl)
  have hfN : f ∣ ((m.natAbs : ℕ) : k) := by
    have := hm.trans hmN
    simpa using this
  obtain ⟨g, hg⟩ := hfN
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm0, ?_⟩
  have hS : Algebra.FormallyUnramified ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ hVU
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left f g
  have hfree : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  have hflat : Module.Flat ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have := IsLocalization.flat (Localization.Away ((m.natAbs : ℕ) : k))
      (Submonoid.powers ((m.natAbs : ℕ) : k))
    exact Module.Flat.trans ℤ k _
  have hfp : Algebra.FinitePresentation ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have : Algebra.FinitePresentation ℤ k := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have := IsLocalization.Away.finitePresentation (S := Localization.Away ((m.natAbs : ℕ) : k))
      ((m.natAbs : ℕ) : k)
    exact Algebra.FinitePresentation.trans ℤ k _
  have hE : Algebra.Etale ℤ (Localization.Away ((m.natAbs : ℕ) : k)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have h2 : Int.castRingHom (Localization.Away ((m.natAbs : ℕ) : k)) =
      algebraMap ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := RingHom.ext_int _ _
  rw [h2, RingHom.etale_algebraMap]
  exact hE

end GlobalTheory.CompanionTheory.CommAlg.OrderEtale
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.EtaleCoord

theorem etale_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (hf : f.Etale) (h : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars R S T

theorem etale_eval₂Hom_iff_int : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  intro k A _ _ N hN φ hu D x
  let ι : k →+* Localization.Away (N : k) := algebraMap k _
  have hφN : IsUnit (φ (N : k)) := by simpa using hu
  let ψ : Localization.Away (N : k) →+* A := IsLocalization.Away.lift (N : k) hφN
  have hψ : ψ.comp ι = φ := by
    ext a
    simp [ψ, ι]
  have hι : ι.Etale := by
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (N : k)
  have ha : (MvPolynomial.map (σ := Fin D) ι).Etale := etale_mvPolynomial_map_of_etale ι hι
  have hb : (MvPolynomial.map (σ := Fin D) (Int.castRingHom (Localization.Away (N : k)))).Etale :=
    etale_mvPolynomial_map_of_etale _ hN
  let Θ := MvPolynomial.eval₂Hom ψ x
  have e1 : MvPolynomial.eval₂Hom φ x = Θ.comp (MvPolynomial.map ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ, ← hψ]
    · intro j
      simp [Θ]
  have e2 : MvPolynomial.eval₂Hom (Int.castRingHom A) x =
      Θ.comp (MvPolynomial.map (Int.castRingHom (Localization.Away (N : k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ]
    · intro j
      simp [Θ]
  rw [e1, e2]
  exact ⟨fun h => RingHom.Etale.stableUnderComposition _ _ hb (etale_of_comp _ _ ha h),
    fun h => RingHom.Etale.stableUnderComposition _ _ ha (etale_of_comp _ _ hb h)⟩

end GlobalTheory.CompanionTheory.Ar.EtaleCoord
end

