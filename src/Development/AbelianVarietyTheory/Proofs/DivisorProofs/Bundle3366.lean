import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3154
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NadelVanishingPairsOfPrincipalisation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0618
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0769
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapUniqueness
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flatSec_unit_at_bdry_height_one : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr
  haveI hN : IsNoetherianRing A := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  let P0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hbotR : ξ P0 ∈ Set.range Y.j := hcov.2.2.2.2.1 hbot
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.integral_model_map_extension hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ P0 hbotR
  obtain ⟨T, iT, hiT, hloc, hval⟩ := GlobalTheory.T.section_value_unit_at_boundary_height_one_prime hP1 hP2 hP3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov
    A ξ β hξ hs hpu hbot g e U₁ h₁ U₂ h₂ htan heig hd₁ hd₂ 𝔭 hht hnr

  set gT : A →+* T.Fr := (algebraMap T.V T.Fr).comp (iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) with hgT
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  have hgTinj : Function.Injective gT :=
    (IsFractionRing.injective T.V T.Fr).comp (hiT.comp hAinj)
  have hunits : ∀ b : P0.asIdeal.primeCompl, IsUnit (gT b) := fun b =>
    isUnit_iff_ne_zero.2 fun h => b.2 (by
      have : (b : A) = 0 := hgTinj (by rw [h, map_zero])
      simp [P0, this])
  let κ : Localization.AtPrime P0.asIdeal →+* T.Fr := IsLocalization.lift hunits
  have hκ : κ.comp (algebraMap A _) = gT := IsLocalization.lift_comp hunits
  obtain ⟨w, hw⟩ := hval (κ u₀) fun k _ φ => by
    have h0 := hu₀ k (φ.comp κ)
    rwa [RingHom.comp_assoc, hκ] at h0
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective P0.asIdeal.primeCompl (u₀ : Localization.AtPrime P0.asIdeal)
  have h1 : gT a = gT b * algebraMap T.V T.Fr w :=
    (IsLocalization.lift_mk'_spec _ _ _ _).1 (by simp only at hab; rw [hab, hw])
  have h2 : iT (algebraMap A _ a) = iT (algebraMap A _ b) * w := by
    apply IsFractionRing.injective T.V T.Fr
    simpa [hgT, map_mul] using h1
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_local_unit_of_dvr_unit A 𝔭 hht T.V iT hiT hloc a b ⟨w, h2⟩
  refine ⟨u, fun k _ φ => ?_⟩
  set ψ : A →+* k := φ.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) with hψ
  by_cases hk : Function.Injective ψ
  ·
    have hunits' : ∀ b : P0.asIdeal.primeCompl, IsUnit (ψ b) := fun b =>
      isUnit_iff_ne_zero.2 fun h => b.2 (by
        have : (b : A) = 0 := hk (by rw [h, map_zero])
        simp [P0, this])
    let φ' : Localization.AtPrime P0.asIdeal →+* k := IsLocalization.lift hunits'
    have hφ' : φ'.comp (algebraMap A _) = ψ := IsLocalization.lift_comp hunits'
    have hle' : 𝔭.asIdeal.primeCompl ≤ P0.asIdeal.primeCompl.comap (RingHom.id A) := fun x hx hx0 => by
      apply hx
      have : x = 0 := by simpa [P0] using hx0
      rw [this]; exact 𝔭.asIdeal.zero_mem
    let mp : Localization.AtPrime 𝔭.asIdeal →+* Localization.AtPrime P0.asIdeal :=
      IsLocalization.map _ (RingHom.id A) hle'
    have hφ : φ = φ'.comp mp := by
      apply IsLocalization.ringHom_ext 𝔭.asIdeal.primeCompl
      rw [RingHom.comp_assoc, IsLocalization.map_comp, RingHom.comp_id, hφ']
    have hmu : mp u = u₀ := by
      rw [← hab, IsLocalization.eq_mk'_iff_mul_eq]
      have := congrArg mp hu
      rw [map_mul] at this
      simpa [mp, IsLocalization.map_eq] using this
    have e2 : φ u = φ' u₀ := by
      rw [← hmu]
      exact congrArg (fun f : Localization.AtPrime 𝔭.asIdeal →+* k => f u) hφ
    rw [e2, ← hφ']
    exact hu₀ k φ'
  ·
    intro _ yy hyy
    exfalso
    apply hnr
    have hker : RingHom.ker ψ = 𝔭.asIdeal := by
      have hle : RingHom.ker ψ ≤ 𝔭.asIdeal := fun x hx => by
        by_contra hx'
        have hu' : IsUnit (algebraMap A (Localization.AtPrime 𝔭.asIdeal) x) :=
          IsLocalization.map_units _ (⟨x, hx'⟩ : 𝔭.asIdeal.primeCompl)
        have := (hu'.map φ).ne_zero
        exact this hx
      have hne : RingHom.ker ψ ≠ ⊥ := fun h => hk ((RingHom.injective_iff_ker_eq_bot ψ).2 h)
      by_contra hne'
      have hlt : RingHom.ker ψ < 𝔭.asIdeal := lt_of_le_of_ne hle hne'
      have hlt0 : (⊥ : Ideal A) < RingHom.ker ψ := bot_lt_iff_ne_bot.2 hne
      have a1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt0
      have a2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, hht] at *
      rw [zero_add] at a1
      have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add a1 le_rfl).trans a2
      exact absurd this (by decide)
    have hpt : (spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) = 𝔭 := PrimeSpectrum.ext hker
    refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    calc Y.j (yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k))
        = (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap ψ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      _ = ξ ((spMap ψ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)) := Scheme.Hom.comp_apply _ _ _
      _ = ξ 𝔭 := by rw [hpt]

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvrStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → UniversallyOpen f → GeometricallyIrreducible f → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProperDvr.isProper_of_specialFibre | exact GlobalTheory.FibreProperDvr.isProper_of_specialFibre | (intros; apply GlobalTheory.FibreProperDvr.isProper_of_specialFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAlgebraisedPowersCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_algebraised_powers_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB) → ∀ (p q : ℤ) (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ (w : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) p) (A.pull (b e))) (w' : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) q) (A'.pull (b e))), (∀ e, (w e).IsGen ∧ (w' e).IsGen) → (∀ e z k l' l, b e z ∈ A.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ p) → (∀ e z k l' l, b e z ∈ A'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l → Geo.Tor.gw (w' e) (𝟙 _) z k l = Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ q) → LBIso (GlobalTheory.AbLaw.pw A q) (GlobalTheory.AbLaw.pw A' p) := by
  first | exact @GlobalTheory.FormalAlg.lbIso_pw_cross | exact GlobalTheory.FormalAlg.lbIso_pw_cross | (intros; apply GlobalTheory.FormalAlg.lbIso_pw_cross <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := GlobalTheory.T.mumford_thickening_endomorphism_maps_sections R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := GlobalTheory.T.exists_genericFibreHom_of_formalSectionRatios R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingPairsOfPrincipalisationStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nadel_vanishing_pairs_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair := by
  first | exact @GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | exact GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation | (intros; apply GlobalTheory.Discrepancy.nadelVanishingPair_of_principalisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsionStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  first | exact @GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | exact GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one | (intros; apply GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModuleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), ‖((deg (A := A) (B := A) f : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  first | (exact @GlobalTheory.AV.AbVar.norm_deg_eq_norm_det) | (exact GlobalTheory.AV.AbVar.norm_deg_eq_norm_det) | (intros; apply GlobalTheory.AV.AbVar.norm_deg_eq_norm_det  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDataWeightVectorFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage4

theorem stage4 : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  intro P hRSW hHL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hT hG hM hRow hLv hPos
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod P.q9
  obtain ⟨hOk, hGU, hGE, hBlk, hA, _hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  obtain ⟨hLT, hLTB, _hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  obtain ⟨hLevW, hPartsW, hHecke, hSep, _hTr⟩ := GlobalTheory.T.lift_test_positive_levels_kappa P R F hT hM hG.unif hLT hLv hPos
  have hOnto := GlobalTheory.T.partial_L_function_of_hypotheses P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hRSW hHL (s := 1) R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hOk.2 hGE hG.unif
  obtain ⟨fw, hBar⟩ := hG.fw
  have hGal : (R.toCx3 F).GalD F.cr false :=
    GlobalTheory.T.doubling_method_consequence hE P.q1 P.q2 P.q13 P.q11 P.q9 P.q14 P.q10 P.q7 P.q4 T R F κ v₀ O 1 hT.ok hSep hT.char hT.ex hT.params
      hT.phs hT.std fw hBar hG.ioExt hG.pins (fun i => (hG.oneMap i).1) hG.phase hOk.1 hOk.2 hHecke hGU hGE hBlk hRow hLT hLTB
      hOnto hPos.1 hPos.2 hG.unif hLevW hA hPartsW
  exact ⟨hGal, GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity R F hT.ok hT.char hT.ex hPos hGal hG.unif hLTB hGE⟩

end GlobalTheory.Stage4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundles
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.RecSec

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem finsum_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i (A.tens C)) (B.logSec b) z =
      ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i A) (B.logSec b) z +
        ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i C) (B.logSec b) z := by
  have : CompactSpace X := compactSpace_of_projOver hp
  have hfin := Δ.finite_support_mult
  have hsub (G : X → ℝ) : (Function.support fun z => (Δ.mult z : ℝ) * G z).Finite :=
    hfin.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h0; exact hz (by simp [h0])
  rw [← finsum_add_distrib (hsub _) (hsub _)]
  refine finsum_congr fun z => ?_
  by_cases h0 : Δ.mult z = 0
  · simp [h0]
  have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
  have hcl : topologicalKrullDim (closure ({z} : Set X)) = e :=
    (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hz1
  have h₁ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i A) z hcl).2.2.2 B b (hb z h0)
  have h₂ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i C) z hcl).2.2.2 B b (hb z h0)
  rw [GlobalTheory.T.pointClosureIntegral_update_tensor_additive F X p σ hp e L i A C (B.logSec b) z h₁ h₂, mul_add]

theorem side_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (N M : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    side N (Function.update L i (A.tens C)) (M.logSec s) (B.logSec b) Δ =
      side N (Function.update L i A) (M.logSec s) (B.logSec b) Δ +
        side N (Function.update L i C) (M.logSec s) (B.logSec b) Δ := by
  simp only [side, Fin.cons_update]
  have hA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ A) M s hs
  have hC := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ C) M s hs
  rw [(GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hp (e + 1) (Fin.cons N L) i.succ A C (M.logSec s) hA hC).2,
    finsum_update_tens P hp hdim Δ B b hb L i A C]
  ring

theorem reciprocity_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro P F _ X _ _ p σ e hp hdim L M N s hs t ht hcod hgM hgN
  classical
  let Df : (Fin e → MLine p σ) → ℝ := fun L =>
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) -
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)
  have hbt : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_left fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hbs : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_right fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hadd : ∀ (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ),
      Df (Function.update L i (A.tens C)) = Df (Function.update L i A) + Df (Function.update L i C) := by
    intro L i A C
    simp only [Df, side_update_tens P hp hdim N M s hs _ N t hbt L i A C,
      side_update_tens P hp hdim M N t ht _ M s hbs L i A C]
    ring
  have hpos : ∀ L : Fin e → MLine p σ, (∀ i, (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := fun L hL =>
    sub_eq_zero.2 (GlobalTheory.T.generatedBundles_reciprocity_semiPositive P F X p σ e hp hdim L M N s hs t ht hcod hL hgM hgN)
  have key : ∀ (S : Finset (Fin e)) (L : Fin e → MLine p σ),
      (∀ i, i ∉ S → (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun L hL => hpos L fun i => hL i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro L hL
      obtain ⟨Q, hQ, hAQ⟩ := GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle F X p σ hp (e + 1) (L a)
      have hgood : ∀ R : MLine p σ, R.φ.SemiPosReg (e + 1) → Df (Function.update L a R) = 0 := by
        intro R hR
        refine ih _ fun i hi => ?_
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hR
        · rw [Function.update_of_ne hia]
          exact hL i (by simp [hia, hi])
      have h := hadd L a (L a) Q
      rw [hgood _ hAQ, hgood _ hQ, Function.update_eq_self] at h
      linarith
  have := key Finset.univ L fun i hi => absurd (Finset.mem_univ i) hi
  exact sub_eq_zero.1 this

end GlobalTheory.RecSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinear
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit k (c.x n i)) = _
    rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit k' (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit k' (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairs
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit k (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothInjectiveFamilyLiftsSmallArtinianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothInjectiveFamily_lifts_small_artinian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u := by
  first | exact @GlobalTheory.DualCon.same_lift_small | exact GlobalTheory.DualCon.same_lift_small | (intros; apply GlobalTheory.DualCon.same_lift_small <;> assumption)
end

