import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
section
open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.SncDescent

theorem eq_of_le_span_singleton {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t : R} (ht : t ∈ maximalIdeal R) {Q : Ideal R} [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (hle : Q ≤ Ideal.span {t}) : Q = Ideal.span {t} := by
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra htQ
  refine h0 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) Q
    (IsNoetherian.noetherian _) (fun x hx => ?_) ?_)
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 (hle hx)
    exact Submodule.smul_mem_smul ht ((hQ.mem_or_mem hx).resolve_left htQ)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

theorem exists_rsp {A : Type} [CommRing A] [IsRegularLocalRing A] {m : ℕ} (p : Fin m → A)
    (hp : ∀ i, p i ∈ maximalIdeal A)
    (hind : ∀ a : Fin m → A, ∑ i, a i * p i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ ∏ i ∈ T, r i = ∏ i, p i := by
  classical
  let τ : Fin m → maximalIdeal A := fun i => ⟨p i, hp i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * p j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  let e := Fintype.equivFin (J ⊕ Fin m)
  refine ⟨_, Sum.elim t p ∘ e.symm, Finset.univ.map ⟨e ∘ Sum.inr, e.injective.comp Sum.inr_injective⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [e.symm.surjective.range_comp, Set.Sum.elim_range]
    exact hs
  · rw [hd, Fintype.card_sum]
  · rw [Finset.prod_map]
    simp

theorem exists_rsp_of_flat {A R : Type} [CommRing A] [IsRegularLocalRing A] [CommRing R] [IsRegularLocalRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) {m : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ∈ maximalIdeal R)
    (hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R)
    (D : Ideal A) (hD : D.map φ = Ideal.span {∏ i, t i})
    (hinj : ∀ i i', (Ideal.span {t i}).comap φ = (Ideal.span {t i'}).comap φ → i = i') :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  classical
  algebraize [φ]
  have hloc : IsLocalHom (algebraMap A R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : algebraMap A R a ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  have hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective A R
  have : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have := isRegularRing_of_isRegularLocalRing A
  have : UniqueFactorizationMonoid A := uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE A
  have hprime : ∀ i, Prime (t i) := fun i => prime_of_not_mem_sq (ht i) fun h => by
    have := hind (Pi.single i 1) (by simpa [Pi.single_apply] using h) i
    simp at this
  have h0 : ∏ i, t i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hprime i).ne_zero
  have hDt : ∀ d ∈ D, ∀ i, t i ∣ φ d := fun d hd i =>
    (Finset.dvd_prod_of_mem t (Finset.mem_univ i)).trans
      (Ideal.mem_span_singleton.1 (hD ▸ Ideal.mem_map_of_mem φ hd))
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => h0 ?_
    rw [h, Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hD
    exact hD
  have key : ∀ i, ∃ p : A, Prime p ∧ (Ideal.span {t i}).comap φ = Ideal.span {p} := fun i => by
    have hP : (Ideal.span {t i}).IsPrime := (Ideal.span_singleton_prime (hprime i).ne_zero).2 (hprime i)
    have hne : (Ideal.span {t i}).comap φ ≠ ⊥ := fun h => hd0 (by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton.2 (hDt d hd i))
    obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hne
    refine ⟨p, hpp, ?_⟩
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).2 hpp
    have : (Ideal.span {t i}).LiesOver ((Ideal.span {t i}).comap φ) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.span {p})
      (q := (Ideal.span {t i}).comap φ) (Ideal.span {t i}) ((Ideal.span_singleton_le_iff_mem _).2 hp)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      have : p ∈ (⊥ : Ideal R).comap φ := hQo.over.le (Ideal.mem_span_singleton_self p)
      exact hpp.ne_zero (hφ (by simpa using this))
    rw [← eq_of_le_span_singleton (ht i) hQ0 hQ]
    exact hQo.over.symm
  choose p hp hP using key
  have htp : ∀ i, t i ∣ φ (p i) := fun i =>
    Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 ((hP i).ge (Ideal.mem_span_singleton_self _)))
  choose u hu using htp
  have hle : D ≤ Ideal.span {∏ i, p i} := fun x hx => by
    rw [Ideal.mem_span_singleton]
    refine Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij => ?_) fun i _ => ?_
    · refine (hp i).irreducible.isRelPrime_iff_not_dvd.2 fun h => hij (hinj i j ?_)
      rw [hP, hP, Ideal.span_singleton_eq_span_singleton]
      exact (hp i).irreducible.associated_of_dvd (hp j).irreducible h
    · rw [← Ideal.mem_span_singleton, ← hP]
      exact Ideal.mem_span_singleton.2 (hDt x hx i)
  have hprod : φ (∏ i, p i) = (∏ i, t i) * ∏ i, u i := by
    simp only [map_prod, hu, Finset.prod_mul_distrib]
  have hU : IsUnit (∏ i, u i) := by
    have := Ideal.map_mono (f := φ) hle
    rw [hD, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton, hprod] at this
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left h0).1 (by simpa using this))
  have hu1 : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) hU
  obtain ⟨n, r, T, hr, hT⟩ := exists_rsp p (fun i => (mem_maximalIdeal _).2 (hp i).not_isUnit) fun a ha i => by
    have h1 := Ideal.mem_map_of_mem φ ha
    rw [Ideal.map_pow, hm, map_sum] at h1
    have h2 := hind (fun j => φ (a j) * u j) (by
      convert h1 using 2 with j
      rw [map_mul, hu]; ring) i
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun h => h2 ((h.map φ).mul (hu1 i))
  refine ⟨n, r, T, hr, ?_⟩
  have h3 : D.map (algebraMap A R) = (Ideal.span {∏ i, p i}).map (algebraMap A R) := by
    change D.map φ = (Ideal.span {∏ i, p i}).map φ
    rw [hD, Ideal.map_span, Set.image_singleton, hprod, Ideal.span_singleton_mul_right_unit hU]
  rw [hT, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) D, h3, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem coeff_single_eq_zero {k σ : Type} [Field k] {g : MvPowerSeries σ k}
    (hg : g ∈ maximalIdeal (MvPowerSeries σ k) ^ 2) (s : σ) :
    MvPowerSeries.coeff (Finsupp.single s 1) g = 0 := by
  classical
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add, ha, hb, add_zero]
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot] at ha hb
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ, ha, hb]

theorem exists_rsp_of_isEtaleCompletion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  intro A _ _ _ k _ m e φ D hφ hD hinj
  classical
  have hR : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k _
  have hA := (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion φ hφ).1
  refine exists_rsp_of_flat φ hφ.1 hφ.2.1 (bdParam k m e) (fun i => ?_) (fun a ha i => ?_) D hD hinj
  · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
    simp
  · have h := coeff_single_eq_zero ha (Sum.inl i)
    rw [map_sum, Finset.sum_eq_single i] at h
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot]
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial] at h
      simpa using h
    · intro j _ hj
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, if_neg]
      simp [Finsupp.single_le_iff, Finsupp.single_apply, hj.symm]
    · simp

end GlobalTheory.SncDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem reads_linear_injective_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx f f' φ φ' hf hf'
  obtain ⟨-, -, hlin⟩ := thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hS hev x hx φ hf.1
  obtain ⟨hl, hinj⟩ := hlin φ' hf'.1
  obtain ⟨-, -, -, -, hp⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x
  obtain ⟨p, -, hp, -⟩ := hp hx
  refine ⟨fun a b => ⟨(hl a b).1, fun w hw => ?_⟩, fun h => hinj ?_, fun h h' e => ?_⟩
  · rw [(hl a b).2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.2 w hw, hf'.2 w hw]
    ring
  · funext z
    have h1 := hf.2 (p z) (hp z).1
    have h2 := hf'.2 (p z) (hp z).1
    rw [h, h2, (hp z).2] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  · refine theta_eq_of_real D ψ V W hψ f f' h h' fun w hw => ?_
    rw [hf.2 w hw, hf'.2 w hw, e]

theorem IsONFr.mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
    (hx : IsONFr X x) : x ∈ X.dom :=
  PIW.FdPA.orthonormal_domain r X x hx

theorem reads_linear_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx
  exact reads_linear_injective_dom D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx.mem_dom

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMove
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

theorem exists_entire_ratio {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (W : ι → Set V)
    (hW : ∀ i, IsOpen (W i)) (hcov : ∀ w, ∃ i, w ∈ W i) (f f' : ι → V → ℂ) (c : ι → ι → V → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (W i)) (hd' : ∀ i, DifferentiableOn ℂ (f' i) (W i))
    (hn : ∀ i, ∀ w ∈ W i, f i w ≠ 0) (hn' : ∀ i, ∀ w ∈ W i, f' i w ≠ 0)
    (hc : ∀ i j w, w ∈ W i → w ∈ W j → f i w = c i j w * f j w)
    (hc' : ∀ i j w, w ∈ W i → w ∈ W j → f' i w = c i j w * f' j w) :
    ∃ ρ : V → ℂ, Differentiable ℂ ρ ∧ (∀ w, ρ w ≠ 0) ∧ ∀ i, ∀ w ∈ W i, f' i w = ρ w * f i w := by
  choose J hJ using hcov
  have key : ∀ i, ∀ w ∈ W i, f' i w = f' (J w) w / f (J w) w * f i w := fun i w h => by
    have := hn _ _ (hJ w)
    rw [hc i (J w) w h (hJ w), hc' i (J w) w h (hJ w)]
    field_simp
  refine ⟨_, fun w => ?_, fun w => div_ne_zero (hn' _ _ (hJ w)) (hn _ _ (hJ w)), key⟩
  refine (((hd' (J w)).mul ((hd (J w)).inv (hn _))).congr fun w' h => ?_).differentiableAt ((hW _).mem_nhds (hJ w))
  exact (eq_div_of_mul_eq (hn _ _ h) (key _ _ h).symm).trans (div_eq_mul_inv _ _)

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in

theorem det_eq_sq_mul_of_theta_ratio (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ))
    (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ)
    (hbas : ∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hN : ∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) (hP : ∀ a, P' a = P (gam a))
    (hn : ∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1)
    (hn' : ∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1)
    (hτ : τ ∈ SiegelH (Fin g)) (hτ' : τ' ∈ SiegelH (Fin g)) (hu : IsUnit h.det)
    (h8 : ∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j))
    (hdet : (4 : ℤ) ∣ N.toBlocks₁₁.det - 1)
    (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0) (hρ1 : ρ 0 = 1) (hκ : κ ≠ 0)
    (hrel : ∀ z, thetaChar τ' c₁ c₂ (h' *ᵥ z) * ρ z = κ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    h.det = κ ^ 2 * h'.det := by
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H D g bas gam N
    P P' h h' τ τ' hbas hiso hN hP hn hn' hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := GlobalTheory.theta_sq_transform_level_eight g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => h⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => ρ (h⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel (h⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  rw [hde, hκ2]

set_option maxHeartbeats 1600000 in

theorem theta_move_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y z y' gam A ρ ν t hκ hκ' hy hz hiso hA hdA hPP hex hmv hbor
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z.x = y.x ≫ ρ := hbor.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hbor
  clear hmv
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hu, -, hv⟩ := hy
  obtain ⟨hu', -, hv'⟩ := hz
  obtain ⟨hdu, hsy, hpos, hn⟩ := T.norm b hb
  obtain ⟨hdu', hsy', hpos', hn'⟩ := T.norm b' hb'
  have hd : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b, w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b)) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b, w)) (by fun_prop) (fun w h => ⟨hb, h⟩)
  have hd' : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b', w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b')) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b', w)) (by fun_prop) (fun w h => ⟨hb', h⟩)
  have hne := fun j w => T.fr_ne j b w hb
  have hne' := fun j w => T.fr_ne j b' w hb'
  have hc := fun j j' w => T.fr_coc j j' b w hb
  have hc' := fun j j' w => T.fr_coc j j' b' w hb'
  have h0 := fun j => T.fr_rig j b hb
  have h0' := fun j => T.fr_rig j b' hb'
  generalize T.Pf (T.co b) = P at *
  generalize T.Pf (T.co b') = P' at *
  have hcov2 : ∀ w, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2 := fun w => by
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex k P w).left
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex k P w).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' w hw => by
    rw [hex]; exact ((o1 _ _ _).1 hw).1
  have tr2 : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' w hw => ((o1 _ _ _).1 hw).2
  have hw0 : ∀ w, (F.ex k P w).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P w)).trans hu.symm
  have hw0' : ∀ w, (F.ex k P' w).left ≫ Xo.univ.t.G.hom = (z.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P' w)).trans hu'.symm
  have hz0 : (F.ex k P 0).left = (y.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker k P hp 0).2 (zero_mem _), hu]
    rfl
  obtain ⟨ρf, hρd, hρ0, hfr⟩ := exists_entire_ratio
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {w | ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2})
    (fun j => GlobalTheory.FamilyUnif_isOpen_ex F k P hp _) hcov2
    (fun q w => valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) (fun q w => T.fr q.1 (b', w))
    (fun q q' w => valAt' ((F.ex k P w).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F k P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
      fun w hw => ⟨Set.mem_univ _, hw⟩).mul ((hd q.2).mono fun w hw => tr2 _ _ w hw))
    (fun q => (hd' q.1).mono fun w hw => tr _ _ w hw)
    (fun q w hw => mul_ne_zero (o2 _ _ _ hw) (hne _ w (tr2 _ _ w hw)))
    (fun q w hw => hne' _ w (tr _ _ w hw))
    (fun q q' w h1 h2 => by
      rw [hc q.2 q'.2 w ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ w h1, tr2 _ _ w h2⟩), ← mul_assoc,
        o3 _ _ _ _ _ h1 h2, mul_assoc])
    (fun q q' w h1 h2 => by
      have e2 := hc' q.1 q'.1 w ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
      rw [hex] at e2
      exact e2)
  have hρ1 : ρf 0 = 1 := by
    obtain ⟨q, hq⟩ := hcov2 0
    have e1 := hfr q 0 hq
    have e2 : T.fr q.1 (b', 0) = valAt' (F.ex k P 0).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, 0) := by
      rw [h0 _ (tr2 _ _ 0 hq), h0' _ (tr _ _ 0 hq), ← hu', hxρ]
      exact (o4 _ _ _ _ hz0 hq).trans (congrArg (fun x : Sp ℂ ⟶ Xo.X => _ * valAt' x _ _) hu)
    exact (mul_eq_right₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ 0 (tr2 _ _ 0 hq)))).1 (e1.symm.trans e2)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z.x y'.x z.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  generalize Formalism.L2.PjFree.toC (t none : CAt σ) = t₀ at *
  have hrel : ∀ w, thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * ρf w =
      κ / (t₀ * κ') * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) := fun w => by
    obtain ⟨q, hq⟩ := hcov2 w
    let p : Over.mk (y.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex k P w).left (hw0 w)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 w _ e1 e2 (tr2 _ _ w hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex k P' w).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 w pt h1 h2 (tr _ _ w hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex w)) h2 hq)
    have hval2 : valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) *
        (κ * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) * T.fr q.2 (b, w)) =
        t₀ * (κ' * thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * T.fr q.1 (b', w)) :=
      (congrArg (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    have e3 : T.fr q.1 (b', w) = ρf w * (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) :=
      hfr q w hq
    rw [e3] at hval2
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hκ')]
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ w (tr2 _ _ w hq)))
    linear_combination -hval2
  have hAu : IsUnit A.det := by
    rcases hdA with h | ⟨⟨m, hm, h⟩, -⟩
    · rw [h]; exact isUnit_one
    · exact IsUnit.of_pow_eq_one h hm.ne'
  have hdA' : A⁻¹.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A⁻¹.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E) := by
    rw [Matrix.det_nonsing_inv]
    rcases hdA with h | ⟨⟨m, hm, h⟩, h4⟩
    · left; rw [h]; simp
    · right; exact ⟨⟨m, hm, by rw [Ring.inverse_eq_inv', inv_pow, h, inv_one]⟩, h4⟩
  have hiso' : ∀ a a', (F.Di k).EF (gam.symm a) (gam.symm a') = (F.Di k).EF a a' := fun a a' => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => T.bas.symm (gam.symm (T.bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := GlobalTheory.AdaptedDetSign.blocks_det_mod_four E H (F.Di k) g r T.bas gam.symm N
    ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) A⁻¹ T.adapt
    (Subtype.val_injective.comp (M.φ k).injective)
    (by
      rw [← (M.X k).Λ_span]
      congr 1
      ext v
      exact ⟨fun ⟨a, ha⟩ => ha ▸ (M.φ k a).2, fun hv => ⟨(M.φ k).symm ⟨v, hv⟩,
        congrArg Subtype.val ((M.φ k).apply_symm_apply ⟨v, hv⟩)⟩⟩)
    (fun a => by
      have := hA (gam.symm a)
      rw [gam.apply_symm_apply] at this
      show (M.φ k (gam.symm a) : Fin r → E) = A⁻¹ *ᵥ (M.φ k a : Fin r → E)
      rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec])
    hdA' (fun _ _ => rfl)
  have hκ2 := det_eq_sq_mul_of_theta_ratio E H (F.Di k) g T.bas gam.symm N P P' (T.h b) (T.h b') (T.ta b) (T.ta b')
    T.c₁ T.c₂ ρf _ T.sympl hiso' (fun _ _ => rfl) (fun a => by rw [← hPP, gam.apply_symm_apply]) hn hn'
    ⟨hsy, hpos⟩ ⟨hsy', hpos'⟩ hdu h8 hdet T.half₁ T.half₂ hρd hρ0 hρ1
    (div_ne_zero hκ (mul_ne_zero ht0 hκ')) hrel
  rw [hκ2]
  field_simp

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof

theorem exists_prime_natCast_ne_zero (k : Type) [Field k] :
    ∃ (l : ℕ) (_ : Fact l.Prime), (l : k) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : k) = 0
  · refine ⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩
    have : ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1 := by push_cast; ring
    rw [← this, h2, h3, sub_zero]
  · exact ⟨2, ⟨Nat.prime_two⟩, h2⟩

theorem torsionUnramified_imp_tate_and_infinite :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω]
      [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
      (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) →
      (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ V A _ _ hb
  obtain ⟨l, hl, hl0⟩ := exists_prime_natCast_ne_zero (ResidueField R)
  have hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0 := fun n => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hl0
  refine ⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩

end GlobalTheory.Proof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormEqOrientedHomSymplecticFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplecticForm_eq_orientedHomSymplecticForm : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ x y : Formalism.IndefR.Datum.WO S T,
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
        Formalism.IndefR.Datum.symplO S T x y := by
  first | exact @GlobalTheory.WeilSchrodinger.symp_eq_symplO | exact GlobalTheory.WeilSchrodinger.symp_eq_symplO | (intros; apply GlobalTheory.WeilSchrodinger.symp_eq_symplO <;> assumption)
end

