import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationNormalisedBlowupSiegelModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PoincCov

theorem isProper_of_blowup {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S₀ : Scheme.{0}} {π₀ : S₀ ⟶ Z} (hB : FinalTheorems.Blowup π₀ J) : IsProper π₀ := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨X', b, hb, hbs, -⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  obtain ⟨f, hf, -⟩ := hb.2 S₀ π₀ hB.1
  obtain ⟨f', hf', -⟩ := hB.2 X' b hb.1
  have e1 : f ≫ f' = 𝟙 S₀ := (hB.2 S₀ π₀ hB.1).unique (by simp [hf', hf]) (by simp)
  have e2 : f' ≫ f = 𝟙 X' := (hb.2 X' b hb.1).unique (by simp [hf, hf']) (by simp)
  haveI : IsIso f := ⟨f', e1, e2⟩
  haveI : IsSeparated z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsProper (b ≫ z) := by
    obtain ⟨m, e, he, he'⟩ := hbs
    have := isProper_str (cycAway n) m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b z
  rw [← hf]
  infer_instance

theorem isProper_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J) : IsProper π := by
  obtain ⟨-, S₀, π₀, ν, U, hB, rfl, hfin, -, -, -⟩ := h
  haveI := isProper_of_blowup z hz hB
  infer_instance

theorem isIso_restrict_of_isNormBl {n : ℕ} {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (hz : IsProjOver z)
    (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} (h : IsNormBl π J)
    (V : Z.Opens) (hV : ∀ x ∈ V, x ∉ J.support) : IsIso (π ∣_ V) := by
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  obtain ⟨hS, S₀, π₀, ν, U, hB, rfl, hfin, hUd, hνd, hνU⟩ := h
  haveI hπ₀V : IsIso (π₀ ∣_ V) := GlobalTheory.Principalise.isIso_restrict_of_blowup hB V hV
  haveI := isProper_of_blowup z hz hB
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (π₀ ≫ z)
  haveI : GlobalTheory.IsNormalScheme Z := .of_pred hZ
  haveI hoi : IsOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI : GlobalTheory.IsNormalScheme (π₀ ⁻¹ᵁ V).toScheme := .of_isOpenImmersion ((π₀ ⁻¹ᵁ V).ι ≫ π₀)
  haveI : IsIso (ν ∣_ (π₀ ⁻¹ᵁ V)) :=
    GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense ν U (π₀ ⁻¹ᵁ V) ((GlobalTheory.isNormalScheme_iff_pred S).mp hS) (GlobalTheory.IsNormalScheme.pred _) hUd hνd hνU
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' (by assumption) hπ₀V

end GlobalTheory.PoincCov

namespace GlobalTheory.PoincCov

theorem exists_normalisation_cover : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z), (∀ x ∈ J.support, x ∉ Set.range i) → IsNormBl π J → ∀ X₁ : Setup F W i, ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ X₁.M.Z) (ν : S₁ ⟶ S), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ IsFinite ν ∧ ν ≫ π = p₁ ≫ X₁.π ∧ IsIso (p₁ ∣_ (X₁.π ⁻¹ᵁ i.opensRange)) ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ X₁.π)) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (b : Sp R ⟶ X₁.M.Z), a ≫ π = b ≫ X₁.π → Set.range (jK R ≫ b ≫ X₁.π) ⊆ Set.range i → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν = a ∧ ξ₁ ≫ p₁ = b := by
  intro g _ n _ _ F Z z i _ hz hZ hiz hdense W J S π hJi hNB X₁
  haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  haveI : Algebra.FiniteType ℤ (CommRingCat.of (cycAway n)) := ‹Algebra.FiniteType ℤ (cycAway n)›
  haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : LocallyOfFiniteType z := by
    obtain ⟨m, e, he, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI hπP : IsProper π := isProper_of_isNormBl z hz hNB
  let Vi : Z.Opens := i.opensRange
  haveI hπV : IsIso (π ∣_ Vi) := isIso_restrict_of_isNormBl z hz hZ hNB Vi (fun x hx hJ => hJi x hJ hx)
  have monoV : ∀ {T : Scheme.{0}} (u v : T ⟶ S), u ≫ π = v ≫ π → Set.range (u ≫ π) ⊆ (Vi : Set Z) → u = v := by
    intro T u v huv hr
    have hu : Set.range u ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      exact hr ⟨w, rfl⟩
    have hv : Set.range v ⊆ ((π ⁻¹ᵁ Vi : S.Opens) : Set S) := by
      rintro _ ⟨w, rfl⟩
      have := hr ⟨w, rfl⟩
      rw [huv] at this
      exact this
    have hm : Mono ((π ⁻¹ᵁ Vi).ι ≫ π) := by
      rw [← morphismRestrict_ι]; infer_instance
    rw [← Scheme.Opens.range_ι] at hu hv
    rw [← IsOpenImmersion.lift_fac _ u hu, ← IsOpenImmersion.lift_fac _ v hv]
    congr 1
    rw [← cancel_mono ((π ⁻¹ᵁ Vi).ι ≫ π)]
    simp only [← Category.assoc, IsOpenImmersion.lift_fac]
    exact huv
  let U : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ Vi
  have hUne : (U : Set X₁.M.Z).Nonempty := by
    refine ⟨X₁.M.pt (show Sp X₁.Ω₁ from IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    show X₁.π (X₁.M.pt _) ∈ Vi
    rw [← Scheme.Hom.comp_apply, X₁.comp]
    exact ⟨_, rfl⟩
  haveI : Nonempty U := hUne.to_subtype
  let c : (U : Scheme.{0}) ⟶ S := X₁.π ∣_ Vi ≫ inv (π ∣_ Vi) ≫ (π ⁻¹ᵁ Vi).ι
  have hc : c ≫ π = U.ι ≫ X₁.π := by
    simp only [c, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  let j : (U : Scheme.{0}) ⟶ pullback π X₁.π := pullback.lift c U.ι hc
  haveI := X₁.fin
  haveI : LocallyOfFiniteType (X₁.π ≫ z) := inferInstance
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ z)
  haveI : IsLocallyNoetherian (pullback π X₁.π) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π X₁.π ≫ π ≫ z)
  have hjs : j ≫ pullback.snd π X₁.π = U.ι := pullback.lift_snd _ _ _
  haveI : QuasiCompact (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd π X₁.π)
  haveI : QuasiSeparated (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : QuasiSeparated j := QuasiSeparated.of_comp j (pullback.snd π X₁.π)
  haveI : LocallyOfFiniteType (j ≫ pullback.snd π X₁.π) := by rw [hjs]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd π X₁.π)
  haveI hfin : IsFinite j.fromNormalization :=
    GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of (cycAway n)) j
      (pullback.fst π X₁.π ≫ π ≫ z) fun x _ => (LocallyOfFiniteType.stalkMap j x).residueFieldMap
  haveI : GlobalTheory.IsNormalScheme X₁.M.Z := X₁.normal
  haveI : GlobalTheory.IsNormalScheme (U : Scheme.{0}) := .of_isOpenImmersion U.ι
  let p₁ : j.normalization ⟶ X₁.M.Z := j.fromNormalization ≫ pullback.snd π X₁.π
  let ν : j.normalization ⟶ S := j.fromNormalization ≫ pullback.fst π X₁.π
  have hp₁ : j.toNormalization ≫ p₁ = U.ι := by
    show j.toNormalization ≫ j.fromNormalization ≫ pullback.snd π X₁.π = U.ι
    rw [Scheme.Hom.toNormalization_fromNormalization_assoc, pullback.lift_snd]
  have hcomm : ν ≫ π = p₁ ≫ X₁.π := by simp [ν, p₁, pullback.condition]
  refine ⟨j.normalization, inferInstance, p₁, ν, GlobalTheory.IsNormalScheme.pred _, ?_, ?_, ?_, hcomm, ?_, ?_, ?_⟩
  · show IsProper (j.fromNormalization ≫ pullback.snd π X₁.π)
    infer_instance
  · constructor
    have hUd : Dense (U : Set X₁.M.Z) := U.isOpen.dense hUne
    refine hUd.mono ?_
    intro x hx
    refine ⟨j.toNormalization ⟨x, hx⟩, ?_⟩
    rw [show p₁ (j.toNormalization ⟨x, hx⟩) = (j.toNormalization ≫ p₁) ⟨x, hx⟩ from rfl, hp₁]
    rfl
  · show IsFinite (j.fromNormalization ≫ pullback.fst π X₁.π)
    infer_instance
  · let O : (pullback π X₁.π).Opens := pullback.snd π X₁.π ⁻¹ᵁ U
    have hjO : Set.range j ⊆ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      show pullback.snd π X₁.π (j x) ∈ U
      rw [← Scheme.Hom.comp_apply, hjs]
      exact x.2
    let f0 : (U : Scheme.{0}) ⟶ O := IsOpenImmersion.lift O.ι j hjO
    have hf0 : f0 ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
    let s' := pullback.snd π X₁.π ∣_ U
    have hs' : s' ≫ U.ι = O.ι ≫ pullback.snd π X₁.π := morphismRestrict_ι _ _
    have e1 : f0 ≫ s' = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, hs', ← Category.assoc, hf0, hjs, Category.id_comp]
    have e2 : s' ≫ f0 = 𝟙 _ := by
      rw [← cancel_mono O.ι, Category.assoc, hf0, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hs', Category.assoc, Category.assoc, pullback.condition]
        · rw [Category.assoc, hc, ← Category.assoc]
          rintro _ ⟨w, rfl⟩
          rw [Scheme.Hom.comp_apply]
          exact (s' w).2
      · rw [Category.assoc, pullback.lift_snd, hs']
    haveI : IsIso s' := ⟨f0, e2, e1⟩
    haveI : IsIso f0 := ⟨s', e1, e2⟩
    have H := GlobalTheory.isPullback_toNormalization_of_mono f0 O.ι j hf0.symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict j.fromNormalization O) H.flip
    haveI : IsIso (j.fromNormalization ∣_ O) := by rw [← e]; infer_instance
    show IsIso ((j.fromNormalization ≫ pullback.snd π X₁.π) ∣_ U)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (by assumption) (by assumption)
  · obtain ⟨-, S₀, π₀, ν₀, U₀, hB, hνπ, -, -, -, -⟩ := hNB
    obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hB.1
    have hpe : p₁ ≫ X₁.π = (ν ≫ ν₀) ≫ π₀ := by rw [← hcomm, Category.assoc ν ν₀ π₀, hνπ]
    have hK : D.KeepsRegular (ν ≫ ν₀) := by
      refine D.keepsRegular_of_dense _ (fun y => inferInstance) ((j.toNormalization.denseRange).mono ?_)
      rintro _ ⟨x, rfl⟩
      show (ν ≫ ν₀) (j.toNormalization x) ∉ D.idealSheaf.support
      rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
      intro h
      apply hJi _ h
      have : j.toNormalization ≫ (ν ≫ ν₀) ≫ π₀ = U.ι ≫ X₁.π := by rw [← hpe, ← Category.assoc, hp₁]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
      exact x.2
    have e : J.comap (p₁ ≫ X₁.π) = (D.pull (ν ≫ ν₀) hK).idealSheaf := by
      rw [GlobalTheory.EffCartierData.idealSheaf_pull, hD, hpe, Scheme.IdealSheafData.comap_comp]
    rw [e]
    exact GlobalTheory.EffCartierData.effCartier_idealSheaf _
  · intro R _ _ _ _ a b hab hgen
    let d : Sp R ⟶ pullback π X₁.π := pullback.lift a b hab
    have hr : Set.range (jK R ≫ b) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show X₁.π ((jK R ≫ b) w) ∈ Vi
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      exact hgen ⟨w, rfl⟩
    let y := IsOpenImmersion.lift U.ι (jK R ≫ b) hr
    have hy : y ≫ U.ι = jK R ≫ b := IsOpenImmersion.lift_fac _ _ _
    have hyj : y ≫ j = jK R ≫ d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
        apply monoV
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc, Category.assoc, hab]
        · rw [Category.assoc, hc, ← Category.assoc, hy, Category.assoc]
          exact hgen
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, hy]
    obtain ⟨ξ, ⟨-, hξ⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (R := R) (R' := FractionRing R)
      (nonZeroDivisors R) le_rfl j.fromNormalization (y ≫ j.toNormalization) d
      (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hyj])
    refine ⟨ξ, ?_, ?_⟩
    · show ξ ≫ j.fromNormalization ≫ pullback.fst π X₁.π = a
      rw [← Category.assoc, hξ, pullback.lift_fst]
    · show ξ ≫ j.fromNormalization ≫ pullback.snd π X₁.π = b
      rw [← Category.assoc, hξ, pullback.lift_snd]

end GlobalTheory.PoincCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenMulPointOnPullbackContainingClosedFibr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem Near.exists_mul_pt {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {Z : Scheme.{0}} (q : Z ⟶ S) (a b : Z ⟶ N.U.left) (ha : a ≫ N.U.hom = q ≫ π)
    (hb : b ≫ N.U.hom = q ≫ π) :
    ∃ (O : Z.Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : Z, π (q z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ q ≫ π ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), t ≫ O.ι ≫ q = s →
        N.Pt s (t ≫ O.ι ≫ a) x.left → N.Pt s (t ≫ O.ι ≫ b) y.left → N.Pt s (t ≫ h) (x * y).left := by
  haveI := N.isOpen
  let X₁ : Over.mk q ⟶ G := Over.homMk (pullback.lift a q ha ≫ N.u) (by
    change (pullback.lift a q ha ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let X₂ : Over.mk q ⟶ G := Over.homMk (pullback.lift b q hb ≫ N.u) (by
    change (pullback.lift b q hb ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let m : Z ⟶ G.left := (X₁ * X₂).left
  have hm : m ≫ G.hom = q := Over.w (X₁ * X₂)
  let O : Z.Opens := m ⁻¹ᵁ N.u.opensRange
  have hO : Set.range (O.ι ≫ m) ⊆ Set.range N.u := by
    rintro _ ⟨z, rfl⟩
    have hz : O.ι z ∈ O := z.2
    rw [Scheme.Hom.comp_apply]
    exact hz
  let h' : O.toScheme ⟶ pullback N.U.hom π := IsOpenImmersion.lift N.u (O.ι ≫ m) hO
  have hh : h' ≫ N.u = O.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hs : h' ≫ pullback.snd N.U.hom π = O.ι ≫ q := by
    rw [← N.u_over, ← Category.assoc, hh, Category.assoc, hm]
  refine ⟨O, h' ≫ pullback.fst _ _, fun z hz => ?_, ?_, ?_⟩
  · refine N.all (m z) ?_
    rw [← Scheme.Hom.comp_apply m G.hom, hm]
    exact hz
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.assoc]
  · rintro T t s x y hts ⟨x₀, hx₁, hx₂, hx₃⟩ ⟨y₀, hy₁, hy₂, hy₃⟩
    let τ : Over.mk s ⟶ Over.mk q := Over.homMk (t ≫ O.ι) (by
      change (t ≫ O.ι) ≫ q = s
      rw [Category.assoc, hts])
    have ex : x = τ ≫ X₁ := by
      ext1
      change x.left = (t ≫ O.ι) ≫ pullback.lift a q ha ≫ N.u
      rw [← hx₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hx₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    have ey : y = τ ≫ X₂ := by
      ext1
      change y.left = (t ≫ O.ι) ≫ pullback.lift b q hb ≫ N.u
      rw [← hy₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hy₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hy₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    refine ⟨t ≫ h', Category.assoc _ _ _, ?_, ?_⟩
    · rw [Category.assoc, hs, hts]
    · rw [ex, ey, ← MonObj.comp_mul, Category.assoc, hh]
      exact (Category.assoc _ _ _).symm

theorem Near.exists_mul_pt_pullback (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S)
    [GrpObj G'] (N : Near M.π G') :
    ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left),
      (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π),
        (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'),
        t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left →
        N.Pt s (t ≫ h) (x * y).left := by
  obtain ⟨O, h, h₁, h₂, h₃⟩ := N.exists_mul_pt (pullback.snd (N.U ⊗ N.U).hom M.π)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left)
    (by rw [Category.assoc, Over.w (fst N.U N.U), pullback.condition])
    (by rw [Category.assoc, Over.w (snd N.U N.U), pullback.condition])
  refine ⟨O, h, fun z hz => h₁ z ?_, ?_, h₃⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  · rw [h₂, pullback.condition]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTraceCoefficientsNonvanishingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_trace_coefficients_nonvanishing : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] [IsProper f] [IsLocallyNoetherian W] (L : LB M), IsAmpleLB L → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → ∀ y : W, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, ∀ (V' : W.Opens), y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  first | exact @GlobalTheory.ProperDenom.exists_local_denom | exact GlobalTheory.ProperDenom.exists_local_denom | (intros; apply GlobalTheory.ProperDenom.exists_local_denom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  first | exact @GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | exact GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | (intros; apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombinationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ), φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  first | exact @GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | exact GlobalTheory.FieldPair.exists_ordQ_eq_ord_div | (intros; apply GlobalTheory.FieldPair.exists_ordQ_eq_ord_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceDominatingLocalDomainComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_dominating_local_domain_complex : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (O : Subring κ) (hO : IsLocModel (algebraMap ℂ κ) O), letI := hO.isLocalRing;
  ¬ IsField O → ∃ F : Place (algebraMap ℂ κ), F.Contains O ∧ ∀ f : O, f ∈ IsLocalRing.maximalIdeal O → (f : κ) ≠ 0 → 0 < F.ord f := by
  first | exact @GlobalTheory.DvrDom.exists_place_dominating | exact GlobalTheory.DvrDom.exists_place_dominating | (intros; apply GlobalTheory.DvrDom.exists_place_dominating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_point_hasArcData_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  intro E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ
  obtain ⟨hdvr, hc, hcz⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨⟨h1, h2, -, h4, h5⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hT := GlobalTheory.twistBaseChange
  have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨χ, hχ, -⟩ := hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)
  obtain ⟨hs, -, hj, hd⟩ := (hχ χ).1 rfl
  obtain ⟨-, -, ev, hC, hX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc
  have hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x)) := by
      simp only [Scheme.Hom.comp_apply]
    rw [e]
    apply hj
    intro hx
    have hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal := hx
    have hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X))) := by
      rw [map_mul, hC, hX]
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)
  refine ⟨spMap ev ≫ χ, ?_⟩
  rw [hm]
  exact GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullb
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem le_pull_chart {X Y : Scheme.{0}} (L : LB X) (q : Y ⟶ X) {D : Type} [CommRing D] (x : Sp D ⟶ Y)
    (i : L.ι) (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ (L.pull q).U (fun _ ↦ i) :=
  fun p hp ↦ Set.mem_iInter.2 fun _ ↦ h hp

theorem evU_mul {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU x U (a * b) = evU x U a * evU x U b := by
  unfold evU
  rw [dif_pos h, dif_pos h, dif_pos h, map_mul]

theorem exists_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  intro R _ X Y L _ q hT
  obtain ⟨s, hs⟩ := hT
  refine ⟨fun E _ _ z i ↦ evU z.left ((L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i)).val, ?_, ?_, ?_⟩
  · intro E _ _ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    show IsUnit (evU _ _ _)
    unfold evU
    rw [dif_pos hz]
    exact (s.s _).isUnit.map _
  · intro E _ _ E' _ _ ψ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    exact evalSectionAtPointOrZero_specMap_comp _ E E' (ψ : E →+* E') z.left _ _ hz
  · intro E _ _ z i j hi hj
    have hzi := le_pull_chart L q.left z.left i hi
    have hzj := le_pull_chart L q.left z.left j hj
    have hV : ⊤ ≤ z.left ⁻¹ᵁ ((L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j)) :=
      fun p hp ↦ ⟨hzi hp, hzj hp⟩
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U i ⊓ L.U j) := fun p hp ↦ ⟨hi hp, hj hp⟩
    have e := congrArg (fun u ↦ evU z.left _ (Units.val u)) (hs (fun _ ↦ i) (fun _ ↦ j))
    simp only [Units.val_mul] at e
    rw [evU_mul _ _ hV] at e
    have e1 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i))).val =
        evU z.left _ (s.s (fun _ ↦ i)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e2 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ j)) (s.s (fun _ ↦ j))).val =
        evU z.left _ (s.s (fun _ ↦ j)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e3 : evU z.left _ ((L.pull q.left).g (fun _ ↦ i) (fun _ ↦ j)).val =
        evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val := by
      unfold evU
      rw [dif_pos hV]
      have hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U i ⊓ L.U j) := hij
      rw [dif_pos hij']
      exact (evalAt_pull_g L q.left z.left (fun _ ↦ i) (fun _ ↦ j) hij hV).symm
    rw [e1, e2, e3] at e
    exact e

end GlobalTheory.PtExt
end
end

