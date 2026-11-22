import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem smooth_of_openImm {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (g : ℕ) (hs : SmoothOfRelativeDimension g s) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    [IsOpenImmersion x] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B) ∧ Algebra.Smooth R B := by
  have h : SmoothOfRelativeDimension g (x ≫ s) := by
    have := smoothOfRelativeDimension_comp 0 g x s
    simpa using this
  rw [hx] at h
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h
  · have h2 : Smooth (spMap (algebraMap R B)) := SmoothOfRelativeDimension.smooth g _
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)

theorem rankAtStalk_kaehler_of_locally {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B))
    (p : PrimeSpectrum B) : Module.rankAtStalk Ω[B⁄R] p = g := by
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
    by_contra! hc
    exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  let Bt := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1
      (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)
  have : Algebra.FormallyEtale B Bt := .of_isLocalization (Submonoid.powers t)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by
    have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bt t]
      exact htp
    exact this
  have : Nontrivial Bt := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  have : Algebra.IsStandardSmooth R Bt := hstd.isStandardSmooth
  have : Module.Free Bt Ω[Bt⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have h1 := Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q
  rw [hq] at h1
  rw [← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
  have hf : Module.finrank Bt Ω[Bt⁄R] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]
    simp
  simp [hf]

theorem globForm_FP : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.glob1_finite_and_projective R _ (OAff A.hom) hF h0
  refine ⟨hfin, hproj, fun p ↦ ?_⟩

  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  let x : A.left := (η[A]).left.base p
  have hxp : A.hom.base x = p := by
    change ((η[A]).left ≫ A.hom).base p = p
    rw [hη]; rfl
  obtain ⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let T : AffOp A.left := Opposite.op U
  let B := (OAff A.hom).obj T
  have hUa : IsAffineOpen U.1 := U.2
  obtain ⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by
    have : x ∈ Set.range hUa.fromSpec.base := by
      rw [hUa.range_fromSpec]; exact hU
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  have hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p := by
    have := congrArg (fun f ↦ f.base q) (affPt_w A.hom U)
    change A.hom.base ((affPt A.hom U).base q) = _ at this
    rw [hq, hxp] at this
    exact this.symm
  haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa
  obtain ⟨hloc, hsm⟩ := smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)
  have hrk := rankAtStalk_kaehler_of_locally g hloc q
  let e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R] := (LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype
  have he : IsBaseChange B e := GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q
  rw [Module.rankAtStalk_eq_of_equiv he.equiv] at h1
  rw [← hqp]
  exact h1.symm.trans hrk

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsLift

theorem surjective_algebraMap_of_finite_unramified : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T]
    [Algebra.FormallyUnramified R T], Function.Surjective (algebraMap R T) := by
  intro R _ _ _ T _ _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := T)
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  have hk : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  let N : Submodule R T := LinearMap.range (Algebra.linearMap R T)
  have hNN : (⊤ : Submodule R T) ≤ N ⊔ IsLocalRing.maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨c, hc⟩ := hk (IsLocalRing.residue T x)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    have hr : IsLocalRing.residue T (algebraMap R T r) = IsLocalRing.residue T x := by
      rw [← hc, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)]
    have hx : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hr, sub_self]
    rw [← hm] at hx
    have hx' : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R T) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    have : x = algebraMap R T r + (x - algebraMap R T r) := by ring
    rw [this]
    exact Submodule.add_mem_sup ⟨r, rfl⟩ hx'
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hNN
  intro y
  obtain ⟨r, hr⟩ := hle (Submodule.mem_top (x := y))
  exact ⟨r, hr⟩

theorem nonempty_algHom_residueField : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T],
    Nonempty (T →ₐ[R] IsLocalRing.ResidueField R) := by
  intro R _ _ _ T _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  let l : IsLocalRing.ResidueField T →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R :=
    IsAlgClosed.lift
  exact ⟨(l.restrictScalars R).comp (IsScalarTower.toAlgHom R T (IsLocalRing.ResidueField T))⟩

theorem exists_section_of_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (B : Type) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (K : Type) [Field K] (φ : R →+* K) (χ : B →+* K), χ.comp (algebraMap R B) = φ →
    ∃ ψ : B →+* R, ψ.comp (algebraMap R B) = RingHom.id R ∧ φ.comp ψ = χ := by
  intro R _ _ _ B _ _ _ _ K _ φ χ hχ
  classical
  obtain ⟨J, hJ, T, _, _, e, hT, hT'⟩ := GlobalTheory.finite_algebra_strictly_henselian_pi R B
  haveI := Fintype.ofFinite J
  let ε : J → B := fun i => e.symm (Pi.single i 1)
  have hεsum : ∑ i, ε i = 1 := by
    simp only [ε, ← map_sum, Finset.univ_sum_single]
    exact map_one e.symm
  have hεid : ∀ i, IsIdempotentElem (ε i) := fun i => by
    show e.symm _ * e.symm _ = e.symm _
    rw [← map_mul, ← Pi.single_mul, _root_.one_mul]

  have hfac : ∀ (L : Type) [CommRing L] (ω : B →+* L) (i : J), ω (ε i) = 1 →
      ∀ (x : B) (r : R), e x i = algebraMap R (T i) r → ω x = ω (algebraMap R B r) := by
    intro L _ ω i hωi x r hr
    have hx : x * ε i = algebraMap R B r * ε i := by
      apply e.injective
      funext j
      simp only [ε, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Pi.mul_apply,
        Pi.algebraMap_apply]
      by_cases h : j = i
      · subst h; simp [hr]
      · simp [Pi.single_eq_of_ne h]
    have := congrArg ω hx
    rwa [map_mul, map_mul, hωi, _root_.mul_one, _root_.mul_one] at this
  obtain ⟨i, hi⟩ : ∃ i, χ (ε i) ≠ 0 := by
    by_contra h
    push_neg at h
    have := congrArg χ hεsum
    simp [map_sum, h] at this
  have hi1 : χ (ε i) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 ((hεid i).map χ)).resolve_left hi
  haveI : IsLocalRing (T i) := inferInstance
  haveI : Module.Finite R (T i) := (hT' i).2
  let π : B →ₐ[R] T i := (Pi.evalAlgHom R T i).comp e.toAlgHom
  have hπ : Function.Surjective π := fun y => ⟨e.symm (Pi.single i y), by simp [π]⟩
  haveI : Algebra.FormallyUnramified R (T i) := Algebra.FormallyUnramified.of_surjective π hπ
  have hsurj : Function.Surjective (algebraMap R (T i)) := surjective_algebraMap_of_finite_unramified R (T i)
  obtain ⟨β⟩ := nonempty_algHom_residueField R (T i)
  obtain ⟨ψ₀, hψ₀⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R B R).2 (β.comp π)
  have hψi : ψ₀ (ε i) = 1 := by
    have h1 : IsLocalRing.residue R (ψ₀ (ε i)) = 1 := by
      have := congrArg (fun g : B →ₐ[R] IsLocalRing.ResidueField R => g (ε i)) hψ₀
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at this
      rw [← IsLocalRing.ResidueField.algebraMap_eq, this]
      simp [π, ε]
    have hloc : ∀ a : R, IsIdempotentElem a → a = 0 ∨ a = 1 := fun a ha => by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
      · right; exact h.mul_left_cancel (by rw [ha.eq, _root_.mul_one])
      · left
        have h0 : (1 - a) * a = 0 := by rw [sub_mul, _root_.one_mul, ha.eq, sub_self]
        exact h.mul_right_eq_zero.1 h0
    rcases hloc _ ((hεid i).map ψ₀) with h | h
    · rw [h, map_zero] at h1; exact absurd h1.symm one_ne_zero
    · exact h
  refine ⟨ψ₀.toRingHom, ?_, ?_⟩
  · ext r; simp
  · ext x
    obtain ⟨r, hr⟩ := hsurj (e x i)
    have h1 : χ x = φ r := by
      rw [hfac K χ i hi1 x r hr.symm]
      show (χ.comp (algebraMap R B)) r = φ r
      rw [hχ]
    have h2 : ψ₀ x = r := by
      have := hfac R ψ₀.toRingHom i hψi x r hr.symm
      simpa using this
    show φ (ψ₀ x) = χ x
    rw [h1, h2]

theorem exists_iso_sp_of_finite_etale : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsFinite f → Etale f →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Algebra.Etale R B ∧ Module.Finite R B ∧
      ∃ e : X ≅ Sp B, e.hom ≫ spMap (algebraMap R B) = f := by
  intro R _ X f hf hfe
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ρ : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  letI : Algebra R Γ(X, ⊤) := ρ.toAlgebra
  have key : X.isoSpec.hom ≫ spMap (algebraMap R Γ(X, ⊤)) = f := by
    have h := Scheme.isoSpec_hom_naturality f
    rw [Scheme.isoSpec_Spec_hom] at h
    show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) = f
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop from rfl,
      Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hsp : spMap (algebraMap R Γ(X, ⊤)) = X.isoSpec.inv ≫ f := by
    rw [← key, Iso.inv_hom_id_assoc]
  have het : Etale (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  have hfi : IsFinite (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  refine ⟨Γ(X, ⊤), inferInstance, inferInstance, ?_, ?_, X.isoSpec, key⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 het
  · exact (IsFinite.SpecMap_iff _).1 hfi

theorem preconnectedSpace_sp (R : Type) [CommRing R] [IsLocalRing R] : PreconnectedSpace (Sp R) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  have key : ∀ z : Sp R, z ⤳ (IsLocalRing.closedPoint R : PrimeSpectrum R) := fun z =>
    IsLocalRing.specializes_closedPoint (R := R) z
  by_cases h : (IsLocalRing.closedPoint R : PrimeSpectrum R) ∈ s
  · right; ext z; simp only [Set.mem_univ, iff_true]; exact (key z).mem_open hs.isOpen h
  · left; ext z; simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hz => h ((key z).mem_closed hs.isClosed hz)

theorem torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  intro S A _ _ hA n _ hn R _ _ _ t K _ φ
  haveI := hA
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  haveI := hfin
  haveI := het
  haveI := preconnectedSpace_sp R
  let ψK : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let E := GlobalTheory.TorsionUnram.torsionEquiv A n
  refine ⟨fun g h hg hh hgh => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := (E _).surjective ⟨g, hg⟩
    obtain ⟨b, hb⟩ := (E _).surjective ⟨h, hh⟩
    have ga : a ≫ torsion.ι A n = g := congrArg Subtype.val ha
    have gb : b ≫ torsion.ι A n = h := congrArg Subtype.val hb
    have hab : ψK ≫ a = ψK ≫ b := by
      apply (E _).injective
      apply Subtype.ext
      show (ψK ≫ a) ≫ torsion.ι A n = (ψK ≫ b) ≫ torsion.ι A n
      rw [Category.assoc, Category.assoc, ga, gb]
      exact hgh
    have hab' : spMap φ ≫ a.left = spMap φ ≫ b.left := congrArg (fun u => u.left) hab
    haveI : PreconnectedSpace (Over.mk t).left := preconnectedSpace_sp R
    have : a = b := GlobalTheory.over_eq_of_preconnected_of_unramified (spMap φ) hab'
    rw [← ga, ← gb, this]
  · obtain ⟨y, hy⟩ := (E _).surjective ⟨x, hx⟩
    have yx : y ≫ torsion.ι A n = x := congrArg Subtype.val hy
    obtain ⟨B, _, _, _, _, e, he⟩ :=
      exists_iso_sp_of_finite_etale R _ (pullback.snd (torsion A n).hom t) inferInstance inferInstance
    let q : Sp K ⟶ Sp B := pullback.lift y.left (spMap φ) (Over.w y) ≫ e.hom
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective q
    have hq : q ≫ spMap (algebraMap R B) = spMap φ := by
      simp only [q, Category.assoc, he, pullback.lift_snd]
    have hχ : χ'.hom.comp (algebraMap R B) = φ := by
      have h0 : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ χ') =
          Spec.map (CommRingCat.ofHom φ) := by
        rw [Spec.map_comp, hχ']
        exact hq
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
    obtain ⟨ψ, hψ1, hψ2⟩ := exists_section_of_point R B K φ χ'.hom hχ
    let s : Sp R ⟶ (torsion A n).left := spMap ψ ≫ e.inv ≫ pullback.fst _ _
    have h1 : e.inv ≫ pullback.snd (torsion A n).hom t = spMap (algebraMap R B) := by
      rw [← he, Iso.inv_hom_id_assoc]
    have hs : s ≫ (torsion A n).hom = t := by
      simp only [s, Category.assoc, pullback.condition]
      rw [reassoc_of% h1, ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', hψ1]
      show Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ t = t
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    let gs : Over.mk t ⟶ torsion A n := Over.homMk s hs
    refine ⟨gs ≫ torsion.ι A n, ((E _) gs).2, ?_⟩
    have h2 : spMap φ ≫ spMap ψ = q := by
      rw [← GlobalTheory.TorsionUnram.spMap_comp', hψ2, ← hχ']
      rfl
    have hy' : ψK ≫ gs = y := by
      apply Over.OverMorphism.ext
      show spMap φ ≫ s = y.left
      simp only [s, ← Category.assoc]
      rw [h2]
      simp only [q, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
    rw [← Category.assoc, hy', yx]

end GlobalTheory.TorsLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLevelFamily
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def AdditiveLevelFamily {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (T : Over S) (lv : D.La → (T ⟶ o.A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, g ^ N₁ = 1 →
        ∃ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧ ∀ a b, Out.WeilIs o.A o.PP.L N₁
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a)
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv b) (unitOn (z ^ D.EF a b))

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

@[simp] theorem word_nil (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ [] Φ = Φ := rfl

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro D m n N e hrat y z
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  let I : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] Matrix (Fin m) (Fin n) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = incM D.host.F x := fun x => rfl
  let L : Matrix (Fin m) (Fin n) D.host.E →ₗ[D.host.F] VA D.host.F N := (e.toLinearMap.restrictScalars D.host.F).comp I
  have hL : ∀ x, L x = e (incM D.host.F x) := fun x => rfl
  let r : (Fin N → D.host.F) →ₗ[D.host.F] (Fin N → AF D.host.F) :=
    LinearMap.pi fun i => (Algebra.linearMap D.host.F (AF D.host.F)).comp (LinearMap.proj i)
  let R : ((Fin N → D.host.F) × (Fin N → D.host.F)) →ₗ[D.host.F] VA D.host.F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap D.host.F (AF D.host.F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin n) * Module.finrank D.host.F D.host.E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank D.host.F (LinearMap.range L) = Module.finrank D.host.F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCharacterDetPower
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_real_eq_prod_det : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) (e : D.what₂.Tau → ℤ), IsInfFam θ → MuVal V χ mu → (∀ ρ, HasInfExp D χ ρ (-(e ρ : ℚ))) → ∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ)) := by
  intro D θ V χ mu e hθ hmu he u hu
  obtain ⟨x, hx, h⟩ := GlobalTheory.VacuumCharacter.exists_root hθ V
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ).ne_zero) u hu
  rw [hmu.2 u x hx, h χ (fun ρ => -(e ρ)) (fun ρ => by push_cast; exact he ρ)]
  rfl

end GlobalTheory.HolRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_constant_term_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  first | exact @GlobalTheory.UAut.ConstAut.isAutOn_constTerm | exact GlobalTheory.UAut.ConstAut.isAutOn_constTerm | (intros; apply GlobalTheory.UAut.ConstAut.isAutOn_constTerm <;> assumption)
end

