import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2891
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThickStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  first | exact @GlobalTheory.Mum.EndThick.formalEnd_exists | exact GlobalTheory.Mum.EndThick.formalEnd_exists | (intros; apply GlobalTheory.Mum.EndThick.formalEnd_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | exact GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed | (intros; apply GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_isAffineOpen_of_preimage_le_affine : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0})
    (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) →
    IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X,
    (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs
  classical

  have hg : IsFinite (spMap (algebraMap R R₁)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁)) := by
    rw [flat_and_surjective_SpecMap_iff]
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (spMap (algebraMap R R₁)) := hff.1
  have : Surjective (spMap (algebraMap R R₁)) := hff.2
  have : IsFinite b := MorphismProperty.of_isPullback H.flip hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p

  let O' : X.Opens := ⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsO' : ∀ x ∈ s, x ∈ O' := by
    rintro x hx ⟨z, hz, rfl⟩
    exact hz (hs z hx)
  have key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O' := by
    intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)
    exact ⟨U, hU, hxU, hUO⟩
  choose U hU hxU hUO using key
  let V : X.Opens := ⨆ x : s, U x.1 x.2
  have hVO : V ≤ O' := iSup_le fun x => hUO x.1 x.2
  have hsV : ∀ x ∈ s, x ∈ V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩
  have hVc : IsCompact (V : Set X) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hU x.1 x.2).isCompact
  have hVq : IsQuasiSeparated (V : Set X) := IsQuasiSeparated.of_quasiSeparatedSpace _
  have hVW : b ⁻¹ᵁ V ≤ W := by
    intro z hz
    by_contra h
    exact hVO hz ⟨z, h, rfl⟩

  have hfin : (b ⁻¹' (s : Set X)).Finite :=
    s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x
  obtain ⟨f, hfV, hft⟩ := GlobalTheory.T.exists_basicOpen_between_finset_and_open' X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset
    (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))
  let f' : Γ(X₁, b ⁻¹ᵁ V) := X₁.presheaf.map (homOfLE hVW).op f
  have hf' : X₁.basicOpen f' = X₁.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfV
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange R R₁ X X₁ p p₁ b H V hVc hVq f'
  refine ⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩
  swap
  · rw [hf']
    exact hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))

  have hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f := by
    intro z hz
    rw [← hf']
    exact ((hn (b z)).1 hz).2 z rfl
  have hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n) := by
    let g : Γ(X₁, X₁.basicOpen f) := X₁.presheaf.map (homOfLE hfV).op (b.app V n)
    have e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact inf_eq_right.2 hle
    rw [← e]
    exact (hW.basicOpen f).basicOpen g
  have : IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme := hA
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mem_mul_eq_zero_of_algebraMap_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] (M : Submonoid R) [IsLocalization M S] :
    ∃ f ∈ M, ∀ a : R, algebraMap R S a = 0 → f * a = 0 := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R S)) :
    (RingHom.ker (algebraMap R S)).FG)
  have hk : ∀ a ∈ s, ∃ m : M, (m : R) * a = 0 := by
    intro a ha
    have : a ∈ RingHom.ker (algebraMap R S) := hs ▸ Submodule.subset_span ha
    exact (IsLocalization.map_eq_zero_iff M S a).1 this
  choose! m hm using hk
  refine ⟨∏ a ∈ s, (m a : R), Submonoid.prod_mem _ fun a _ => (m a).2, ?_⟩
  have key : ∀ a ∈ Submodule.span R (s : Set R), (∏ a ∈ s, (m a : R)) * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        rw [← Finset.prod_erase_mul _ _ hb, _root_.mul_assoc, hm b hb, mul_zero]
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add, hb, hc, add_zero]
    | smul r b _ hb => rw [smul_eq_mul, _root_.mul_left_comm, hb, mul_zero]
  intro a ha
  exact key a (hs ▸ ha)

theorem exists_affineOpen_isIntegrallyClosed_charZero (X : Scheme.{0})
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X)
    (h0 : ∀ x : X, CharZero (X.residueField x)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧
      IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := X.presheaf.algebra_section_stalk (U := V) ⟨x, hxV⟩
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨f, hfM, hf⟩ := exists_mem_mul_eq_zero_of_algebraMap_eq_zero (R := Γ(X, V))
    (S := X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  have hU : IsAffineOpen (X.basicOpen f) := hV.basicOpen f
  have hxU : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxV]
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨f, hfM⟩

  letI : Algebra Γ(X, V) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  let g : Γ(X, X.basicOpen f) →+* X.presheaf.stalk x := (X.presheaf.germ _ x hxU).hom
  have hcomp : ∀ a : Γ(X, V), g (algebraMap Γ(X, V) Γ(X, X.basicOpen f) a) =
      algebraMap Γ(X, V) (X.presheaf.stalk x) a := fun a =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxU a
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) σ
    have hr : algebraMap Γ(X, V) (X.presheaf.stalk x) r = 0 := by
      rw [← hcomp, ← hrm, map_mul, hσ, zero_mul]
    have hfr := congrArg (algebraMap Γ(X, V) Γ(X, X.basicOpen f)) (hf r hr)
    rw [map_mul, map_zero] at hfr
    have hu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) f) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) ⟨f, Submonoid.mem_powers f⟩
    have hr0 := hu.mul_right_eq_zero.1 hfr
    have hmu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) (m : Γ(X, V))) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) m
    rw [hr0] at hrm
    exact hmu.mul_left_eq_zero.1 hrm
  haveI : IsDomain (X.presheaf.stalk x) := (hN x).1
  haveI hD : IsDomain Γ(X, X.basicOpen f) := hinj.isDomain g
  haveI : CharZero (X.residueField x) := h0 x
  have hcz : CharZero Γ(X, X.basicOpen f) := by
    refine ⟨fun a b hab => ?_⟩
    have := congrArg ((X.residue x).hom.comp g) hab
    simp only [map_natCast] at this
    exact Nat.cast_injective this
  have hIC : IsIntegrallyClosed Γ(X, X.basicOpen f) := by
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
    let P : Spec Γ(X, X.basicOpen f) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ X.basicOpen f := hU.range_fromSpec.le ⟨P, rfl⟩
    letI : Algebra Γ(X, X.basicOpen f) (X.presheaf.stalk (hU.fromSpec P)) :=
      X.presheaf.algebra_section_stalk (U := X.basicOpen f) ⟨_, hy⟩
    have h : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) :=
      hU.isLocalization_stalk' P hy
    haveI := (hN (hU.fromSpec P)).1
    haveI := (hN (hU.fromSpec P)).2
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P))
        (Localization.AtPrime p)).toRingEquiv
  exact ⟨⟨X.basicOpen f, hU⟩, hxU, hD, IsLocallyNoetherian.component_noetherian ⟨_, hU⟩, hIC, hcz⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparating
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAmpleSep

theorem mem_iff_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (I : Ideal R) (hI : ∀ j, r j - φ (c j) ∈ I) (p : MvPolynomial κ A) :
    MvPolynomial.eval₂Hom φ r p ∈ I ↔ φ (MvPolynomial.eval c p) ∈ I := by
  have hr : (Ideal.Quotient.mk I) ∘ r = ((Ideal.Quotient.mk I).comp φ) ∘ c := by
    funext j; exact Ideal.Quotient.eq.2 (hI j)
  have e : Ideal.Quotient.mk I (MvPolynomial.eval₂Hom φ r p) = Ideal.Quotient.mk I (φ (MvPolynomial.eval c p)) := by
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, hr, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.eval₂_comp_left]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := I), e]

theorem ideal_eq_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom φ r)) (P Q : Ideal R)
    (hP : ∀ j, r j - φ (c j) ∈ P) (hQ : ∀ j, r j - φ (c j) ∈ Q) (hPQ : ∀ x, φ x ∈ P ↔ φ x ∈ Q) : P = Q := by
  ext a
  obtain ⟨p, rfl⟩ := hs a
  rw [mem_iff_of_gen φ r c P hP, mem_iff_of_gen φ r c Q hQ]
  exact hPQ _

theorem mem_basicOpen_iff_prime {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) {y : Y} (hy : y ∈ D)
    (a : Γ(Y, D)) : y ∈ Y.basicOpen a ↔ a ∉ (hD.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have h := hD.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hD.primeIdealOf ⟨y, hy⟩ ∈ hD.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ y ∈ Y.basicOpen a := by
    show hD.fromSpec (hD.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a ↔ y ∈ Y.basicOpen a
    rw [h]
  rw [← h2, hD.fromSpec_preimage_basicOpen]
  rfl

variable {K : Type} [Field K]

theorem one_left_comp_hom (B : AbVar K) : (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ≫ B.X.hom = 𝟙 _ := Over.w _

theorem sp_pt_eq (a b : Sp K) : a = b := by
  have h : ∀ p : PrimeSpectrum K, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem top_le_preimage_unit (B : AbVar K) : (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens) ≤
    (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ⁻¹ᵁ (B.X.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial

def unitU (B : AbVar K) : (⊤ : (Sp K).Opens).toScheme ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left.resLE (B.X.hom ⁻¹ᵁ ⊤) (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens)
    (top_le_preimage_unit B)

theorem unitU_comp (B : AbVar K) : unitU B ≫ (B.X.hom ∣_ ⊤) = 𝟙 _ := by
  rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, unitU,
    Scheme.Hom.resLE_comp_ι_assoc, one_left_comp_hom, Category.comp_id, Category.id_comp]

theorem unitU_ι (B : AbVar K) (t : (⊤ : (Sp K).Opens).toScheme) :
    (B.X.hom ⁻¹ᵁ ⊤).ι (unitU B t) = B.origin := by
  rw [← Scheme.Hom.comp_apply, unitU, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, AbVar.origin]
  exact congrArg _ (sp_pt_eq _ _)

theorem topU_pt_eq (a b : (⊤ : (Sp K).Opens).toScheme) : a = b := Subtype.ext (sp_pt_eq _ _)

theorem isUnit_sub_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (c : R) (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a - c * b) := by
  by_contra h
  have hb' : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hb
  have h' : a - c * b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h'' := Ideal.add_mem _ h' (Ideal.mul_mem_left _ c hb')
  rw [sub_add_cancel] at h''
  exact (IsLocalRing.mem_maximalIdeal _).1 h'' ha

theorem gs_secSubScale {Y : Scheme.{0}} {P : LB Y} (a b : P.Sec) (c : Γ(Y, ⊤)) (y : Y) (k : P.ι) (hk : y ∈ P.U k) :
    gs (𝟙 Y) y _ ((DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k) =
      gs (𝟙 Y) y _ (a.f k) - gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (b.f k) := by
  have e : (DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k =
      a.f k - Out.resTop _ c * b.f k := by
    simp only [DVR.SecOps.secAdd, DVR.SecOps.secNeg, DVR.SecOps.secScale, sub_eq_add_neg]
  rw [e, LBGerm.gs_sub _ y _ hk, gs_mul _ y _ hk, Out.resTop, gs_res _ y _ hk]

theorem exists_sep_of_chart {Y T : Scheme.{0}} (π : Y ⟶ T) (u : T ⟶ Y) (hu : u ≫ π = 𝟙 T) (hT : ∀ a b : T, a = b)
    {P : LB Y} (hP : P.IsLB) {n : ℕ} (s : Fin n → P.Sec) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (i : Fin n) (hD : IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : Fin n → Γ(Y, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
            (Y.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r))
    (t₀ : T) (hi : u t₀ ∈ Out.nonzeroLocus (s i)) :
    ∃ t : Fin n → P.Sec, (∀ j, u t₀ ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, y ≠ u t₀ → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  classical
  have hTle : ⊤ ≤ u ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t _ => by rw [hT t t₀]; exact hi
  let c : Fin n → Γ(T, ⊤) := fun j => (u.appLE (Out.nonzeroLocus (s i)) ⊤ hTle).hom (r j)
  let φ := (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom
  have hc : ∀ (y : Y) (x : Γ(T, ⊤)), gs (𝟙 Y) y ⊤ (π.appTop.hom x) = gs π y ⊤ x := fun y x =>
    (gs_pull (𝟙 Y) π y ⊤ trivial x).trans (by rw [Category.id_comp])
  have hφ : ∀ y ∈ Out.nonzeroLocus (s i), ∀ x, gs (𝟙 Y) y _ (φ x) = gs π y ⊤ x := fun y hy x =>
    (gs_appLE π ⊤ _ le_top (𝟙 Y) y hy x).trans (by rw [Category.id_comp])
  have hrel : ∀ j k y, y ∈ Out.nonzeroLocus (s i) → y ∈ P.U k →
      gs (𝟙 Y) y _ ((s j).f k) = gs (𝟙 Y) y _ (r j) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro j k y hyD hk
    have hm : y ∈ Out.nonzeroLocus (s i) ⊓ P.U k := ⟨hyD, hk⟩
    have e := congrArg (gs (𝟙 Y) y (Out.nonzeroLocus (s i) ⊓ P.U k)) (hr j k)
    rwa [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  have hkey : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j k, y ∈ P.U k →
      gs (𝟙 Y) y _ ((DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))).f k) =
        gs (𝟙 Y) y _ (r j - φ (c j)) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro y hy j k hk
    rw [gs_secSubScale _ _ _ y k hk, hrel j k y hy hk, hc, LBGerm.gs_sub _ y _ hy, hφ y hy]
    ring
  have hiff : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j,
      y ∈ Out.nonzeroLocus (DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))) ↔ y ∈ Y.basicOpen (r j - φ (c j)) := by
    intro y hy j
    obtain ⟨k, hk⟩ := exists_chart hP y
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, hkey y hy j k hk, IsUnit.mul_iff,
      ← GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk, LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy]
    exact and_iff_left hy
  have h0 : ∀ j, u t₀ ∉ Y.basicOpen (r j - φ (c j)) := by
    intro j h
    have hu1 := (LBGerm.isUnit_gs_iff u t₀ _ hi _).2 h
    have e1 : gs u t₀ _ (r j) = gs (𝟙 T) t₀ ⊤ (c j) :=
      ((gs_appLE u _ ⊤ hTle (𝟙 T) t₀ trivial (r j)).trans (by rw [Category.id_comp])).symm
    have e2 : gs u t₀ _ (φ (c j)) = gs (𝟙 T) t₀ ⊤ (c j) :=
      (gs_appLE π ⊤ _ le_top u t₀ hi (c j)).trans (by rw [hu])
    rw [LBGerm.gs_sub u t₀ _ hi, e1, e2, sub_self] at hu1
    exact not_isUnit_zero hu1
  refine ⟨fun j => DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i))),
    fun j h => h0 j ((hiff _ hi j).1 h), fun y hy => ?_⟩
  by_cases hyD : y ∈ Out.nonzeroLocus (s i)
  · by_contra hno
    push_neg at hno
    have hPy : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal := fun j => by
      by_contra h
      exact hno j ((hiff y hyD j).2 ((mem_basicOpen_iff_prime hD hyD _).2 h))
    have hQ : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := fun j => by
      by_contra h
      exact h0 j ((mem_basicOpen_iff_prime hD hi _).2 h)
    have hb : ∀ z ∈ Out.nonzeroLocus (s i), ∀ x, z ∈ Y.basicOpen (φ x) ↔ π z ∈ T.basicOpen x := fun z hz x =>
      (LBGerm.isUnit_gs_iff (𝟙 Y) z _ hz (φ x)).symm.trans (by rw [hφ z hz]; exact LBGerm.isUnit_gs_iff π z ⊤ trivial x)
    have hPQ : ∀ x, φ x ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal ↔ φ x ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := by
      intro x
      rw [← not_iff_not, ← mem_basicOpen_iff_prime hD hyD, ← mem_basicOpen_iff_prime hD hi, hb y hyD, hb _ hi,
        hT (π y) (π (u t₀))]
    have hE := ideal_eq_of_gen φ r c hs _ _ hPy hQ hPQ
    have e1 := hD.fromSpec_primeIdealOf ⟨y, hyD⟩
    have e2 := hD.fromSpec_primeIdealOf ⟨u t₀, hi⟩
    rw [PrimeSpectrum.ext hE] at e1
    exact hy (e1.symm.trans e2)
  · have hy' : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨k, hk⟩ := exists_chart hP y
    refine ⟨j, ?_⟩
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, gs_secSubScale _ _ _ y k hk]
    exact isUnit_sub_mul_of_not_isUnit _ ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s j) hk).1 hj)
      fun h => hyD ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk).2 h)

theorem exists_sec_sep_origin : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB →
    Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)),
      (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  intro K _ B L hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  obtain ⟨t₀⟩ : Nonempty (⊤ : (Sp K).Opens).toScheme := ⟨⟨IsLocalRing.closedPoint K, trivial⟩⟩
  have hmem : unitU B t₀ ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨t, h1, h2⟩ := exists_sep_of_chart (B.X.hom ∣_ ⊤) (unitU B) (unitU_comp B) topU_pt_eq
    (LB.isLB_linComb hL _ _) s hcov i hD r hr hsurj t₀ hi
  have hinj : ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y = unitU B t₀ := fun y hy =>
    Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans
      (hy.trans ((unitU_ι B t₀).symm.trans (Scheme.Opens.ι_apply _ _))))
  exact ⟨N, hN, M + 1, t, fun j y hy => hinj y hy ▸ h1 j, fun y hy => h2 y fun h => hy (h ▸ unitU_ι B t₀)⟩

end GlobalTheory.RelAmpleSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFactorStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appell_humbert_factor : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.AHBundle.exists_lb_of_hermitian_int | exact GlobalTheory.AHBundle.exists_lb_of_hermitian_int | (intros; apply GlobalTheory.AHBundle.exists_lb_of_hermitian_int <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponentialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | exact GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | (intros; apply GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_theta_term_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  first | exact @GlobalTheory.Poinc.IntTerm.IntPoint.main | exact GlobalTheory.Poinc.IntTerm.IntPoint.main | (intros; apply GlobalTheory.Poinc.IntTerm.IntPoint.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiextensionGeneratorBezoutCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biextension_generator_bezout_combination : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  first | exact @GlobalTheory.Mum.LamComb.exists_gen_lam_comb | exact GlobalTheory.Mum.LamComb.exists_gen_lam_comb | (intros; apply GlobalTheory.Mum.LamComb.exists_gen_lam_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellPointBasicOpenAffineSpaceCoordsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCell_point_basicOpen_affineSpace_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ g : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1), ¬ IsNilpotent (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g) ∧ (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y₀ TF.X Z) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W), IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g)) → ⊤ ≤ z₀ ⁻¹ᵁ U₀ TF.X Z) ∧ ∃ (z : Sp (Localization.Away g) ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∀ r, ev z W hz (((toBase TF Z).appLE U.1 W h.2.1).hom r) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.C r)) ∧ ∀ i, ev z W hz (cellCoord N i) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.X i) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section | exact GlobalTheory.LogPole.exists_cell_section | (intros; apply GlobalTheory.LogPole.exists_cell_section <;> assumption)
end

