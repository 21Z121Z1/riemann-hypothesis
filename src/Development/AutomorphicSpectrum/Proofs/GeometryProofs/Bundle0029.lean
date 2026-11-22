import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj Limits

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def regIso (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => h.inj p (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩

def regPt (h : IsCptGen ξ) (p : Cpt ξ) : Sp (regAt ξ p) ⟶ X :=
  spMap (regIso h p).toRingHom ≫ X.fromSpecStalk p.1

theorem genMap_regIso_symm (h : IsCptGen ξ) (p : Cpt ξ) (a : regAt ξ p) :
    genMap ξ p ((regIso h p).symm a) = a := by
  exact congrArg Subtype.val ((regIso h p).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes {p q : Cpt ξ} (hs : q.1 ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ p s := by
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem regAt_le {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, genMap_specializes hs s⟩

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (x := ξ (IsLocalRing.closedPoint Ω)) (y := p.1) p.2,
    ← Category.assoc, ← Spec.map_comp] at h2
  exact h2

theorem spMap_algebraMap_regPt (h : IsCptGen ξ) (p : Cpt ξ) : spMap (algebraMap (regAt ξ p) Ω) ≫ regPt h p = ξ := by
  have e : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun x => rfl
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  exact spMap_genMap_fromSpecStalk p

abbrev regIncl {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p →+* regAt ξ q := Subring.inclusion (regAt_le hs)

theorem spMap_regIncl_regPt (h : IsCptGen ξ) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    spMap (regIncl hs) ≫ regPt h p = regPt h q := by
  have e : (regIncl hs).comp (regIso h p).toRingHom =
      (regIso h q).toRingHom.comp (X.presheaf.stalkSpecializes hs).hom :=
    RingHom.ext fun s => Subtype.ext (genMap_specializes hs s).symm
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

def castPt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : LieModel G y E := e ▸ M

theorem castPt_pt_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (a : E) :
    ((castPt e M).pt a).left = (M.pt a).left := by
  subst e
  rfl

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanChart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem spMap_fromSpec_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {D : Type} [CommRing D]
    (ψ : Γ(X, U) →+* D) :
    spMap ψ ≫ hU.fromSpec ≫ f = spMap (ψ.comp (f.appLE V U hUV).hom) ≫ hV.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ringHom_eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    {ψ ψ' : Γ(X, U) →+* D} (h : spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec) : ψ = ψ' := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_ringHom_of_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    (x : Sp D ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* D, x = spMap φ ≫ hU.fromSpec := by
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec (CommRingCat.of D))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change x = Spec.map (CommRingCat.ofHom (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem le_preimage_of_fst {X : Scheme.{0}} {U : X.Opens} {C : Type} [CommRing C] (x : Sp (DualNumber C) ⟶ X)
    (h : ∀ p, (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ x) p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom := fun c => ⟨TrivSqZeroExt.inl c, by simp⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ p.asIdeal := fun a ha => by
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  haveI := p.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  let p₀ : ↥(Sp C) := (⟨p.asIdeal.map (TrivSqZeroExt.fstHom C C C).toRingHom, hprime⟩ : PrimeSpectrum C)
  have hp : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  have e := h p₀
  simp only [Scheme.Hom.comp_apply] at e
  show x p ∈ U
  rw [← hp]
  exact e

theorem tan_iff_der (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C) :
    (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
    (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
       ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
    (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  intro h1
  have hal : ∀ c : C, algebraMap C (DualNumber C) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hy : y = spMap (u.comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    have hw := Over.w (1 : Over.mk y ⟶ G)
    rw [h1, Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV u] at hw
    exact hw.symm
  have hbase : spMap (algebraMap C (DualNumber C)) ≫ y =
      spMap (((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    rw [hy, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun φ hφ hb => ?_, fun v hv => ?_⟩
  · have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      ext b
      · simpa [hal] using hφ _
      · simpa [hal] using hb b
    refine ⟨Over.homMk (spMap φ ≫ hU.fromSpec) ?_, ?_, rfl⟩
    · change (spMap φ ≫ hU.fromSpec) ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y
      rw [Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV φ, hbase, hcomp]
    · have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
        ext a
        exact hφ a
      change spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap φ ≫ hU.fromSpec = _
      rw [h1, ← Category.assoc, ← Spec.map_comp, ← hfst]
      rfl
  · have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans h1
    have hle : ⊤ ≤ v.left ⁻¹ᵁ U := by
      refine le_preimage_of_fst v.left fun p => ?_
      rw [hv']
      simp only [Scheme.Hom.comp_apply]
      exact hU.range_fromSpec.subset (Set.mem_range_self _)
    obtain ⟨φ, hφ⟩ := exists_ringHom_of_le hU v.left hle
    have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
      apply ringHom_eq_of_fromSpec hU
      rw [← hv', hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      apply ringHom_eq_of_fromSpec hV
      rw [← hbase, ← spMap_fromSpec_hom G.hom hU hV hUV φ, ← Category.assoc, ← hφ]
      exact Over.w v
    refine ⟨φ, fun a => RingHom.congr_fun hfst a, fun b => ?_, hφ⟩
    have := RingHom.congr_fun hcomp b
    simpa [hal] using congrArg TrivSqZeroExt.snd this

end GlobalTheory.CompanionTheory.Ar.TanChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslateIntoSmallerOpen
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.Transl

theorem translates_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' _ g hg
  haveI := Γ.flat
  haveI := Γ.separated
  let p0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.bot_prime⟩
  have hp0 : p0 ⤳ Γ.G.hom g := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨g', hg'g, hg'⟩ := Flat.generalizingMap Γ.G.hom hp0
  obtain ⟨s, x, hx⟩ := Γ.pt_onto g' (by rw [hg'])
  have hsU : (Γ.pt s).left x ∈ U := by
    rw [hx]; exact hg'g.mem_open U.isOpen hg
  have hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    PrimeSpectrum.ext (by
      haveI := z.isPrime
      haveI := z'.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])
  have hsall : ∀ z, (Γ.pt s).left z ∈ U := fun z => hsub x z ▸ hsU
  have hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U := by
    rw [map_inv]; exact hU.inv _ _ hsall
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.T.finite_point_extends_section R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)
  refine ⟨σ, s⁻¹, hσ, ?_⟩
  set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ
  have hτpt : Γ.pt s ≫ τ = 1 := by
    rw [hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ,
      Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]
  have hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x) := by
    have h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left := by
      rw [hτpt, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 := congrArg (fun h => h x) h1
    simpa using h2
  have hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _ := Over.w _
  haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed (η[Γ.G]).left :=
    UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom
  have hcl : IsClosed (Set.range (η[Γ.G]).left) := by
    have h := (η[Γ.G]).left.isClosedMap _ isClosed_univ
    rwa [Set.image_univ] at h
  have hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g := by
    rw [hx]; exact hg'g.map τ.left.continuous
  have hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left :=
    Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩
  have hmem : τ.left g ∈ Set.range (η[Γ.G]).left :=
    closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)
  obtain ⟨z, hz⟩ := hmem
  rw [← hz]
  exact hU'.one z

end GlobalTheory.CompanionTheory.Ar.BT.Transl
end

