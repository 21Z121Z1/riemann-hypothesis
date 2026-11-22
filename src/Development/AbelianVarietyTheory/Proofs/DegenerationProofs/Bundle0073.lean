import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ToImm
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep

theorem ext_local {T X : Scheme.{0}} (f g : T ⟶ X)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ T), y ≫ f = y ≫ g) : f = g :=
  ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t =>
    @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)

theorem exists_hom_of_ringHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (φ : Γ(X, U) →+* Γ(Y, V)) : ∃ g : V.toScheme ⟶ X, ∀ (R : Type) [CommRing R] (y : Sp R ⟶ V.toScheme)
      (h : ⊤ ≤ (y ≫ V.ι) ⁻¹ᵁ V), ∃ h' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U,
        ∀ f, valHom (y ≫ g) U h' f = valHom (y ≫ V.ι) V h (φ f) := by
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))
  refine ⟨h', fun f => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec
      U ⊤ ⊤ h0 le_rfl).symm
  have h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  have h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  unfold valHom
  rw [h4]
  rfl

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

theorem eq_zero_of_dense {Y : Scheme.{0}} [IsReduced Y] {K : Type} [Field K] {A : Type}
    (x : A → (Sp K ⟶ Y)) (hd : Dense (⋃ a, Set.range (x a))) (V : Y.Opens) (f : Γ(Y, V))
    (hf : ∀ a (h : ⊤ ≤ x a ⁻¹ᵁ V), valHom (x a) V h f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw, hw'⟩ := hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hw'
  have h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f := fun t' _ => by
    have : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hw
  have h2 : ⊤ ≤ x a ⁻¹ᵁ V := h1.trans ((x a).preimage_mono (Y.basicOpen_le f))
  have := (isUnit_valR_iff (x a) V h2 f).2 h1
  rw [valR_eq _ _ h2, hf a h2] at this
  exact (not_isUnit_zero this).elim

theorem comp_eq_of_const {k R : Type} [CommRing k] [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    (p' : Y ⟶ Sp k) (x : Sp R ⟶ X) (y : Sp R ⟶ Y) {U : X.Opens} {V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ V) (e : ∀ a, valHom x U h (constFn p U a) = valHom y V h' (constFn p' V a)) :
    x ≫ p = y ≫ p' := by
  refine eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)
  obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f
  have := e a
  rw [valHom_constFn, valHom_constFn] at this
  exact this

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {H : LB X} {H' : LB Y}
  {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem exists_chart [IsReduced Y] (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ)
    {K : Type} [Field K] {A : Type} (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X))
    (hd : Dense (⋃ a, Set.range (x a)))
    (hx : ∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) (i : J) :
    ∃ g : (nonzeroLocus (s' i)).toScheme ⟶ X, ∀ (R : Type) [CommRing R] [IsLocalRing R]
      (y : Sp R ⟶ (nonzeroLocus (s' i)).toScheme),
      (y ≫ g) ≫ p = (y ≫ (nonzeroLocus (s' i)).ι) ≫ p' ∧
        ∀ v, Crd H' s' (y ≫ (nonzeroLocus (s' i)).ι) v → Crd H s (y ≫ g) v := by
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i (Set.mem_univ i)
  choose r' hr' using fun j =>
    (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists
  let ev := MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r
  let ev' := MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'
  have hs : Function.Surjective ev := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hk : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro f hf
    refine eq_zero_of_dense x hd _ _ fun a h => ?_
    obtain ⟨e, v, hv', hv⟩ := hx a
    have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
    have h' := (crd_isUnit_iff i hv).1 hu
    have : (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply,
          valHom_constFn, e]
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        have e := (crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')
        rw [valR_eq _ _ h, valR_eq _ _ h'] at e
        exact hu.mul_right_cancel e
    have := congrArg (fun q => q f) this
    simp only [RingHom.comp_apply] at this
    rw [this, (RingHom.mem_ker).1 hf, map_zero]
  let φ := RingHom.liftOfSurjective ev hs ⟨ev', hk⟩
  have hφ : ∀ f, φ (ev f) = ev' f := fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f
  have hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a := fun a => by
    have := hφ (MvPolynomial.C a)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply] using this
  have hφr : ∀ j, φ (r j) = r' j := fun j => by
    have := hφ (MvPolynomial.X j)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_X'] using this
  obtain ⟨g, hg⟩ := exists_hom_of_ringHom hA _ φ
  refine ⟨g, fun R _ _ y => ?_⟩
  have h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i) := fun z _ => (y z).2
  obtain ⟨h', hv⟩ := hg R y h
  refine ⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩
  obtain ⟨w, hw⟩ := crd_exists hH s (y ≫ g)
  have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
  have hu' : IsUnit (w i) := (crd_isUnit_iff i hw).2 h'
  have := crd_smul (hu.unit * hu'.unit⁻¹) hw
  convert this using 2 with j
  rw [crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr,
    mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]

theorem exists_factor : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  intro k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx
  choose g hg using exists_chart hH hH' hI x x' hd hx
  let 𝒰 := Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc
  have hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i =
      pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j := by
    intro i j
    refine ext_local _ _ fun R _ _ y => ?_
    have e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι =
        (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨a₁, b₁⟩ := hg i R (y ≫ pullback.fst _ _)
    obtain ⟨a₂, b₂⟩ := hg j R (y ≫ pullback.snd _ _)
    obtain ⟨v, hv⟩ := crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)
    rw [← Category.assoc, ← Category.assoc]
    exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))
  have hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i :=
    fun i => 𝒰.ι_glueMorphisms g hcomp i
  have key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y),
      (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧
        ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v := by
    intro R _ _ y
    have : y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have h := (top_le_iff y _).2 hi
    have hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact h (Set.mem_univ z)
    have e := IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr
    have := hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)
    rwa [← hG i, ← Category.assoc, e] at this
  refine ⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_,
    fun R _ _ y => (key R y).2⟩
  · rw [← Category.assoc, (key R y).1]
  · obtain ⟨e, v, hv', hv⟩ := hx a
    exact eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv

end GlobalTheory.ZH.ToImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology

theorem exists_lift_valR {O T : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] (π : O →+* T)
    [IsLocalHom π] {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (c : Sp O ⟶ X) (ce : Sp T ⟶ Y)
    (h : ce ≫ i = spMap π ≫ c) (U : Y.Opens) (hU : ⊤ ≤ ce ⁻¹ᵁ U) (f : Γ(Y, U)) :
    ∃ (U' : X.Opens) (f' : Γ(X, U')), ⊤ ≤ c ⁻¹ᵁ U' ∧ π (valR c U' f') = valR ce U f := by
  have hy : ce (cpt T) ∈ U := hU trivial
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (ce (cpt T)) ((Y.presheaf.germ U _ hy).hom f)
  obtain ⟨U', hU', f', rfl⟩ := X.presheaf.germ_exist a
  have hcl : spMap π (cpt T) = cpt O := IsLocalRing.comap_closedPoint π
  have h1 : (spMap π ≫ c) (cpt T) ∈ U' := by rw [← h]; exact hU'
  have h2 : ⊤ ≤ c ⁻¹ᵁ U' := (top_le_iff_cpt c U').2 (by rw [← hcl]; exact h1)
  refine ⟨U', f', h2, toStkA_injective ?_⟩
  rw [toStkA_map_valR π c U' _ h2, toStkA_valR_eq_gs ce U _ hU, ← h, ← gs_pull ce i _ U' hU',
    gs_eq ce _ U hy, gs_eq ce _ (i ⁻¹ᵁ U') hU', ← Scheme.Hom.germ_stalkMap_apply ce U _ hy,
    ← Scheme.Hom.germ_stalkMap_apply ce (i ⁻¹ᵁ U') _ hU', ← ha]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply i U' _ hU' f').symm

variable {p : ℕ} [Fact p.Prime]

theorem exists_finite_values {V : Type} [CommRing V] (j : V →+* OO p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hj : ∀ x, (j x : PadicAlgCl p) ∈ K₀) {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (c : Sp (OO p) ⟶ X) (hc : c ≫ s = spMap j) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      ∀ (U : X.Opens), ⊤ ≤ c ⁻¹ᵁ U → ∀ f, ((valR c U f : OO p) : PadicAlgCl p) ∈ K := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := c (cpt _)) (U := ⊤) trivial
  have hWt : ⊤ ≤ c ⁻¹ᵁ W := (top_le_iff_cpt c W).2 hyW
  have hft : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  letI := (s.appLE ⊤ W le_top).hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.1
  let φ : Γ(X, W) →+* PadicAlgCl p := (OO p).subtype.comp (CrdCalc.valHom c W hWt)
  have hφ : ∀ f, φ f = ((valR c W f : OO p) : PadicAlgCl p) := fun f => by
    rw [CrdCalc.valR_eq c W hWt]; rfl
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))) :=
    haveI : Finite (φ '' (t : Set Γ(X, W))) := ((t.finite_toSet).image φ).to_subtype
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W))), inferInstance, ?_⟩
  set K := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))
  have hall : ∀ f, φ f ∈ K := fun f => by
    have hf : f ∈ Algebra.adjoin Γ(Sp V, ⊤) (t : Set Γ(X, W)) := ht ▸ trivial
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      refine (le_sup_left : _ ≤ K) ?_
      have e : (s.appLE ⊤ W le_top ≫ c.appLE W ⊤ hWt ≫ (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom) =
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom ≫ CommRingCat.ofHom j := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]
        refine congrArg (· ≫ _) ((Scheme.Hom.appLE_comp_appLE c s ⊤ W ⊤ le_top hWt).trans ?_)
        simp only [hc]
        rfl
      have e' : CrdCalc.valHom c W hWt (algebraMap Γ(Sp V, ⊤) Γ(X, W) r) =
        j ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) := congrArg (fun q => q.hom r) e
      have := hj ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r)
      rw [← e'] at this
      exact this
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  intro U hU f
  obtain ⟨g, hgU, hyg⟩ := hW.exists_basicOpen_le ⟨c (cpt _), hU trivial⟩ hyW
  have hgt : ⊤ ≤ c ⁻¹ᵁ X.basicOpen g := (top_le_iff_cpt c _).2 hyg
  have := hW.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (resG X hgU f)
  have e2 := congrArg (valR c (X.basicOpen g)) e
  rw [CrdCalc.valR_mul c _ hgt, CrdCalc.valR_res c hgU hgt] at e2
  have r1 : ∀ b : Γ(X, W), valR c (X.basicOpen g) (algebraMap Γ(X, W) Γ(X, X.basicOpen g) b) = valR c W b :=
    fun b => CrdCalc.valR_res c (X.basicOpen_le g) hgt b
  rw [r1, r1] at e2
  have hu : IsUnit (valR c W g) := (CrdCalc.isUnit_valR_iff c W hWt g).2 hgt
  have hg0 : φ (g ^ n) ≠ 0 := by
    rw [map_pow, hφ]
    exact pow_ne_zero _ (hu.map (OO p).subtype).ne_zero
  have e3 : ((valR c U f : OO p) : PadicAlgCl p) = φ a / φ (g ^ n) := by
    rw [eq_div_iff hg0, hφ, hφ]
    exact congrArg Subtype.val e2
  rw [e3]
  exact div_mem (hall _) (hall _)

theorem exists_tendsto (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {r : ℝ}
    (hr : r < 1) (ω : ℕ → PadicAlgCl p) (hK : ∀ e, ω e ∈ K) (h : ∀ e, ‖ω (e + 1) - ω e‖ ≤ r ^ (e + 1)) :
    ∃ a, Tendsto ω atTop (𝓝 a) := by
  have hc : CauchySeq ω := cauchySeq_of_le_geometric r r hr fun e => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h e
  haveI : FiniteDimensional ℚ_[p] K.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[p] K)
  obtain ⟨a, -, ha⟩ := cauchySeq_tendsto_of_isComplete K.toSubmodule.complete_of_finiteDimensional hK hc
  exact ⟨a, ha⟩

theorem hasSum_of_levels {Ix : Type} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) (x : Ix → PadicAlgCl p)
    (s : ℕ → PadicAlgCl p) (a : PadicAlgCl p) (hs : Tendsto s atTop (𝓝 a))
    (h : ∀ e, ∃ S : Finset Ix, ∀ T, S ⊆ T → ‖s e - ∑ i ∈ T, x i‖ ≤ r ^ (e + 1)) : HasSum x a := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have h1 := (Metric.tendsto_nhds.1 hs) (ε / 2) (half_pos hε)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).comp (tendsto_add_atTop_nat 1)
  have h3 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨e, he1, he2⟩ := (h1.and h3).exists
  obtain ⟨S, hS⟩ := h e
  refine ⟨S, fun T hT => ?_⟩
  have := hS T hT
  rw [← dist_eq_norm, dist_comm] at this
  have h4 := dist_triangle (∑ i ∈ T, x i) (s e) a
  simp only [Function.comp] at he2
  linarith

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section

namespace GlobalTheory

open GtBaseChange in

theorem exists_gtDatum_baseChange_maps :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  intro S S' f E G _ d
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨extBC f E, AddEquiv.refl _,
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }, pullback.fst E.B.hom f,
    isGrpPullback_pullback E.B f, hq, fun χ => GtBaseChange.lbIso_refl (pull_isLB (E.O χ).isLB _),
    fun Z τ => ?_⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)
  · have hτ : (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ (splitTorus S E.X).hom =
        (splitTorus S' E.X).hom ≫ f := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)
    refine ⟨pushPt hτ τ, ?_, fun χ z => ?_⟩
    · change (τ.left ≫ eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ d.i.left =
        (τ.left ≫ i.left) ≫ pullback.fst G.hom f
      exact (Category.assoc _ _ _).trans
        ((congrArg (τ.left ≫ ·) hi.symm).trans (Category.assoc _ _ _).symm)
    · have e₂ : charUnit S' E.X χ =
          pullU (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ⊤ (charUnit S E.X χ) :=
        Units.ext (hT χ).symm
      refine Eq.trans ?_ (congrArg (gm τ.left z ⊤) e₂).symm
      exact (gm_pull τ.left _ z ⊤ trivial _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ker_le_ker_of_range_subset_of_isReduced {X T Y : Scheme.{0}} [IsReduced T] (f : X ⟶ Y)
    [IsClosedImmersion f] (g : T ⟶ Y) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g
    ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact f.range_subset_ker_support

theorem exists_iso_isMonHom_of_isGt_of_range_eq :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Over (Sp k)) (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (f : G ⟶ Y) (f' : G' ⟶ Y), E.IsGt G → E'.IsGt G' → IsClosedImmersion f.left → IsClosedImmersion f'.left → Set.range f.left = Set.range f'.left → η[G] ≫ f = η[G'] ≫ f' → ∃ e : G ≅ G', IsMonHom e.hom ∧ e.hom ≫ f' = f := by
  intro k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1
  have hs := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1
  have hs' := (UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have hk : f'.left.ker = f.left.ker :=
    le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le)
      (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)
  have := IsClosedImmersion.isIso_lift f'.left f.left hk
  have hl := IsClosedImmersion.lift_fac f'.left f.left hk.le
  let e : G ≅ G' := Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by
    rw [asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])
  have he : e.hom ≫ f' = f := Over.OverMorphism.ext hl
  have : Mono f' := Over.mono_of_mono_left f'
  refine ⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩
  rw [← cancel_mono f', Category.assoc, he, h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRepStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomial_matrices_projectiveRep : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_monomial_matrices | exact GlobalTheory.ThetaReal.exists_monomial_matrices | (intros; apply GlobalTheory.ThetaReal.exists_monomial_matrices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOriginStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_mulPull_iso_origin : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  first | exact @GlobalTheory.ThetaReal.exists_normalised_mulPull | exact GlobalTheory.ThetaReal.exists_normalised_mulPull | (intros; apply GlobalTheory.ThetaReal.exists_normalised_mulPull <;> assumption)
end

