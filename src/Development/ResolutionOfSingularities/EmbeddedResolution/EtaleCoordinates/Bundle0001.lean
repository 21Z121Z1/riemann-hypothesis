import Mathlib

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))

abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)

def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := rfl

def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down

@[simp]
theorem coordVectorInl_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (a : Fin n) :
    coordVectorInl n m f (ULift.up (Sum.inl a)) = pullbackCoord f (ULift.up a) := rfl

@[simp]
theorem coordVectorInl_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (b : Fin m) :
    coordVectorInl n m f (ULift.up (Sum.inr b)) = 0 := rfl

def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down

@[simp]
theorem coordVectorInr_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (a : Fin n) :
    coordVectorInr n m f (ULift.up (Sum.inl a)) = 0 := rfl

@[simp]
theorem coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartAlgebra
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}

noncomputable def chartCoeffHom (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Γ(X, W) →+* Γ(Y, V) :=
  (W.topIso.inv ≫ (g ≫ (AffineSpace n W.toScheme ↘ W.toScheme)).appTop ≫ V.topIso.hom).hom

noncomputable def chartVar (g : V.toScheme ⟶ AffineSpace n W.toScheme) (j : n) : Γ(Y, V) :=
  V.topIso.hom.hom (g.appTop.hom (AffineSpace.coord (S := W.toScheme) j))

noncomputable def chartEvalHom (_hW : IsAffineOpen W) (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    MvPolynomial n Γ(X, W) →+* Γ(Y, V) :=
  MvPolynomial.eval₂Hom (chartCoeffHom g) (chartVar g)

private theorem resLE_appTop_eq {X' Y' : Scheme.{u}} (h : Y' ⟶ X') (W' : X'.Opens)
    (V' : Y'.Opens) (e : V' ≤ h ⁻¹ᵁ W') :
    (h.resLE W' V' e).appTop = W'.topIso.hom ≫ h.appLE W' V' e ≫ V'.topIso.inv := by
  simp

private theorem resLE_appTop_conj_topIso_eq_appLE {X' Y' : Scheme.{u}} (h : Y' ⟶ X') (W' : X'.Opens) (V' : Y'.Opens)
    (e : V' ≤ h ⁻¹ᵁ W') :
    W'.topIso.inv ≫ (h.resLE W' V' e).appTop ≫ V'.topIso.hom = h.appLE W' V' e := by
  rw [resLE_appTop_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem chartEvalHom_comp_C (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    (chartEvalHom hW g).comp (MvPolynomial.C : Γ(X, W) →+* MvPolynomial n Γ(X, W)) =
      (h.appLE W V e).hom := by
  have key : chartCoeffHom g = (h.appLE W V e).hom := by
    simp only [chartCoeffHom, hg, resLE_appTop_conj_topIso_eq_appLE]
  refine RingHom.ext fun a => ?_
  have h1 : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
  rw [RingHom.comp_apply, h1, key]

theorem chartEvalHom_C (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) (a : Γ(X, W)) :
    chartEvalHom hW g (MvPolynomial.C a) = (h.appLE W V e).hom a :=
  RingHom.congr_fun (chartEvalHom_comp_C hW h e g hg) a

@[reducible]
noncomputable def chartAlgebra (hW : IsAffineOpen W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) :=
  (chartEvalHom hW g).toAlgebra

theorem chartAlgebra_isScalarTower (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    letI : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    IsScalarTower Γ(X, W) (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show (h.appLE W V e).hom a = chartEvalHom hW g (algebraMap Γ(X, W) (MvPolynomial n Γ(X, W)) a)
  rw [MvPolynomial.algebraMap_eq, chartEvalHom_C hW h e g hg]

private theorem algebraEtale_congr {R S : Type u} [CommRing R] [CommRing S] {f f' : R →+* S}
    (h : f = f') (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R S _ _ f'.toAlgebra := by
  subst h
  exact hf

private theorem algebraEtale_of_ringHomEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : RingHom.Etale f) : @Algebra.Etale R S _ _ f.toAlgebra := h

private theorem algebraEtale_comp_equiv {R R' S S' : Type u} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] (eR : R' ≃+* R) (f : R →+* S) (eS : S ≃+* S')
    (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R' S' _ _ (((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.Etale R S := hf
  let : Algebra R' R := (eR : R' →+* R).toAlgebra
  let : Algebra R S' := ((eS : S →+* S').comp f).toAlgebra
  let : Algebra R' S' := ((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra
  have : IsScalarTower R' R S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale R' R' := inferInstance
  have : Algebra.Etale R' R :=
    Algebra.Etale.of_equiv (R := R') (A := R') (AlgEquiv.ofRingEquiv (f := eR) fun _ => rfl)
  have : Algebra.Etale R S' :=
    Algebra.Etale.of_equiv (R := R) (A := S) (AlgEquiv.ofRingEquiv (f := eS) fun _ => rfl)
  exact Algebra.Etale.comp R' R S'

private theorem comp_appTop_apply {A B C : Scheme.{u}} (f : A ⟶ B) (k : B ⟶ C) (z : Γ(C, ⊤)) :
    (f ≫ k).appTop.hom z = f.appTop.hom (k.appTop.hom z) :=
  congrArg (fun m : Γ(C, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom m z) (Scheme.Hom.comp_appTop f k)

private theorem specMap_appTop_apply {R S : CommRingCat.{u}} (u : R ⟶ S) (a : R) :
    (Spec.map u).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) =
      (Scheme.ΓSpecIso S).inv.hom (u.hom a) :=
  (congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso_inv_naturality u)).symm

private theorem isoSpec_hom_appTop_apply (Z : Scheme.{u}) [IsAffine Z] (a : Γ(Z, ⊤)) :
    Z.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv.hom a) = a := by
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  exact congrArg (fun m : Γ(Z, ⊤) ⟶ Γ(Z, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso Γ(Z, ⊤)).inv_hom_id

private noncomputable def affineOpenIsoSpec {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W') :
    W'.toScheme ≅ Spec Γ(X', W') :=
  haveI : IsAffine W'.toScheme := hW
  W'.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso W'.topIso.symm.op

private theorem affineOpenIsoSpec_hom_appTop_apply {X' : Scheme.{u}} {W' : X'.Opens}
    (hW : IsAffineOpen W') (a : Γ(X', W')) :
    (affineOpenIsoSpec hW).hom.appTop.hom ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      W'.topIso.inv.hom a := by
  have : IsAffine W'.toScheme := hW
  show (W'.toScheme.isoSpec.hom ≫ Spec.map W'.topIso.symm.hom).appTop.hom
      ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) = W'.topIso.inv.hom a
  rw [comp_appTop_apply, specMap_appTop_apply, isoSpec_hom_appTop_apply]
  rfl

private noncomputable def affineSpaceOpenIsoSpecMvPolynomial {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) :
    AffineSpace m W'.toScheme ≅ Spec (CommRingCat.of (MvPolynomial m Γ(X', W'))) :=
  (AffineSpace.functor.obj (Opposite.op m)).mapIso (affineOpenIsoSpec hW) ≪≫
    AffineSpace.SpecIso m Γ(X', W')

private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) (j : m) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.X j)) =
      AffineSpace.coord W'.toScheme j := by
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord (Spec Γ(X', W')) j := by
    rw [← AffineSpace.SpecIso_inv_appTop_coord, ← comp_appTop_apply, Iso.hom_inv_id]
    simp
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord W'.toScheme j
  rw [comp_appTop_apply, key, AffineSpace.map_appTop_coord]

private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) (a : Γ(X', W')) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a) := by
  have h1 : (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(X', W') →+* MvPolynomial m Γ(X', W')))).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a) :=
    specMap_appTop_apply _ a
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m (Spec Γ(X', W')) ↘ Spec Γ(X', W')).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) := by
    rw [← h1, ← comp_appTop_apply, ← AffineSpace.SpecIso_inv_over, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a)
  rw [comp_appTop_apply, key, ← comp_appTop_apply, AffineSpace.map_over, comp_appTop_apply,
    affineOpenIsoSpec_hom_appTop_apply]

theorem chartAlgebra_etale (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have hEt : Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom) := inferInstance
  have hr : RingHom.Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hEt
  have hAlg := algebraEtale_of_ringHomEtale _ hr
  have h2 := algebraEtale_comp_equiv
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).symm.commRingCatIsoToRingEquiv
    (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom V.topIso.commRingCatIsoToRingEquiv hAlg
  refine algebraEtale_congr ?_ h2
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · have hC : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
    show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.C a))) = chartEvalHom hW g (MvPolynomial.C a)
    rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C, ← comp_appTop_apply, hC]
    rfl
  · show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.X j))) = chartEvalHom hW g (MvPolynomial.X j)
    rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X]
    simp [chartEvalHom, chartVar]

theorem chartAlgebra_formallyEtale (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.FormallyEtale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra_etale hW hV g
  infer_instance

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]

section

variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S (MvPolynomial.X i)

theorem coord_def (i : ι) :
    coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl

end

section

variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]

include ι

private theorem exists_basisKaehler :
    ∃ b : Module.Basis ι S (KaehlerDifferential k S),
      ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i) := by
  have h : IsBaseChange S (KaehlerDifferential.map k k (MvPolynomial ι k) S) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial ι k) S
  refine ⟨(Algebra.TensorProduct.basis S
    (KaehlerDifferential.mvPolynomialBasis k ι)).map h.equiv, fun i => ?_⟩
  simp only [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]
  rfl

noncomputable def basisKaehler : Module.Basis ι S (KaehlerDifferential k S) :=
  (exists_basisKaehler k ι S).choose

@[simp] theorem basisKaehler_apply (i : ι) :
    basisKaehler k ι S i = KaehlerDifferential.D k S (coord k ι S i) :=
  (exists_basisKaehler k ι S).choose_spec i

private noncomputable def partialDerivFun (i : ι) (s : S) : S :=
  (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i

private theorem partialFun_map_add (i : ι) :
    ∀ x y : S, partialDerivFun k ι S i (x + y) = partialDerivFun k ι S i x + partialDerivFun k ι S i y := by
  intro x y
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (x + y)) i
      = (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
        + (basisKaehler k ι S).repr (KaehlerDifferential.D k S y) i
  rw [map_add, map_add, Finsupp.add_apply]

private theorem partialFun_map_smul (i : ι) :
    ∀ (c : k) (x : S),
      partialDerivFun k ι S i (c • x) = (RingHom.id k) c • partialDerivFun k ι S i x := by
  intro c x
  have h1 : c • x = algebraMap k S c * x := Algebra.smul_def c x
  have h2 : KaehlerDifferential.D k S (c • x)
      = algebraMap k S c • KaehlerDifferential.D k S x := by
    rw [h1, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  show (basisKaehler k ι S).repr (KaehlerDifferential.D k S (c • x)) i
      = c • (basisKaehler k ι S).repr (KaehlerDifferential.D k S x) i
  rw [h2, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def]

private noncomputable def partialDerivLinear (i : ι) : S →ₗ[k] S where
  toFun := partialDerivFun k ι S i
  map_add' := partialFun_map_add k ι S i
  map_smul' := partialFun_map_smul k ι S i

private theorem partialLinear_leibniz (i : ι) :
    ∀ a b : S, partialDerivLinear k ι S i (a * b)
      = a • partialDerivLinear k ι S i b + b • partialDerivLinear k ι S i a := by
  intro a b
  have h : KaehlerDifferential.D k S (a * b)
      = a • KaehlerDifferential.D k S b + b • KaehlerDifferential.D k S a :=
    (KaehlerDifferential.D k S).leibniz a b
  have h2 : (basisKaehler k ι S).repr (KaehlerDifferential.D k S (a * b)) i
      = a * (basisKaehler k ι S).repr (KaehlerDifferential.D k S b) i
        + b * (basisKaehler k ι S).repr (KaehlerDifferential.D k S a) i := by
    rw [h, map_add, Finsupp.add_apply, LinearEquiv.map_smul, LinearEquiv.map_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  exact h2

noncomputable def partialDeriv (i : ι) : Derivation k S S :=
  Derivation.mk' (partialDerivLinear k ι S i) (partialLinear_leibniz k ι S i)

theorem partialDeriv_apply (i : ι) (s : S) :
    partialDeriv k ι S i s = (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i := rfl

@[simp] theorem partialDeriv_coord [DecidableEq ι] (i j : ι) :
    partialDeriv k ι S i (coord k ι S j) = if i = j then (1 : S) else 0 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S j, Module.Basis.repr_self,
    Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem partialDeriv_coord_self (i : ι) :
    partialDeriv k ι S i (coord k ι S i) = 1 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S i, Module.Basis.repr_self,
    Finsupp.single_eq_same]

theorem partialDeriv_coord_of_ne (i j : ι) (h : i ≠ j) :
    partialDeriv k ι S i (coord k ι S j) = 0 := by
  classical
  rw [partialDeriv_coord k ι S i j, if_neg h]

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem sum_smul_derivation_apply (c : ι → S) (f : ι → Derivation k S S)
    (s : S) (t : Finset ι) :
    (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i * f i s := by
  induction t using Finset.cons_induction_on
  · simp
  · rename_i a u hu ih
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

theorem span_range_partialDeriv [Finite ι] :
    Submodule.span S (Set.range (partialDeriv k ι S)) = (⊤ : Submodule S (Derivation k S S)) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  refine Submodule.eq_top_iff'.mpr fun D => ?_
  have key : D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
    ext s
    have h1 : ∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i)
        = KaehlerDifferential.D k S s := by
      rw [← Module.Basis.sum_repr (basisKaehler k ι S) (KaehlerDifferential.D k S s)]
      exact Finset.sum_congr rfl fun i _ => by rw [basisKaehler_apply, partialDeriv_apply]
    have h2 : D.liftKaehlerDifferential
        (∑ i : ι, partialDeriv k ι S i s • KaehlerDifferential.D k S (coord k ι S i))
        = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by rw [h1]
    simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D] at h2
    rw [sum_smul_derivation_apply, ← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact sum_mem fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem eq_sum_smul_partialDeriv [Fintype ι] (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
  ext s
  have hsum : (∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i) s
      = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i s :=
    sum_smul_derivation_apply k ι S (fun i => D (coord k ι S i))
      (partialDeriv k ι S) s Finset.univ
  rw [hsum]
  have h1 : D s = D.liftKaehlerDifferential (KaehlerDifferential.D k S s) := by
    rw [Derivation.liftKaehlerDifferential_comp_D]
  have h2 : KaehlerDifferential.D k S s
      = ∑ i : ι, (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i
          • basisKaehler k ι S i :=
    ((basisKaehler k ι S).sum_repr (KaehlerDifferential.D k S s)).symm
  rw [h1, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    ← partialDeriv_apply]
  exact mul_comm _ _

private theorem exists_basisDerivation [Fintype ι] [DecidableEq ι] :
    ∃ b : Module.Basis ι S (Derivation k S S), ∀ i : ι, b i = partialDeriv k ι S i := by
  have hli : LinearIndependent S (partialDeriv k ι S) := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    have h0 : (∑ i ∈ s, g i • partialDeriv k ι S i) (coord k ι S j) = 0 := by
      rw [hg]
      simp
    rw [sum_smul_derivation_apply k ι S g (partialDeriv k ι S)
      (coord k ι S j) s] at h0
    have key : ∑ i ∈ s, g i * partialDeriv k ι S i (coord k ι S j)
        = g j * partialDeriv k ι S j (coord k ι S j) := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro i _ hij
        rw [partialDeriv_coord_of_ne k ι S i j hij, mul_zero]
      · intro hj'
        exact absurd hj hj'
    rw [key, partialDeriv_coord_self, mul_one] at h0
    exact h0
  have hsp : ⊤ ≤ Submodule.span S (Set.range (partialDeriv k ι S)) :=
    (span_range_partialDeriv k ι S).ge
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

noncomputable def basisDerivation [Fintype ι] [DecidableEq ι] :
    Module.Basis ι S (Derivation k S S) :=
  (exists_basisDerivation k ι S).choose

@[simp] theorem basisDerivation_apply [Fintype ι] [DecidableEq ι] (i : ι) :
    basisDerivation k ι S i = partialDeriv k ι S i :=
  (exists_basisDerivation k ι S).choose_spec i

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

