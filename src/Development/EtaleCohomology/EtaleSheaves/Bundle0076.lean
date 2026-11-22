import Development.EtaleCohomology.EtaleSheaves.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0073

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLiftNonconstOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.NonconstantLift

theorem dim_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) = topologicalKrullDim (U : Set X) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  symm
  exact IsHomeomorph.topologicalKrullDim_eq _ (hU.isoSpec.hom.homeomorph).isHomeomorph

theorem appTop_eq {k Ω : Type} [Field k] [Field Ω] (f : CommRingCat.of k ⟶ CommRingCat.of Ω)
    (g : Sp Ω ⟶ Sp k) (hg : g = Spec.map f) (e) : g.appLE ⊤ ⊤ e = (Spec.map f).appTop := by
  subst hg
  first
  | exact Scheme.Hom.appLE_eq_app _
  | (simp only [Scheme.Hom.appLE]; exact (CategoryTheory.Category.comp_id _).trans rfl)
  | (simp only [Scheme.Hom.appLE]; erw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl)
  | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; convert Category.comp_id _ using 2; exact (Subsingleton.elim _ _ : (homOfLE e).op = 𝟙 _) ▸ rfl)

theorem stalk_inj {X : Scheme.{0}} [IsIntegral X] {x : X} (hx : x = genericPoint X) {T : CommRingCat}
    [Nontrivial T] (f : X.presheaf.stalk x ⟶ T) : Function.Injective f.hom := by
  subst hx
  exact (f.hom : X.functionField →+* T).injective

theorem key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω] (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ R : Subalgebra k Ω, R.FG ∧ ringKrullDim R = ringKrullDim Γ(X, U) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hle : (⊤ : (Sp Ω).Opens) ≤ φ ⁻¹ᵁ U := fun z _ => by
    show φ z ∈ U
    rw [hη z]; exact hηU
  have hU' : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let α : k →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU').hom
  let ψ : Γ(X, U) →+* Ω := (φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
  have hcomp : ψ.comp α = algebraMap k Ω := by
    have h1 : p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle =
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appTop_eq _ _ hφ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap k Ω) := by
      rw [reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    ext a
    simpa [α, ψ] using congrArg (fun g => (CommRingCat.Hom.hom g) a) h2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have hs' : (φ.appLE U ⊤ hle).hom s = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom hs
      simpa [ψ] using this
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    have h3 := Scheme.Hom.germ_stalkMap_apply φ U z (hle trivial) s
    have h4 : (X.presheaf.germ U (φ z) (hle trivial)).hom s = 0 := by
      apply stalk_inj (hη z) (φ.stalkMap z)
      rw [h3, map_zero]
      have := congrArg ((Sp Ω).presheaf.germ ⊤ z (show z ∈ (⊤ : (Sp Ω).Opens) from Set.mem_univ z)).hom hs'
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero] at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      exact this
    exact germ_injective_of_isIntegral X (φ z) (hle trivial) (by rw [map_zero]; exact h4)
  let _ : Algebra k Γ(X, U) := α.toAlgebra
  let ψa : Γ(X, U) →ₐ[k] Ω := { ψ with commutes' := fun a => DFunLike.congr_fun hcomp a }
  have hft : α.FiniteType := by
    have := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU hU'
    exact RingHom.FiniteType.comp this (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  have : Algebra.FiniteType k Γ(X, U) := hft
  refine ⟨ψa.range, ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  · exact (ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective ψa hinj).toRingEquiv).symm

theorem dim_contra {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω]
    (hdim : ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X) (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) : False := by
  have hU : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨W, hW, hx⟩
  choose V hV hxV using hU
  have hlt : ∀ x, topologicalKrullDim (V x : Set X) < topologicalKrullDim X := fun x => by
    obtain ⟨R, hR, hRd⟩ := key p φ hφ hη (hV x) ⟨x, hxV x⟩
    rw [← dim_affine (hV x), ← hRd]
    exact hdim R hR
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hne : t.Nonempty := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨i, hi⟩
  have hle : topologicalKrullDim X ≤ t.sup' hne (fun i => topologicalKrullDim (V i : Set X)) := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨V i, (V i).isOpen, hx, Finset.le_sup' (fun i => topologicalKrullDim (V i : Set X)) hi⟩
  exact lt_irrefl _ (hle.trans_lt ((Finset.sup'_lt_iff hne).2 fun i _ => hlt i))

theorem LeafLiftNonconst_of : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen y
  by_contra! hcon
  obtain ⟨_, _, _⟩ := id hc0
  have hsnd : ∀ a, e a = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm a) := fun a => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hconst : ∀ a, e a = genericPoint X := by
    obtain ⟨b, hb⟩ := hgen
    intro a
    rw [← hb, hsnd a, hsnd b, hcon a, hcon b]
  have : JacobsonSpace C0 := LocallyOfFiniteType.jacobsonSpace c0
  obtain ⟨a0, -, ha0⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨y, trivial⟩
    isClosed_univ.isLocallyClosed
  have hcl : IsClosed ({a0} : Set C0) := by simpa [closedPoints] using ha0
  exact dim_contra p hdim (pointOfClosedPoint c0 a0 hcl ≫ e)
    (by rw [Category.assoc, he, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp])
    (fun z => by rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hconst])

end LateralTheory.E.NonconstantLift
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNSysGlueOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodSystemGluing
open LateralTheory.E.LeafSHSysPf

theorem cocone_u_eq {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j')
    (c : Cocone D) (j j' : J) : u j ≫ c.ι.app j = u j' ≫ c.ι.app j' := by
  have h1 := c.w (IsFiltered.leftToMax j j')
  have h2 := c.w (IsFiltered.rightToMax j j')
  rw [← h1, ← h2, ← Category.assoc, ← Category.assoc, hu, hu]

theorem LeafNSysGlue_of (hR : LeafRingSys) : LeafNSysGlue := by
  intro _ B U x
  let 𝒰 := U.left.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let ι : Spec R ⟶ U.left := 𝒰.f (𝒰.idx x)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨J, _, _, D, u, hu, het, hq, c, ⟨hc⟩, hcof⟩ := hR R y
  have hE : ∀ j, Etale (Spec.map (u j) ≫ ι ≫ U.hom) := fun j => by
    have : Etale (Spec.map (u j)) := HasRingHomProperty.Spec_iff.2 (het j)
    have : Etale U.hom := U.prop
    infer_instance
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (Spec.map (u j) ≫ ι ≫ U.hom) (hE j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (u j) ≫ ι) (by show (Spec.map (u j) ≫ ι) ≫ U.hom = Spec.map (u j) ≫ ι ≫ U.hom; rw [Category.assoc]) trivial
  let tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j := fun {j j'} g =>
    MorphismProperty.Over.homMk (Spec.map (D.map g))
      (by show Spec.map (D.map g) ≫ Spec.map (u j) ≫ ι ≫ U.hom = Spec.map (u j') ≫ ι ≫ U.hom; rw [← Spec.map_comp_assoc, hu]) trivial
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  exact ⟨{
    J := J
    D := D
    V := V
    a := a
    e := fun j => Iso.refl _
    tr := tr
    tr_a := fun g => by
      apply MorphismProperty.Over.Hom.ext
      show Spec.map (D.map g) ≫ Spec.map _ ≫ ι = Spec.map _ ≫ ι
      rw [← Spec.map_comp_assoc, hu]
    tr_spec := fun g => by
      show 𝟙 _ ≫ Spec.map (D.map g) ≫ 𝟙 _ = _
      simp
    hx := fun j => by
      obtain ⟨q, hq⟩ := hq j
      refine ⟨q, ?_⟩
      rw [← hy]
      show ι (Spec.map (u j) q) = ι y
      congr 1
    c := c
    hc := hc
    cof := hcof
    t := Spec.map (c.ι.app j0) ≫ Spec.map (u j0) ≫ ι
    ht := fun j => by
      show _ = Spec.map (c.ι.app j) ≫ 𝟙 _ ≫ Spec.map (u j) ≫ ι
      rw [Category.id_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cocone_u_eq D u hu c j0 j] }⟩

end LateralTheory.E.NeighbourhoodSystemGluing
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjAffPf

theorem desc_spec (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] (A : Type) [CommRing A]
    [Algebra Ω A] [Algebra.FinitePresentation Ω A] :
    Desc k (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) := by
  let P := Algebra.Presentation.ofFinitePresentation Ω A
  let R : Subalgebra k Ω := Algebra.adjoin k P.coeffs
  have : P.HasCoeffs R := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let B := P.ModelOfHasCoeffs R
  let e : Ω ⊗[R] B ≃ₐ[Ω] A := P.tensorModelOfHasCoeffsEquiv R
  have hR : R.FG := ⟨P.finite_coeffs.toFinset, by simp [R]⟩
  let gB : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.toRingEquiv.toCommRingCatIso.hom
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Ω)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap Ω A)) gB := by
    refine (CommRingCat.isPushout_tensorProduct R Ω B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change e (x ⊗ₜ 1) = algebraMap Ω A x
      simpa [Algebra.TensorProduct.algebraMap_apply] using e.commutes x
    · simp [gB]
  refine ⟨R, hR, Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap R B)), _, ?_,
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem desc_of_iso (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (i : X ≅ Y) (g : Y ⟶ Sp Ω) (h : Desc k g) : Desc k (i.hom ≫ g) := by
  obtain ⟨R, hR, D, q, v, hq, hpb⟩ := h
  exact ⟨R, hR, D, q, i.hom ≫ v, hq,
    hpb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

theorem LeafObjAff_of : LeafObjAff := by
  intro k _ Ω _ _ X f hX hf
  obtain ⟨h1, h2, h3⟩ := hf
  let g : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of Ω) := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  letI : Algebra Ω Γ(X, ⊤) := φ.hom.toAlgebra
  have hg : LocallyOfFinitePresentation g := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤))) = g := Spec.map_preimage g
  have hfp : Algebra.FinitePresentation Ω Γ(X, ⊤) := by
    rw [← Spec.map_preimage g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hg
    exact hg
  have := desc_spec k (Ω := Ω) Γ(X, ⊤)
  rw [hφ] at this
  have hf' : f = X.isoSpec.hom ≫ g := by simp [g]
  rw [hf']
  exact desc_of_iso k X.isoSpec g this

end LateralTheory.E.LeafObjAffPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjGluePf

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

def DescAt (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D), FP q ∧ IsPullback v f q (toR R)

theorem toR_eq {R R' : Subalgebra k Ω} (h : R ≤ R') : toR R' ≫ incl h = toR R := by
  simp only [toR, incl]
  rw [← Spec.map_comp]
  rfl

theorem fp_snd {X Y Z : Scheme.{0}} (q : X ⟶ Z) (g : Y ⟶ Z) (hq : FP q) : FP (pullback.snd q g) := by
  obtain ⟨h1, h2, h3⟩ := hq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem descAt_mono {R R' : Subalgebra k Ω} (h : R ≤ R') {X : Scheme.{0}} {f : X ⟶ Sp Ω}
    (hd : DescAt R f) : DescAt R' f := by
  obtain ⟨D, q, v, hq, hp⟩ := hd
  refine ⟨pullback q (incl h), pullback.snd q (incl h),
    pullback.lift v (f ≫ toR R') (by rw [hp.w, Category.assoc, toR_eq]), fp_snd _ _ hq, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback q (incl h))
  rw [pullback.lift_fst, toR_eq]
  exact hp

def GlueData (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) (U V : X.Opens) : Prop :=
  ∃ (DU DV DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qV : DV ⟶ Sp R) (qW : DW ⟶ Sp R)
    (vU : U.toScheme ⟶ DU) (vV : V.toScheme ⟶ DV) (vW : (U ⊓ V).toScheme ⟶ DW) (φU : DW ⟶ DU) (φV : DW ⟶ DV),
    FP qU ∧ FP qV ∧ FP qW ∧ IsOpenImmersion φU ∧ IsOpenImmersion φV ∧ φU ≫ qU = qW ∧ φV ≫ qV = qW ∧
    IsPullback vU (U.ι ≫ f) qU (toR R) ∧ IsPullback vV (V.ι ≫ f) qV (toR R) ∧
    IsPullback vW ((U ⊓ V).ι ≫ f) qW (toR R) ∧
    vW ≫ φU = X.homOfLE inf_le_left ≫ vU ∧ vW ≫ φV = X.homOfLE inf_le_right ≫ vV

def LeafInclDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens) (R : Subalgebra k Ω), R.FG →
    DescAt R (U.ι ≫ f) → DescAt R (V.ι ≫ f) → DescAt R ((U ⊓ V).ι ≫ f) →
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ GlueData R' f U V

def LeafGlueTwo : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω) (U V : X.Opens) (R : Subalgebra k Ω), U ⊔ V = ⊤ → GlueData R f U V → DescAt R f

theorem LeafObjGlue_of (hI : LeafInclDescend) (hG : LeafGlueTwo) : LeafObjGlue := by
  intro k _ Ω _ _ X f hf U V hUV ⟨R1, h1, d1⟩ ⟨R2, h2, d2⟩ ⟨R3, h3, d3⟩
  obtain ⟨R', -, hR', g⟩ := hI k Ω f hf U V (R1 ⊔ R2 ⊔ R3) ((h1.sup h2).sup h3)
    (descAt_mono (le_sup_left.trans le_sup_left) d1) (descAt_mono (le_sup_right.trans le_sup_left) d2)
    (descAt_mono le_sup_right d3)
  exact ⟨R', hR', hG k Ω f U V R' hUV g⟩

end LateralTheory.E.LeafObjGluePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafQCQSInductPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafQCQSInductPf

def Cov (X : Scheme.{0}) (L : List X.Opens) : Prop :=
  (∀ u ∈ L, IsAffineOpen u) ∧ ∀ x : X, ∃ u ∈ L, x ∈ u

lemma sep_of {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] [X.IsSeparated] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

lemma fp_res {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (hf : FP f) (W : X.Opens)
    (hW : IsCompact (W : Set X)) : FP (W.ι ≫ f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, ?_, inferInstance⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  exact quasiCompact_of_compactSpace _

lemma cov_pull {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) :
    Cov W.toScheme (L.map (W.ι ⁻¹ᵁ ·)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact (hA u hu).preimage_of_isOpenImmersion W.ι (by simpa using hle u hu)
  · intro x
    obtain ⟨u, hu, hx⟩ := hc (W.ι x) (by
      have := Set.mem_range_self (f := W.ι) x
      rwa [Scheme.Opens.range_ι] at this)
    exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hx⟩

lemma exists_list {X : Scheme.{0}} (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ L : List X.Opens, (∀ u ∈ L, IsAffineOpen u) ∧ (∀ u ∈ L, u ≤ W) ∧ ∀ x ∈ W, ∃ u ∈ L, x ∈ u := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  refine ⟨hs.toFinset.toList.map (fun a : X.affineOpens => a.1), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.prop
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [e]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) a (by simpa using ha)
  · intro x hx
    rw [e] at hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, hxa⟩

lemma compact_of_cover {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) : IsCompact (W : Set X) := by
  have : (W : Set X) = ⋃ u ∈ L, (u : Set X) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx => let ⟨u, hu, h⟩ := hc x hx; ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => hle u hu h⟩
  rw [this]
  exact L.finite_toSet.isCompact_biUnion fun u hu => (hA u hu).isCompact

lemma mem_V {X : Scheme.{0}} (L : List X.Opens) (x : X) :
    x ∈ (⨆ u ∈ L, u : X.Opens) ↔ ∃ u ∈ L, x ∈ u := by
  simp

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma glue_step {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (U : X.Opens) (L' : List X.Opens)
    (hc : Cov X (U :: L'))
    (hV : Cov (⨆ u ∈ L', u : X.Opens).toScheme
        (L'.map ((⨆ u ∈ L', u : X.Opens).ι ⁻¹ᵁ ·)) → P ((⨆ u ∈ L', u : X.Opens).ι ≫ f))
    (hW : P ((U ⊓ ⨆ u ∈ L', u : X.Opens).ι ≫ f)) :
    P f := by
  have hU : IsAffineOpen U := hc.1 U (by simp)
  have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
  have hUV : U ⊔ (⨆ u ∈ L', u : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hx⟩ := hc.2 x
    rcases List.mem_cons.mp hu with rfl | hu
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((mem_V L' x).mpr ⟨u, hu, hx⟩))
  refine hG f hf U _ hUV ?_ ?_ ?_
  · haveI : IsAffine U := hU
    exact hA _ inferInstance (fp_res f hf U hU.isCompact)
  · refine hV (cov_pull _ L' hL' (fun u hu => ?_) (fun x hx => (mem_V L' x).mp hx))
    exact le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu
  · exact hW

end

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma empty_case {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (hc : Cov X []) : P f := by
  have : IsEmpty X := ⟨fun x => by obtain ⟨u, hu, _⟩ := hc.2 x; simp at hu⟩
  exact hA f inferInstance hf

lemma stepA : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    X.IsSeparated → Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf _ hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hs hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      have : (⨆ u ∈ L', u : X.Opens).toScheme.IsSeparated := sep_of (⨆ u ∈ L', u : X.Opens).ι
      refine ih _ _ (by simp [hl]) (fp_res f hf _ ?_) this hcV
      exact compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have hA' : ∀ v ∈ L'.map (U ⊓ ·), IsAffineOpen v := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact hU.inf (hL' u hu)
      have hle : ∀ v ∈ L'.map (U ⊓ ·), v ≤ W := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact inf_le_inf_left U (le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
      have hcW : ∀ x ∈ W, ∃ v ∈ L'.map (U ⊓ ·), x ∈ v := by
        intro x hx
        obtain ⟨hxU, hxV⟩ := hx
        obtain ⟨u, hu, h⟩ := (mem_V L' x).mp hxV
        exact ⟨U ⊓ u, List.mem_map.mpr ⟨u, hu, rfl⟩, ⟨hxU, h⟩⟩
      have : W.toScheme.IsSeparated := sep_of W.ι
      exact ih _ ((L'.map (U ⊓ ·)).map (W.ι ⁻¹ᵁ ·)) (by simp [hl])
        (fp_res f hf W (compact_of_cover W _ hA' hle hcW)) this (cov_pull W _ hA' hle hcW)

lemma stepB : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    have hVc : IsCompact ((⨆ u ∈ L', u : X.Opens) : Set X) :=
      compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      exact ih _ _ (by simp [hl]) (fp_res f hf _ hVc) hcV
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have : QuasiSeparated f := hf.2.2
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      have hWc : IsCompact (W : Set X) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU.isCompact (⨆ u ∈ L', u : X.Opens).2 hVc
      obtain ⟨L2, h1, h2, h3⟩ := exists_list W hWc
      haveI : IsAffine U := hU
      have : W.toScheme.IsSeparated := sep_of (X.homOfLE (inf_le_left : W ≤ U))
      exact stepA P hA hG _ (W.ι ≫ f) (L2.map (W.ι ⁻¹ᵁ ·)) rfl (fp_res f hf W hWc) this
        (cov_pull W L2 h1 h2 h3)

end

theorem LeafQCQSInduct_of : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := by
  intro S _ P hA hG X f hf
  have : QuasiCompact f := hf.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨L, h1, -, h3⟩ := exists_list (⊤ : X.Opens) (by simpa using isCompact_univ)
  exact stepB P hA hG _ f L rfl hf ⟨h1, fun x => h3 x trivial⟩

end LateralTheory.E.LeafQCQSInductPf
end
end

