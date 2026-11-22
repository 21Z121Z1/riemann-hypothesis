import Development.EtaleCohomology.EtaleSheaves.Bundle0083
import Development.EtaleCohomology.EtaleSheaves.Bundle0082
import Development.EtaleCohomology.EtaleSheaves.Bundle0073
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Mathlib

-- bundled from Development.EtaleCohomology.EtaleSheaves.Geo
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfB
open LateralTheory.E.LeafTw0LocGenPfA

theorem geo {q : ℕ} [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W h => ∃ a : (ZMod q)ˣ, h.appTop ξ.1 = (h.appTop ζ.1) ^ (a : ZMod q).val := by
  classical
  have key : ∀ x : V, ∃ (Wx : V.Opens) (_ : x ∈ Wx) (a : (ZMod q)ˣ),
      V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op ξ.1 =
        V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op (ζ.1 ^ (a : ZMod q).val) := by
    intro x
    have hq : IsUnit ((q : V.presheaf.stalk x)) := by
      simpa using ζ.2.1.map (V.presheaf.germ ⊤ x trivial).hom
    have hr : ∀ z : Γ(V, ⊤), Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
        Polynomial.aeval ((V.presheaf.germ ⊤ x trivial).hom z) (Polynomial.cyclotomic q ℤ) = 0 := by
      intro z hz
      have h := Polynomial.aeval_algHom_apply (V.presheaf.germ ⊤ x trivial).hom.toIntAlgHom z (Polynomial.cyclotomic q ℤ)
      rw [hz, map_zero] at h
      exact h
    obtain ⟨a, ha⟩ := local_pow hq (hr _ ζ.2.2) (hr _ ξ.2.2)
    have h2 : (V.presheaf.germ ⊤ x trivial).hom ξ.1 = (V.presheaf.germ ⊤ x trivial).hom (ζ.1 ^ (a : ZMod q).val) := by
      rw [map_pow]; exact ha
    obtain ⟨Wx, hx, i1, i2, he⟩ := TopCat.Presheaf.germ_eq V.presheaf (U := ⊤) (V := ⊤) x trivial trivial _ _ h2
    refine ⟨Wx, hx, a, ?_⟩
    have e1 : i1 = homOfLE le_top := Subsingleton.elim _ _
    have e2 : i2 = homOfLE le_top := Subsingleton.elim _ _
    subst e1 e2
    exact he
  choose Wx hx a ha using key
  have fin : ∀ (x : V) {W : Scheme.{0}} (g' : W ⟶ (Wx x).toScheme),
      (g' ≫ (Wx x).ι).appTop ξ.1 = ((g' ≫ (Wx x).ι).appTop ζ.1) ^ (a x : ZMod q).val := by
    intro x W g'
    have hle : (Wx x).ι ''ᵁ ⊤ ≤ Wx x := by simp
    have hW : ∀ z : Γ(V, ⊤), (Wx x).ι.appTop z =
        V.presheaf.map (homOfLE hle).op (V.presheaf.map (homOfLE le_top : Wx x ⟶ ⊤).op z) := by
      intro z
      rw [Scheme.Opens.ι_appTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hW, hW, ha x]
    simp only [map_pow]
    exact map_pow (ConcreteCategory.hom (Scheme.Hom.appTop g')) _ _
  let 𝒰 : V.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers V (fun x => (Wx x).toScheme) (fun x => (Wx x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨_, Scheme.Cover.mem_grothendieckTopology 𝒰, fun W h hh => ?_⟩
  obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨a x, fin x g⟩

end LateralTheory.E.LeafTw0LocGenPfB
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfNu
section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def nu : P.ResidueField ⊗[B] Ω[B⁄A] →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A] :=
  LinearMap.baseChange P.ResidueField ((KaehlerDifferential.map A A B (B ⧸ I)).restrictScalars B)

theorem nu_surjective : Function.Surjective (nu (A := A) I P) := by
  apply LinearMap.lTensor_surjective
  exact KaehlerDifferential.map_surjective_of_surjective A A B (B ⧸ I) Ideal.Quotient.mk_surjective

theorem nu_D (x : B) : nu (A := A) I P ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B x) =
    (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A (B ⧸ I) (Ideal.Quotient.mk I x) := by
  simp [nu]

def LeafResDimQ : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    e ≤ Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[(B ⧸ I)⁄A])

theorem LeafResSpanD_of (hQ : LeafResDimQ) : LeafResSpanD := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have : Nontrivial B := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (Ideal.eq_top_of_isUnit_mem P (zero_mem P)
    (by rw [h]; exact isUnit_one))⟩
  have := hB.isStandardSmooth
  have : Module.Free B Ω[B⁄A] := inferInstance
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B) (e + d)
  have hf : Module.finrank B Ω[B⁄A] = e + d := Module.finrank_eq_of_rank_eq hr
  have : Module.Finite B Ω[B⁄A] := inferInstance
  have hV : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄A]) = e + d := by
    rw [Module.finrank_baseChange, hf]
  have hrn := LinearMap.finrank_range_add_finrank_ker (nu (A := A) I P)
  rw [LinearMap.range_eq_top.mpr (nu_surjective (A := A) I P), finrank_top, hV] at hrn
  have hq := hQ d e A B I hB hBI P hIP
  have hS : Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) ≤ LinearMap.ker (nu (A := A) I P) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    simp [nu_D, Ideal.Quotient.eq_zero_iff_mem.mpr x.2]
  exact ⟨inferInstance, (Submodule.finrank_mono hS).trans (by omega)⟩

end LateralTheory.E.LeafCoordsPointResPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfQS
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology GlobalTheory.GlueModels LateralTheory.E.LeafGlueTwoPfFP

namespace LateralTheory.E.LeafGlueTwoPfQS

theorem qs_range {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] [QuasiSeparatedSpace A] :
    IsQuasiSeparated (Set.range e) := by
  simpa [Set.image_univ] using (isQuasiSeparated_univ (α := A)).image_of_isEmbedding e.isOpenEmbedding.isEmbedding

theorem compact_pre {A D : Scheme.{0}} (e : A ⟶ D) [IsOpenImmersion e] {s : Set D} (hs : IsCompact s)
    (h : s ⊆ Set.range e) : IsCompact (e ⁻¹' s) :=
  (e.isOpenEmbedding.isInducing.isCompact_preimage_iff h).2 hs

theorem compact_inter_range {W A D : Scheme.{0}} (φ : W ⟶ A) (e : A ⟶ D) [IsOpenImmersion e] [QuasiCompact φ]
    {s : Set D} (hs : IsCompact s) (ho : IsOpen s) (h : s ⊆ Set.range e) :
    IsCompact (s ∩ Set.range (φ ≫ e)) := by
  rw [← Set.image_preimage_eq_inter_range]
  refine IsCompact.image ?_ (φ ≫ e).continuous
  have hp : ((φ ≫ e) ⁻¹' s) = φ ⁻¹' (e ⁻¹' s) := by ext x; simp
  rw [hp]
  exact QuasiCompact.isCompact_preimage (f := φ) _ (e.continuous.isOpen_preimage _ ho) (compact_pre e hs h)

set_option backward.isDefEq.respectTransparency false in
theorem leafPushoutQS : LeafPushoutQS := by
  intro DW DU DV φU φV _ _ hW hWs hUs hVs
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  have : QuasiCompact φU := quasiCompact_of_compactSpace φU
  have : QuasiCompact φV := quasiCompact_of_compactSpace φV
  let good : Set (pushout φU φV : Scheme.{0}) → Prop := fun s => IsOpen s ∧ IsCompact s ∧
    (s ⊆ Set.range (pushout.inl φU φV) ∨ s ⊆ Set.range (pushout.inr φU φV))
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun s : {s // good s} => s.1) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩; exact s.2.1
    · intro x u hx hu
      rcases pushout_cover φU φV x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DU} {x : DU}, x ∈ U → ∃ U' ∈ DU.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DU.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inl φU φV ⁻¹' u, (pushout.inl φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inl φU φV '' U', ⟨⟨_, (pushout.inl φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inl φU φV).continuous, Or.inl (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
      · have hb : ∀ {U : TopologicalSpace.Opens DV} {x : DV}, x ∈ U → ∃ U' ∈ DV.affineOpens, x ∈ U' ∧ U' ≤ U :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp DV.isBasis_affineOpens
        obtain ⟨U', hU', hyU', hle⟩ := hb (U := ⟨pushout.inr φU φV ⁻¹' u, (pushout.inr φU φV).continuous.isOpen_preimage u hu⟩) (x := y) hx
        refine ⟨pushout.inr φU φV '' U', ⟨⟨_, (pushout.inr φU φV).isOpenEmbedding.isOpenMap _ U'.2,
          (show IsAffineOpen U' from hU').isCompact.image (pushout.inr φU φV).continuous, Or.inr (Set.image_subset_range _ _)⟩,
          rfl⟩, ⟨y, hyU', rfl⟩, Set.image_subset_iff.2 hle⟩
  · have e : Set.range (φU ≫ pushout.inl φU φV) = Set.range (φV ≫ pushout.inr φU φV) := by
      rw [pushout.condition]
    have hWo : IsOpen (Set.range (φU ≫ pushout.inl φU φV)) := (φU ≫ pushout.inl φU φV).isOpenEmbedding.isOpen_range
    have mixed : ∀ s t : Set (pushout φU φV : Scheme.{0}), IsOpen s → IsCompact s →
        s ⊆ Set.range (pushout.inl φU φV) → IsOpen t → IsCompact t → t ⊆ Set.range (pushout.inr φU φV) →
        IsCompact (s ∩ t) := by
      intro s t so sc hs tO tc ht
      have hsub : s ∩ t ⊆ Set.range (φU ≫ pushout.inl φU φV) := by
        rintro x ⟨h1, h2⟩
        obtain ⟨a, rfl⟩ := hs h1
        obtain ⟨b, hb⟩ := ht h2
        obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr φU φV hb.symm
        exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]⟩
      have hst : s ∩ t = (s ∩ Set.range (φU ≫ pushout.inl φU φV)) ∩ (t ∩ Set.range (φU ≫ pushout.inl φU φV)) := by
        ext x; constructor
        · intro hx; exact ⟨⟨hx.1, hsub hx⟩, ⟨hx.2, hsub hx⟩⟩
        · intro hx; exact ⟨hx.1.1, hx.2.1⟩
      rw [hst]
      refine qs_range (φU ≫ pushout.inl φU φV) _ _ Set.inter_subset_right (so.inter hWo)
        (compact_inter_range φU _ sc so hs) Set.inter_subset_right (tO.inter hWo) ?_
      rw [e]; exact compact_inter_range φV _ tc tO ht
    rintro ⟨s, so, sc, hs⟩ ⟨t, tO, tc, ht⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact qs_range (pushout.inl φU φV) s t hs so sc ht tO tc
    · exact mixed s t so sc hs tO tc ht
    · show IsCompact (s ∩ t); rw [Set.inter_comm]; exact mixed t s tO tc ht so sc hs
    · exact qs_range (pushout.inr φU φV) s t hs so sc ht tO tc

theorem LeafGlueTwo_of : LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' leafPushoutQS

end LateralTheory.E.LeafGlueTwoPfQS
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafMapFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf

namespace LateralTheory.E.LeafMapFPPf

section
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

@[reassoc]
theorem incl_comp {R S T : Subalgebra k Ω} (h1 : R ≤ S) (h2 : S ≤ T) :
    incl h2 ≫ incl h1 = incl (h1.trans h2) := by
  simp only [incl, ← Spec.map_comp]
  congr 1

theorem incl_refl (R : Subalgebra k Ω) : incl (le_refl R) = 𝟙 _ := by
  simp only [incl]
  rw [← Spec.map_id]
  congr 1

theorem sq {R S : Subalgebra k Ω} (h : R ≤ S) {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D}
    (hs : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w])) c
      (pullback.snd q (incl h)) (toR S) :=
  IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h)
    (by rw [pullback.lift_fst, toR_incl]; exact hs) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

def dgMap {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : pullback q1 (incl hT) ⟶ pullback q1 (incl hS) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl h) (by
    rw [pullback.condition, Category.assoc, incl_comp])

@[reassoc (attr := simp)]
theorem dgMap_fst {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem dgMap_snd {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S)
    (hT : R ≤ T) (h : S ≤ T) : dgMap q1 hS hT h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ incl h :=
  pullback.lift_snd _ _ _

def dg {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : (GlobalTheory.FGAbove R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q1 (incl S.unop.2.2)
  map {S T} f := dgMap q1 _ _ (show T.unop.1 ≤ S.unop.1 from leOfHom f.unop)
  map_id S := by apply pullback.hom_ext <;> simp [incl_refl]
  map_comp f g := by apply pullback.hom_ext <;> simp [incl_comp]

def dgT {R : Subalgebra k Ω} {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R) : dg q1 ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.fst _ _ ≫ q1
  naturality S T f := by simp [dg]

theorem dgπ_map {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    pullback.lift v1 (c1 ≫ toR T) (by rw [Category.assoc, toR_incl, hs.w]) ≫ dgMap q1 hS hT h =
      (pullback.lift v1 (c1 ≫ toR S) (by rw [Category.assoc, toR_incl, hs.w]) : C1 ⟶ pullback q1 (incl hS)) := by
  apply pullback.hom_ext
  · erw [Category.assoc, dgMap_fst, pullback.lift_fst, pullback.lift_fst]
  · erw [Category.assoc, dgMap_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_incl]

def dgCone {R : Subalgebra k Ω} {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1)
    (hs : IsPullback v1 c1 q1 (toR R)) : Cone (dg q1) where
  pt := C1
  π := { app S := pullback.lift v1 (c1 ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs.w])
         naturality S T f := by
           exact (Category.id_comp _).trans (dgπ_map c1 q1 v1 hs _ _ _).symm }

end

def LeafLimFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C1 D1 : Scheme.{0}} (c1 : C1 ⟶ Sp Ω) (q1 : D1 ⟶ Sp R) (v1 : C1 ⟶ D1) (hs : IsPullback v1 c1 q1 (toR R)),
    FP q1 → Nonempty (IsLimit (dgCone c1 q1 v1 hs))

def LeafStagesFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    {D1 : Scheme.{0}} (q1 : D1 ⟶ Sp R), FP q1 →
    (∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) ∧ QuasiSeparatedSpace ((dg q1).obj S)) ∧
    ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), IsAffineHom (dgMap q1 S.2.2 T.2.2 h)

theorem morphismDescent_of_isLimit (hL : LeafLimFP) (hI : LeafStagesFP) : LeafMapFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 D0 D1 q q1 v0 v1 hq hq1 hs0 hs1
  haveI := GlobalTheory.FGAbove.isFiltered hR
  obtain ⟨hc⟩ := hL k Ω R hR (γ1 ≫ c0) q1 v1 hs1 hq1
  obtain ⟨hcs, haf⟩ := hI k Ω R q1 hq1
  haveI := hq.1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, CompactSpace ((dg q1).obj S) := fun S => (hcs S).1
  haveI : ∀ S : (GlobalTheory.FGAbove R)ᵒᵖ, QuasiSeparatedSpace ((dg q1).obj S) := fun S => (hcs S).2
  haveI : ∀ {S T : (GlobalTheory.FGAbove R)ᵒᵖ} (f : S ⟶ T), IsAffineHom ((dg q1).map f) := fun f => haf _ _ _
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D := dg q1)
    (t := dgT q1) (f := q) (c := dgCone (γ1 ≫ c0) q1 v1 hs1) hc (γ1 ≫ v0) (by
      ext S
      simp only [dgCone, dgT, NatTrans.comp_app, Functor.const_map_app]
      erw [pullback.lift_fst_assoc]
      rw [hs1.w]; simp only [Category.assoc, hs0.w])
  let P := pullback q1 (incl S.unop.2.2)
  let g' : P ⟶ D0 := g
  let w1 : C1 ⟶ P := pullback.lift v1 ((γ1 ≫ c0) ≫ toR S.unop.1) (by rw [Category.assoc, toR_incl, hs1.w])
  have hg1' : w1 ≫ g' = γ1 ≫ v0 := hg1
  have hg2' : g' ≫ q = pullback.snd q1 (incl S.unop.2.2) ≫ incl S.unop.2.2 := by
    rw [show g' ≫ q = pullback.fst q1 (incl S.unop.2.2) ≫ q1 from hg2]; exact pullback.condition
  refine ⟨S.unop.1, S.unop.2.1, pullback q (incl S.unop.2.2), P, pullback.snd _ _,
    pullback.lift g' (pullback.snd _ _) hg2', pullback.lift v0 (c0 ≫ toR S.unop.1)
      (by rw [Category.assoc, toR_incl, hs0.w]), w1, fp_snd _ _ hq, ?_, sq S.unop.2.2 hs0, ?_, ?_⟩
  · rw [pullback.lift_snd]; exact fp_snd _ _ hq1
  · rw [pullback.lift_snd]; exact sq S.unop.2.2 hs1
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact hg1'.symm
    · simp only [Category.assoc, pullback.lift_snd, w1]

end LateralTheory.E.LeafMapFPPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFGraphOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

theorem toR_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]; rfl

theorem incl_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

abbrev cmp {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    pullback c p ⟶ pullback b p :=
  pullback.lift (pullback.fst c p ≫ a) (pullback.snd _ _)
    (by rw [Category.assoc, h]; exact pullback.condition)

theorem paste {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    IsPullback (cmp p a b c h) (pullback.fst c p) (pullback.fst b p) a := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback b p).flip
  rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (a ≫ b) p).flip

theorem LeafSpreadLQFGraph_of (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := by
  intro k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf
  have hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) := by
    infer_instance
  obtain ⟨S, hRS, hSfg, hS⟩ := hM k Ω R hRfg
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0
    (cmp p (toR R) _ _ (toR_sk R))
    ⟨hLFT, inferInstance, inferInstance⟩ (by rw [pullback.lift_fst]; exact hq) (paste p _ _ _ (toR_sk R))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hpb) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hpb.w.symm
      · simp only [Category.assoc, pullback.lift_snd]; exact hve.symm) hlqf
  refine ⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩
  refine hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p)
    (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hr.w.symm
  · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmooth1Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.SpreadingOutSmoothness

theorem stepB {R K B A : Type} [CommRing R] [CommRing K] [CommRing B] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Algebra A B] [IsScalarTower R A B] (M : Submonoid R)
    [IsLocalization M K] [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Algebra.Smooth K B]
    (Q : Ideal B) [Q.IsPrime] : Algebra.IsSmoothAt R (Q.comap (algebraMap A B)) := by
  haveI : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth K (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := Algebra.FormallySmooth.comp R K _
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime Q) Q
  exact Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv (Q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem algDescend (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A] (hfp : Algebra.FinitePresentation R A) (hs : Algebra.Smooth Ω (Ω ⊗[R] A))
    (P : PrimeSpectrum (Ω ⊗[R] A)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  let e := Algebra.TensorProduct.cancelBaseChange R (FractionRing R) Ω Ω A
  haveI : Algebra.Smooth Ω (Ω ⊗[FractionRing R] (FractionRing R ⊗[R] A)) := Algebra.Smooth.of_equiv e.symm
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ Ω
  haveI : Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω
  letI : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (FractionRing R ⊗[R] A) :=
    IsLocalization.tensorRight _ _
  let φ : FractionRing R ⊗[R] A →+* Ω ⊗[R] A := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : FractionRing R ⊗[R] A →ₐ[FractionRing R] Ω ⊗[FractionRing R] _).toRingHom
  haveI : (P.asIdeal.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hφ : φ.comp (algebraMap A (FractionRing R ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom := by
    ext a
    show e (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P =
      ⟨(P.asIdeal.comap φ).comap (algebraMap A (FractionRing R ⊗[R] A)), inferInstance⟩ := by
    ext1; simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hφ]
  rw [hc]
  exact stepB (K := FractionRing R) (nonZeroDivisors R) (P.asIdeal.comap φ)

def LeafAlgDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A], Algebra.FinitePresentation R A → Algebra.Smooth Ω (Ω ⊗[R] A) →
    ∀ P : PrimeSpectrum (Ω ⊗[R] A),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A

def LeafStalkOfAlg : Prop := LeafAlgDescend → LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafStalkDescend

theorem leafAlgDescend : LeafAlgDescend := fun k _ Ω _ _ R A _ _ hfp hs P => algDescend k Ω R A hfp hs P

theorem LeafSpreadSmooth1_of (hB : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim) (hT : LeafStalkOfAlg) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 :=
  LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadSmooth_of
    (LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafSpreadSmoothAffSm_of (hT leafAlgDescend)) hB

end LateralTheory.E.SpreadingOutSmoothness

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0TwFreeOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0TwFreePf

def aug (q : ℕ) (A : CommRingCat.{0}) : (twF q 0).obj A →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Submodule.liftQ (twRel q 0 A) (Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q)))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, _, rfl⟩
    simp [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single]
    exact sub_self (1 : ULift.{1} (ZMod q)))

theorem aug_mk (q : ℕ) (A : CommRingCat.{0}) (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  show Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q))) (Finsupp.single ζ 1) = 1
  rw [Finsupp.linearCombination_single, one_smul]

theorem aug_map (q : ℕ) (A B : CommRingCat.{0}) (g : A ⟶ B) (ζ : Prim q A) :
    aug q B (((twF q 0).map g).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))) = 1 := by
  show aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.single ζ 1))) = 1
  rw [Finsupp.mapDomain_single]
  exact aug_mk q B _

theorem LeafTw0TwFree_of : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := by
  intro q _ V ζ
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q 0
  let x : P.obj (op V) := (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 0).obj Γ(V, ⊤))
  let φ := ((toSheafify Scheme.etaleTopology P).app (op V)).hom
  by_cases hS : ∃ (c : ULift.{1} (ZMod q)), c • twGen 0 ζ = 0 ∧ c ≠ 0
  · obtain ⟨c, hc, hc0⟩ := hS
    have heq : φ (c • x) = φ 0 := by
      rw [φ.map_smul, φ.map_zero]; exact hc
    have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 heq
    by_cases hne : ∃ (U : Scheme.{0}) (f : U ⟶ V), (Presheaf.equalizerSieve (F := P) (X := op V) (c • x) 0).arrows f
    · exfalso
      obtain ⟨U, f, hf⟩ := hne
      apply hc0
      have h1 : (P.map f.op).hom (c • x) = (P.map f.op).hom 0 := hf
      rw [(P.map f.op).hom.map_smul, (P.map f.op).hom.map_zero] at h1
      let y : (twF q 0).obj Γ(U, ⊤) := ((twF q 0).map (Scheme.Γ.map f.op)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))
      have h3 : aug q Γ(U, ⊤) y = 1 := aug_map q _ _ _ ζ
      have h4 : aug q Γ(U, ⊤) (c • y) = c • aug q Γ(U, ⊤) y := (aug q _).map_smul c y
      have h5 : c • y = 0 := h1
      rw [h5, h3, map_zero, smul_eq_mul, mul_one] at h4
      exact h4.symm
    · left
      push Not at hne
      exact (tw q 0).isSeparated V _ hmem _ _ (fun U f hf => absurd hf (hne U f))
  · right
    intro c hc
    by_contra h0
    exact hS ⟨c, hc, h0⟩

end LateralTheory.E.LeafTw0TwFreePf
end
end

