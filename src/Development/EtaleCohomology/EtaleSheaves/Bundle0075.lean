import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.Bundle0052
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0064
import Development.EtaleCohomology.EtaleSheaves.Bundle0070
import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal
import Development.EtaleCohomology.EtaleSheaves.Bundle0074
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.TwPairExists
import Development.EtaleCohomology.EtaleSheaves.Bundle0024
import Development.EtaleCohomology.EtaleSheaves.Bundle0020
import Development.EtaleCohomology.EtaleSheaves.Bundle0025
import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
import Development.EtaleCohomology.EtaleSheaves.UnitSections
import Development.EtaleCohomology.EtaleSheaves.Bundle0037
import Development.EtaleCohomology.EtaleSheaves.Bundle0032
import Development.EtaleCohomology.EtaleSheaves.Bundle0055
import Development.EtaleCohomology.EtaleSheaves.Bundle0057
import Development.EtaleCohomology.EtaleSheaves.Bundle0054
import Development.EtaleCohomology.EtaleSheaves.Bundle0063
import Development.EtaleCohomology.EtaleSheaves.Bundle0049
import Development.EtaleCohomology.TateTwists.Bundle0032
import Development.EtaleCohomology.TateTwists.Bundle0033
import Development.EtaleCohomology.EtaleSheaves.Bundle0071
import Development.EtaleCohomology.EtaleSheaves.Bundle0072
import Development.EtaleCohomology.EtaleSheaves.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
import Development.EtaleCohomology.EtaleSheaves.Bundle0073

-- bundled from Development.EtaleCohomology.EtaleSheaves.ArchimedeanCokernel
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut
theorem LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of (hD : LateralTheory.E.TruncationKernel.RelDesc) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩
  have hinj := hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
  refine LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)
  refine (LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_
  rw [← hx]
  exact LateralTheory.E.KernelLocalization.bd_pull ..
theorem LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm
  have h := LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  exact ⟨h.2, h.1 (m - 1) (by omega)⟩
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BoundaryKernel
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartBCNnmPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData LateralTheory.E.ProjectiveLineCharts₂

namespace LateralTheory.E.ChartBC_nnmPf

theorem res_bijective {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  have : (homOfLE h) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

theorem pushout_gen {Z X Y P : CommRingCat.{0}} {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (R : Subring P) (hi : ∀ x, i x ∈ R) (hj : ∀ y, j y ∈ R) (p : P) : p ∈ R := by
  let i' : X ⟶ CommRingCat.of R := CommRingCat.ofHom (i.hom.codRestrict R hi)
  let j' : Y ⟶ CommRingCat.of R := CommRingCat.ofHom (j.hom.codRestrict R hj)
  have w' : f ≫ i' = g ≫ j' := by
    ext z
    have := congrArg (fun φ => φ.hom z) h.w
    simpa [i', j'] using this
  let σ := h.desc i' j' w'
  have hσ : σ ≫ CommRingCat.ofHom R.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc]; ext; rfl
    · rw [h.inr_desc_assoc]; ext; rfl
  have := congrArg (fun φ => φ.hom p) hσ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  rw [← this]; exact (σ.hom p).2

theorem restrict_appTop_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ (f ∣_ U).appTop =
      f.app U ≫ X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).le).op := by
  rw [morphismRestrict_appTop]
  have e := f.naturality (homOfLE (Scheme.Opens.ι_image_top U).le).op
  calc _ = (Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ f.app (U.ι ''ᵁ ⊤)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc, ← Functor.map_comp]; rfl

theorem snd_eq {A : Type} [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (V : L.Opens) :
    (V.ι ≫ l).appTop = l.appLE ⊤ V le_top ≫ L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top V).le).op := by
  unfold Scheme.Hom.appLE
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem ChartBC_of : ChartBC := by
  intro A _ L l f hf W x hW hsx
  have hpb := IsPullback.paste_vert (isPullback_morphismRestrict f W) hf
  have : IsAffine W.toScheme := hW
  have hA : IsAffineOpen (f ⁻¹ᵁ W) := IsAffine.of_isPullback hpb
  refine ⟨hA, ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hA
  have hpo := isPushout_appTop_of_isPullback hpb
  let ψ := L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le).op
  have hψ := res_bijective (X := L) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).ge
  let R : Subring Γ((f ⁻¹ᵁ W).toScheme, ⊤) :=
    (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x)).range.map ψ.hom
  intro t
  have ht : ψ t ∈ R := pushout_gen hpo R ?_ ?_ (ψ t)
  · obtain ⟨r, ⟨q, rfl⟩, hr⟩ := Subring.mem_map.mp ht
    exact ⟨q, hψ.1 hr⟩
  · intro w
    obtain ⟨w0, rfl⟩ := (res_bijective (X := P1) (Scheme.Opens.ι_image_top W).le
      (Scheme.Opens.ι_image_top W).ge).2 w
    have h1 : (f ∣_ W).appTop (P1.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op w0) =
        ψ (f.app W w0) := congrArg (fun φ => φ.hom w0) (restrict_appTop_eq f W)
    erw [h1]
    obtain ⟨q, rfl⟩ := hsx w0
    refine Subring.mem_map.mpr ⟨_, ⟨q.map (Int.castRingHom A), rfl⟩, ?_⟩
    congr 1
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    congr 1; exact RingHom.ext_int _ _
  · intro a
    refine Subring.mem_map.mpr ⟨_, ⟨Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a), rfl⟩, ?_⟩
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, snd_eq]
    simp only [rA, RingHom.comp_apply]
    erw [Iso.hom_inv_id_apply]
    rfl

end LateralTheory.E.ChartBC_nnmPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle
section
namespace LateralTheory.E.LeafA6nat_xy7V2Cut

theorem kumTExists : LateralTheory.E.CupProductRingLaws.LeafKumTExists := fun q _ =>
  ⟨_, LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange q⟩

theorem oneSpec : LateralTheory.E.CupProductRingLaws.LeafOneSpec :=
  LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of
    (LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit LateralTheory.E.UnitSections.LeafUnitSec_of)
    LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of

theorem etaleFirstChernClass_represented_by_chern_cocycle : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle :=
  have hr := LateralTheory.E.LeafRootLocPf.LeafRootLoc_of
  LateralTheory.E.ChernClassRootLocalization.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique
    (LateralTheory.E.ChernClassEvaluation.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness LateralTheory.E.LeafEvMkPf.LeafEvMk_of
      (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor hr kumTExists) (LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor.etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor hr kumTExists)
      (LateralTheory.E.ChernCocycleEdgeCoboundary.etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots hr) (LateralTheory.E.ChernCocycleFaceFormulas.etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r hr) (LateralTheory.E.ChernCocycleFaceDegeneracyIdentities.etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization hr))
    hr

theorem natKum : LateralTheory.E.CupProductRingLaws.LeafNatKum := fun q _ =>
  ((LateralTheory.Fix.EtaleKummerClassExplicitCocycle.holds_of LateralTheory.Fin.EtaleKummerTriangleExists.intersectionNumber_baseChange) q).2.1

theorem goal_of : LateralTheory.E.D2.LeafA6nat := fun q _ =>
  ⟨LateralTheory.E.LeafNatCupPf.LeafNatCup_of LateralTheory.Fix.CupProductTensor.cupSpec q,
   LateralTheory.E.LeafNatOnePf.LeafNatOne_of oneSpec q,
   LateralTheory.E.FirstChernNaturality.etale_first_chern_class_natural_of_spec etaleFirstChernClass_represented_by_chern_cocycle q,
   natKum q⟩

end LateralTheory.E.LeafA6nat_xy7V2Cut
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueRelPfCone
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace LateralTheory.E.GlueRelPfCone

theorem pre_pull_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (b : HK R L F m) :
    HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) (HK.pull R φ F m b) = 0 := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩
  ext1
  simp only [zcomp, Cocycle.ofHom_coe]
  rw [δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]
  simp [Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem range_of_pre_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (x : HK R K F m)
    (hx : HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) x = 0) : x ∈ Set.range (HK.pull R φ F m) := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m', hm', γ, hγ⟩ := hx
  obtain rfl : m' = m := by omega
  have hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m') := by
    rw [hγ]; rfl
  have hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0 := by
    rw [δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp
  let b : Cocycle L (res R F) m' := Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')))
    (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)
  refine ⟨CohomologyClass.mk b, ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩
  ext1
  rw [δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ',
    mappingCone.δ_inl]
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]
  simp [zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]

theorem coneExact : LateralTheory.E.GlueRelPf.ConeExact := by
  intro R _ K L φ F m x
  exact ⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩

theorem GlueRel_of (hE : LateralTheory.E.GlueRelPf.EdgeInj) : LateralTheory.E.LocGlueEtPf.GlueRel :=
  LateralTheory.E.GlueRelPf.GlueRel_of coneExact hE

end LateralTheory.E.GlueRelPfCone
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.H0Lifting
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.H0Lifting
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem exists_epi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (M : DerivedCategory A) :
    ∃ (Z : A) (φ : (DerivedCategory.singleFunctor A 0).obj Z ⟶ M),
      Epi ((DerivedCategory.homologyFunctor A 0).map φ) := by
  let K := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  let φ0 : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (K.cycles 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (K.iCycles 0) (fun k _ => K.iCycles_d 0 k)
  have h1 : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (K.cycles 0)).inv ≫
      HomologicalComplex.cyclesMap φ0 0 = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles 0)]
    simp [φ0]
  have h2 : Epi (HomologicalComplex.cyclesMap φ0 0) := epi_of_epi_fac h1
  have h3 : Epi (HomologicalComplex.homologyMap φ0 0) :=
    epi_of_epi_fac (HomologicalComplex.homologyπ_naturality φ0 0)
  have h4 : Epi ((DerivedCategory.homologyFunctor A 0).map (DerivedCategory.Q.map φ0)) := by
    have h := (DerivedCategory.homologyFunctorFactors A 0).inv.naturality φ0
    have h5 : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) 0).map φ0) := h3
    exact epi_of_epi_fac h.symm
  refine ⟨K.cycles 0, ((DerivedCategory.singleFunctorIsoCompQ A 0).app _).hom ≫ DerivedCategory.Q.map φ0 ≫ e.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ h4 _ inferInstance)

theorem transport {A D : Type*} [Category A] [Category D] (S : A ⥤ D) (H : D ⥤ A) (η : S ⋙ H ≅ 𝟭 A)
    {X Y Z : A} {M : D} (a : X ⟶ Y) (s : X ⟶ Z) (t : H.obj (S.obj Y) ⟶ H.obj M) (φ : S.obj Z ⟶ M)
    (h : a ≫ η.inv.app Y ≫ t = s ≫ η.inv.app Z ≫ H.map φ) : H.map (S.map a) ≫ t = H.map (S.map s ≫ φ) := by
  have h1 : a ≫ η.inv.app Y = η.inv.app X ≫ H.map (S.map a) := η.inv.naturality a
  have h2 : s ≫ η.inv.app Z = η.inv.app X ≫ H.map (S.map s) := η.inv.naturality s
  have h3 : η.inv.app X ≫ H.map (S.map a) ≫ t = η.inv.app X ≫ H.map (S.map s) ≫ H.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t) h1).symm.trans ((Category.assoc _ _ _).trans
      (h.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ H.map φ) h2).trans (Category.assoc _ _ _))))))
  rw [Functor.map_comp]
  exact (cancel_epi _).1 h3

abbrev PF (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

def gen {B : Scheme.{0}} (q : ℕ) {U V : B.Etale} (a : V ⟶ U) : ((PF B q).obj U).obj (op V) :=
  ModuleCat.freeMk (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem gen_res {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).obj U).map b.op (gen q a) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem gen_map {B : Scheme.{0}} (q : ℕ) {U V W : B.Etale} (a : V ⟶ U) (b : W ⟶ V) :
    ((PF B q).map a).app (op W) (gen q b) = gen q (b ≫ a) :=
  ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) _ _

theorem pf_ext {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (f g : (PF B q).obj U ⟶ F) (h : f.app (op U) (gen q (𝟙 U)) = g.app (op U) (gen q (𝟙 U))) : f = g := by
  ext ⟨V⟩ : 2
  refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
  rintro ⟨a⟩
  change f.app (op V) (gen q a) = g.app (op V) (gen q a)
  have e : gen q a = ((PF B q).obj U).map a.op (gen q (𝟙 U)) := by rw [gen_res, Category.comp_id]
  rw [e, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

theorem pf_exists {B : Scheme.{0}} {q : ℕ} {U : B.Etale} {F : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))}
    (s : F.obj (op U)) : ∃ f : (PF B q).obj U ⟶ F, f.app (op U) (gen q (𝟙 U)) = s := by
  let c : ∀ V : B.Etaleᵒᵖ, ((PF B q).obj U).obj V ⟶ F.obj V := fun V =>
    ModuleCat.freeDesc (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V.unop ⟶ U))
      (TypeCat.ofHom (fun a => F.map a.down.op s))
  have hc : ∀ (V : B.Etale) (a : V ⟶ U), c (op V) (gen q a) = F.map a.op s := fun V a =>
    ModuleCat.freeDesc_apply (R := ULift.{1} (ZMod q)) _ _
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
    refine ModuleCat.free_hom_ext (R := ULift.{1} (ZMod q)) (X := ULift.{1} (V ⟶ U)) ?_
    rintro ⟨a⟩
    change c (op W) (((PF B q).obj U).map (Quiver.Hom.op b) (gen q a)) = F.map (Quiver.Hom.op b) (c (op V) (gen q a))
    rw [gen_res, hc, hc, op_comp, Functor.map_comp]
    rfl
  · change c (op U) _ = _
    rw [hc]
    simp

theorem loc_lift {B : Scheme.{0}} {q : ℕ} {F G : SShv B q} (π : F ⟶ G) [Epi π] (U : B.Etale)
    (t : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U) ⟶ G) :
    Cov U (fun U' a => ∃ s : (presheafToSheaf (EtTop B) _).obj ((PF B q).obj U') ⟶ F,
      (presheafToSheaf (EtTop B) _).map ((PF B q).map a) ≫ t = s ≫ π) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  have hπ : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  let adj := sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))
  let t' : (PF B q).obj U ⟶ G.obj := adj.homEquiv _ _ t
  refine ⟨_, Presheaf.imageSieve_mem (EtTop B) π.hom (t'.app (op U) (gen q (𝟙 U))), ?_⟩
  rintro U' a ⟨z, hz⟩
  obtain ⟨f, hf⟩ := pf_exists (F := F.obj) z
  refine ⟨(adj.homEquiv _ F).symm f, ?_⟩
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply pf_ext
  change t'.app (op U') (((PF B q).map a).app (op U') (gen q (𝟙 U'))) = π.hom.app (op U') (f.app (op U') (gen q (𝟙 U')))
  rw [hf, hz, gen_map, ← NatTrans.naturality_apply, gen_res, Category.id_comp, Category.comp_id]

theorem etale_sheaf_epi_lifts_degree_zero_derived_maps_locally : EtaleDerivedDegreeZeroHomologyLocallyLifts := by
  intro B q M U t
  obtain ⟨Z, φ, hφ⟩ := exists_epi M
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0
  let X : B.Etale ⥤ SShv B q := PF B q ⋙ presheafToSheaf (EtTop B) _
  let π : Z ⟶ (H0 B q).obj M := η.inv.app Z ≫ (H0 B q).map φ
  have hπ : Epi π := epi_comp _ _
  let t0 : X.obj U ⟶ (H0 B q).obj M := η.inv.app (X.obj U) ≫ t
  refine (loc_lift π U t0).mono ?_
  rintro U' a ⟨s, hs⟩
  refine ⟨(DerivedCategory.singleFunctor _ 0).map s ≫ φ, ?_⟩
  exact transport _ _ η (X.map a) s t φ hs

end LateralTheory.E.H0Lifting
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KerLocOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedSH0Of
section
namespace LateralTheory.E.LeafClosedSH0PfCut
open LateralTheory.E.LeafClosedSH0Pf

theorem LeafClosedSH0_of (hS : LeafSHSieve) : LateralTheory.E.LeafVanBPf.LeafClosedSH0 :=
  LateralTheory.E.LeafClosedSH0Pf.LeafClosedSH0_of hS LateralTheory.E.LeafClosedSH0PfQuot.shQuot
    LateralTheory.E.LeafClosedSH0PfEmpty.emptySec LateralTheory.E.LeafClosedSH0PfPrim.primLift

end LateralTheory.E.LeafClosedSH0PfCut
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPf
section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointPf

open LateralTheory.E.LeafCoordsPf
open scoped Pointwise TensorProduct

theorem exists_smul_mem_of_span {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (P : Ideal B) [P.IsPrime] (g : ι → M)
    (hg : Submodule.span P.ResidueField (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] g i) = ⊤) (m : M) :
    ∃ s ∉ P, s • m ∈ Submodule.span B (Set.range g) := by
  set N := Submodule.span B (Set.range g)
  let f := LinearMap.baseChange P.ResidueField N.mkQ
  have hf : Function.Surjective f := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)
  have hr : LinearMap.range f = ⊥ := by
    rw [LinearMap.range_eq_map, ← hg, Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have : g i ∈ N := Submodule.subset_span (Set.mem_range_self i)
    simp [f, (Submodule.Quotient.mk_eq_zero N).mpr this]
  have : Subsingleton (P.ResidueField ⊗[B] (M ⧸ N)) := by
    have h0 : ∀ z : P.ResidueField ⊗[B] (M ⧸ N), z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := hf z
      have : f w ∈ LinearMap.range f := ⟨w, rfl⟩
      rw [hr] at this
      exact this
    exact ⟨fun a b => by rw [h0 a, h0 b]⟩
  obtain ⟨u, hu, hum⟩ := GlobalTheory.SS.DefectZero.exists_smul_eq_zero B P.ResidueField (M ⧸ N) (N.mkQ m)
  refine ⟨u, fun H => hu (Ideal.algebraMap_residueField_eq_zero.mpr H), ?_⟩
  have : (Submodule.Quotient.mk (u • m) : M ⧸ N) = 0 := by rw [Submodule.Quotient.mk_smul]; exact hum
  exact (Submodule.Quotient.mk_eq_zero N).mp this

def LeafCoordsPointRes : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I) (y : Fin e → B),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ ∧
    Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

theorem LeafCoordsPointLoc_of (hR : LeafCoordsPointRes) : LeafCoordsPointLoc := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨t, y, hI, hΩ⟩ := hR d e A B I hB hBI P hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  have := hB.isStandardSmooth
  refine ⟨fun j => t j, y, fun j => (t j).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P t hI ⟨x, hx⟩
    refine ⟨s, hs, Submodule.mem_sup_left ?_⟩
    have := Submodule.mem_map_of_mem (f := I.subtype) hsm
    rw [Submodule.map_span, ← Set.range_comp] at this
    simpa [Function.comp_def] using this
  · intro ω
    obtain ⟨s, hs, hsm⟩ := exists_smul_mem_of_span P _ hΩ ω
    exact ⟨s, hs, Submodule.mem_sup_left hsm⟩

theorem LeafCoordsPoint_of_res (hR : LeafCoordsPointRes) : LeafCoordsPoint :=
  LeafCoordsPoint_of (LeafCoordsPointLoc_of hR)

end LateralTheory.E.LeafCoordsPointPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPairRelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafTripleFPPf

namespace LateralTheory.E.LeafPairRelPf

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' R'' : Subalgebra k Ω} (h : R ≤ R')
    (h' : R' ≤ R'') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

def LeafFactorStage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C E Y : Scheme.{0}} (c : C ⟶ Sp Ω) (p : E ⟶ Sp R) (w : C ⟶ E), FP p → ∀ (hs : IsPullback w c p (toR R))
    (f : Y ⟶ Sp R), LocallyOfFinitePresentation f → ∀ (a : C ⟶ Y), a ≫ f = c ≫ toR R →
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (g : pullback p (incl h) ⟶ Y),
      g ≫ f = pullback.snd p (incl h) ≫ incl h ∧
      pullback.lift w (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ g = a

theorem LeafPairRel_of (hO : LeafObjFP) (hF : LeafFactorStage) : LeafPairRel := by
  intro k _ Ω _ _ R hRfg C0 C1 c0 γ1 h1fp D0 q v0 hq hs
  obtain ⟨R1, hR1, E, p1, w, hp1, hsE⟩ := hO k Ω (γ1 ≫ c0) h1fp
  have h0 : R ≤ R ⊔ R1 := le_sup_left
  have h1 : R1 ≤ R ⊔ R1 := le_sup_right
  have hfg : (R ⊔ R1).FG := hRfg.sup hR1
  have hsE' := pb_lift h1 hsE
  have hlfp : LocallyOfFinitePresentation (pullback.snd q (incl h0)) := (fp_snd q (incl h0) hq).1
  obtain ⟨S, h, hS, g, hg1, hg2⟩ := hF k Ω (R ⊔ R1) hfg (γ1 ≫ c0) (pullback.snd p1 (incl h1)) _
    (fp_snd _ _ hp1) hsE' (pullback.snd q (incl h0)) hlfp
    (γ1 ≫ pullback.lift v0 (c0 ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hs.w))
    (by simp only [Category.assoc, pullback.lift_snd])
  refine ⟨S, h0.trans h, hS, pullback (pullback.snd p1 (incl h1)) (incl h),
    pullback.lift (g ≫ pullback.fst q (incl h0)) (pullback.snd _ _) ?_,
    pullback.lift (pullback.lift w ((γ1 ≫ c0) ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hsE.w))
      ((γ1 ≫ c0) ≫ toR S) (by simp only [Category.assoc, toR_incl, pullback.lift_snd]), ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc, incl_incl]
  · rw [pullback.lift_snd]; exact fp_snd _ _ (fp_snd _ _ hp1)
  · convert pb_lift h hsE' using 2; exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hg2,
        Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LeafPairRelPf

end
end

