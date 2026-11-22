import Development.EtaleCohomology.EtaleSheaves.Bundle0034
import Development.EtaleCohomology.EtaleSheaves.Bundle0032
import Development.EtaleCohomology.TateTwists.Bundle0022
import Development.EtaleCohomology.EtaleSheaves.Bundle0042
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

-- bundled from Development.EtaleCohomology.EtaleSheaves.AugBij
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationBijective

def Aug : Prop := ∀ q : ℕ, ∃ φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1

def AugBij : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Bijective (φ T)

theorem Tw0_of (hA : Aug) (hB : AugBij) : LateralTheory.E.LCIsoPf.Tw0 := by
  intro q
  obtain ⟨φ, hnat, hgen⟩ := hA q
  have hb := hB q φ hnat hgen
  refine ⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩
  intro V U g hV hU a
  apply (hb V hV).1
  have h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)),
      φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b := fun T hT b =>
    (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b
  rw [hnat, h1 U hU, h1 V hV]

end LateralTheory.E.TateTwistZeroAugmentationBijective
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechYoneda
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

theorem CechSigma_of (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of cechYoneda hS

end LateralTheory.E.CechSigma_xy1Pf_Yo
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartGeoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartGeoPf

theorem chartStdGeo_pf : ChartStdGeo := by
  intro X S p n _ x W hxW
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) x
  obtain ⟨g, hgW, hxg⟩ := hV.exists_basicOpen_le ⟨x, hxW⟩ hxV
  refine ⟨U, hU, X.basicOpen g, hV.basicOpen g, (X.basicOpen_le g).trans e, hxg, hgW, ?_⟩
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h3 := h1.comp hf
  rw [zero_add] at h3
  convert h3 using 1
  rw [← Scheme.Hom.appLE_map p e (homOfLE (X.basicOpen_le g)).op]
  rfl

theorem rangeKer_pf : RangeKer := by
  intro X Z ι _ V hV y
  have hy : hV.fromSpec y ∈ V := by
    have h := hV.range_fromSpec
    exact (show hV.fromSpec y ∈ (V : Set X) from h ▸ Set.mem_range_self y)
  have hcl : closure (Set.range ι) = Set.range ι := ι.isClosedEmbedding.isClosed_range.closure_eq
  have key : ∀ f : Γ(X, V), hV.fromSpec y ∈ X.basicOpen f ↔ f ∉ (show PrimeSpectrum Γ(X, V) from y).asIdeal := by
    intro f
    show y ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
    rw [hV.fromSpec_preimage_basicOpen]
    rfl
  rw [← hcl, ← Scheme.Hom.support_ker, SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hy,
    Scheme.Hom.ker_apply, Scheme.mem_zeroLocus_iff]
  simp only [key, not_not]
  rfl

theorem quotLoc_pf : QuotLoc := by
  intro n A B T _ _ _ _ π hπ hloc P hP hI
  obtain ⟨s, hs, H⟩ := hloc
  have hPb : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ (by simpa using hI)
  obtain ⟨t, hts, htP⟩ : ∃ t ∈ s, t ∉ P.map π := by
    by_contra! hc
    exact hPb.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  obtain ⟨g, rfl⟩ := hπ t
  have hg : g ∉ P := fun h => htP (Ideal.mem_map_of_mem π h)
  refine ⟨g, hg, ?_⟩
  set φ : Localization.Away g →+* Localization.Away (π g) := Localization.awayMap π g with hφ
  have hsurj : Function.Surjective φ := by
    rw [hφ, Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    exact ⟨b, 0, by simp⟩
  have hker : RingHom.ker φ = (RingHom.ker π).map (algebraMap B (Localization.Away g)) :=
    IsLocalization.ker_map _ π (Submonoid.map_powers π g)
  let e : (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g))) ≃+*
      Localization.Away (π g) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : (e.symm : Localization.Away (π g) →+* _).comp
      ((algebraMap T (Localization.Away (π g))).comp (π.comp (algebraMap A B))) =
      algebraMap A (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g))) := by
    ext a
    apply e.injective
    simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply, RingEquiv.apply_symm_apply]
    rw [IsScalarTower.algebraMap_apply A B]
    show _ = e (Ideal.Quotient.mk _ (algebraMap B (Localization.Away g) (algebraMap A B a)))
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp [φ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap, ← he]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).1 _ e.symm (H _ hts)

theorem ChartGeo_of_parts (h1 : ChartStdGeo) (h2 : RangeKer) (h3 : QuotLoc) : LateralTheory.E.LeafChartAffPf.ChartGeo := by
  intro X Z S p ι _ d e _ _ x hx W hxW
  obtain ⟨U, hU, V, hV, hUV, hxV, hVW, hstd⟩ := h1 p (e + d) x W hxW
  letI : Algebra Γ(S, U) Γ(X, V) := (p.appLE U V hUV).hom.toAlgebra
  have h0 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension e) (ι ≫ p) inferInstance ⟨U, hU⟩
    ⟨ι ⁻¹ᵁ V, hV.preimage ι⟩ ((le_refl (ι ⁻¹ᵁ V)).trans ((TopologicalSpace.Opens.map ι.base).map (homOfLE hUV)).le)
  rw [← Scheme.Hom.appLE_comp_appLE ι p U V (ι ⁻¹ᵁ V) hUV le_rfl, ← Scheme.Hom.app_eq_appLE,
    CommRingCat.hom_comp] at h0
  refine ⟨Γ(S, U), Γ(X, V), inferInstance, inferInstance, inferInstance, RingHom.ker (ι.app V).hom, hstd,
    fun P hP hI => h3 e _ _ _ (ι.app V).hom (ι.app_surjective V hV) h0 P hP hI,
    hV.fromSpec, inferInstance, ?_, ?_, fun y => h2 ι V hV y⟩
  · rw [hV.range_fromSpec]; exact hxV
  · rw [hV.range_fromSpec]; exact hVW

end LateralTheory.E.ChartGeoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassExistence

def LeafEvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LeafEvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleKummerChernEdgeValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def EtaleKummerChernTriangleValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

def EtaleKummerChernCochainCoboundaryVanishesOnEdges : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTriangles : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (δ 2 3 α) 3 0 (by simp) U x = 0

theorem cx_ext_pf : LateralTheory.EtaleFoundations.cx_ext := by
  intro R _ E I n α h
  apply LateralTheory.E.ChernCocycleExistenceAndUniqueness.cochain_ext_ev α 0
  intro p s hs U x
  rw [h]
  simp [ev]

theorem res_neg_pf : LateralTheory.EtaleFoundations.res_neg := by
  intro q s hs U a
  exact LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q s hs) U a 0

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : LeafEvMk) (hd : LeafEvDelta) (h1 : EtaleKummerChernEdgeValuesExistNatural) (h2 : EtaleKummerChernTriangleValuesExistNatural)
    (c1 : EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) : LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists := by
  intro q _ E L hi
  exact LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values hmk h1 h2 (LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components hd cx_ext_pf res_neg_pf c1 c2 c3) q L hi

end LateralTheory.E.ChernClassExistence
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CochainComplexSingleFunctorZeroMapFZero
section
noncomputable section
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso] <;> rfl

lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  ext i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
    first
    | (apply Eq.symm; refine (Category.assoc _ _ _).trans ?_; congr 1; exact Iso.inv_hom_id_assoc _ _)
    | (dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at *; simp)
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CokernelKilling
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KillCokPf

def Pointwise : Prop := B1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D) (O : CommRingCat.{0}) (o : D ⟶ O), IE o → BC q i φ (d ≫ o) →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (m : ℤ) (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) (Q : Ideal O), Q.IsPrime →
  ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = Q.comap o.hom ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)

def Assemble : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m),
  (∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = r ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem KillCok_of (hC : Coprod) (hP : Pointwise) (hA : Assemble) : LateralTheory.E.DescLocPf.Fine.KillCok := by
  intro hH q _ i n A Y φ hq P _ het _ D d hD hpts Y' w φ' hpo m _ y
  have hB1 : B1 := hH.2.2.2.2.2.2.1
  have hloc : ∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧
      Q₁.comap e.hom = r ∧ ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro r hr
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts r hr
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hP hB1 q i φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
    exact ⟨D₁, e, Q₁, he, hQ₁, hc.trans hQr, rest⟩
  obtain ⟨E, e, Y'', u, φ'', he, hs, hpo', hy⟩ := hA hC q i φ' m y hloc
  exact ⟨E, e, Y'', u, φ'', he, hs, het d e hD he, hpo', hy⟩

end LateralTheory.E.KillCokPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CorePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

def ImageClosed : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens) (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      IsClosedImmersion (γ.imageι ≫ pullback.snd p₁ q)

theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

theorem Core_of (hI : ImageClosed) : Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  have hne : Nonempty X₁ := inferInstance
  obtain ⟨x₀⟩ := hne
  obtain ⟨j₀, -⟩ := hUc x₀
  let V : X₁.Opens := Finset.univ.inf U
  have hV : ∀ j, V ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  have hVne : (V : Set X₁).Nonempty := inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP (V.ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : V.toScheme ⟶ pullback p₁ q := pullback.lift V.ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = V.ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    hI p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hV γ hγ1 hγ2, hVne, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.CorePf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverExistence
section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.CoverExistence

theorem Cover_of : LateralTheory.E.ChowGraphCut.Cover := by
  intro A _ X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end LateralTheory.E.CoverExistence
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagCompPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagCompPf

theorem block_unique {A : Type} [CommRing A] (P R : PartDiagCut.Part A) (e : A) (he : e ∈ R.1) (a b : P.1)
    (ha : e * a.1 = e) (hb : e * b.1 = e) : a = b := by
  by_contra hne
  have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
  have h0 : a.1 * b.1 = 0 := P.orth a.1 a.2 b.1 b.2 hne'
  have : e = 0 := by
    calc e = e * a.1 * b.1 := by rw [ha, hb]
      _ = e * (a.1 * b.1) := by ring
      _ = 0 := by rw [h0, mul_zero]
  exact (R.idem e he).2 this

theorem par_trans {B : Type} [CommRing B] (I : Ideal B) {P Q R : PartDiagCut.Part (B ⧸ I)} (h1 : P ≤ Q) (h2 : Q ≤ R) (e : R.1) :
    par (h1.trans h2) e = par h1 (par h2 e) := by
  apply block_unique P R e.1 e.2
  · exact par_spec _ e
  · calc e.1 * (par h1 (par h2 e)).1 = e.1 * (par h2 e).1 * (par h1 (par h2 e)).1 := by rw [par_spec h2 e]
      _ = e.1 * ((par h2 e).1 * (par h1 (par h2 e)).1) := by ring
      _ = e.1 := by rw [par_spec h1 (par h2 e), par_spec h2 e]

theorem DiagComp_of : DiagComp := by
  intro B _ I P Q R h1 h2
  ext x e
  have key : ∀ (g g' : B →+* B), g = g' → ∀ (a b : P.1), a = b →
      ∀ (hA : S I a.1 ≤ (S I e.1).comap g) (hD : S I b.1 ≤ (S I e.1).comap g'),
      IsLocalization.map (M := S I a.1) (T := S I e.1) (Localization (S I e.1)) g hA (x a)
      = IsLocalization.map (M := S I b.1) (T := S I e.1) (Localization (S I e.1)) g' hD (x b) := by
    rintro g _ rfl a _ rfl hA hD; rfl
  simp only [stageMap, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  erw [IsLocalization.map_map]
  exact key _ _ (RingHom.id_comp _).symm _ _ (par_trans I h1 h2 e) _ _

end LateralTheory.E.DiagCompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagIdPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagIdPf

theorem par_self {A : Type} [CommRing A] {P : LateralTheory.E.PartDiagCut.Part A} (h : P ≤ P) (e : P.1) : par h e = e := by
  apply Subtype.ext
  by_contra hne
  have h1 := par_spec h e
  have h2 := P.orth e.1 e.2 (par h e).1 (par h e).2 (fun h' => hne h'.symm)
  exact (P.idem e.1 e.2).2 (h1.symm.trans h2)

theorem aux {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P) (e0 e : P.1) (hee : e0 = e)
    (hle : S I e0.1 ≤ (S I e.1).comap (RingHom.id B)) :
    IsLocalization.map (M := S I e0.1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B) hle (x e0) = x e := by
  subst hee
  exact IsLocalization.map_id _ _

theorem DiagId_of : LateralTheory.E.PartDiagCut.DiagId := by
  intro B _ I P h
  refine RingHom.ext fun x => funext fun e => ?_
  simp only [stageMap, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.id_apply]
  exact aux I P x (par h e) e (par_self h e) _

end LateralTheory.E.DiagIdPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagNatPf
section
namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
end

