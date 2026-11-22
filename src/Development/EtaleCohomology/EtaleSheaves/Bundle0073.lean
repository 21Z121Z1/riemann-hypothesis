import Development.EtaleCohomology.EtaleSheaves.Bundle0066
import Development.EtaleCohomology.EtaleSheaves.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
import Development.EtaleCohomology.EtaleSheaves.Bundle0068
import Development.EtaleCohomology.EtaleSheaves.Bundle0067

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafObjFPPf

def Desc (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
    FP q ∧ IsPullback v f q (toR R)

def LeafObjAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), IsAffine X → FP f → Desc k f

def LeafObjGlue : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
    Desc k (U.ι ≫ f) → Desc k (V.ι ≫ f) → Desc k ((U ⊓ V).ι ≫ f) → Desc k f

def LeafQCQSInduct : Prop := ∀ (S : Scheme.{0}) [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop),
    (∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f) →
    (∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f) →
    ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → P f

theorem objectDescent_of_affineDescent (hA : LeafObjAff) (hG : LeafObjGlue) (hI : LeafQCQSInduct) : LeafObjFP := by
  intro k _ Ω _ _ X f hf
  exact hI (Sp Ω) (fun g => Desc k g) (fun g hX hg => hA k Ω g hX hg)
    (fun g hg U V hUV h1 h2 h3 => hG k Ω g hg U V hUV h1 h2 h3) f hf

end LateralTheory.E.LeafObjFPPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPairFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafPairFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  simp only [toR, incl, ← Spec.map_comp]
  congr 1

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem raise {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D) (hq : FP q)
    (hs : IsPullback v c q (toR R)) :
    ∃ (E : Scheme.{0}) (q' : E ⟶ Sp R') (w : C ⟶ E), FP q' ∧ IsPullback w c q' (toR R') := by
  refine ⟨pullback q (incl h), pullback.snd _ _, pullback.lift v (c ≫ toR R') ?_, fp_snd _ _ hq, ?_⟩
  · rw [Category.assoc, toR_incl, hs.w]
  · refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, toR_incl]
    exact hs

def LeafMapFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (q1 : D1 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP q1 → IsPullback v0 c0 q (toR R) →
    IsPullback v1 (γ1 ≫ c0) q1 (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

theorem pairDescent_of_objects_morphisms (hO : LeafObjFP) (hM : LeafMapFP) : LeafPairFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 h1 D0 q v0 hq hsq
  obtain ⟨R1, hR1, D1, q1, v1, hq1, hs1⟩ := hO k Ω (γ1 ≫ c0) h1
  obtain ⟨E0, q0', w0, hq0', hs0'⟩ := raise (le_sup_left : R ≤ R ⊔ R1) c0 q v0 hq hsq
  obtain ⟨E1, q1', w1, hq1', hs1'⟩ := raise (le_sup_right : R1 ≤ R ⊔ R1) (γ1 ≫ c0) q1 v1 hq1 hs1
  exact hM k Ω (R ⊔ R1) (hR.sup hR1) c0 γ1 q0' q1' w0 w1 hq0' hq1' hs0' hs1'

end LateralTheory.E.LeafPairFPPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafProjModelPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.LeafProjModelPf

theorem image_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have hB := Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing
  have hred : ∀ U : Y.affineOpens, _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) := fun U =>
    isReduced_of_injective _ (f.toImage_app_injective U)
  refine @isReduced_of_isReduced_stalk _ (fun z => ⟨?_⟩)
  rintro g ⟨n, e⟩
  obtain ⟨U, hzU, s, rfl⟩ := f.image.presheaf.exists_germ_eq g
  rw [← map_pow, ← map_zero (f.image.presheaf.germ _ z hzU).hom] at e
  obtain ⟨V, hzV, iU, iV, e'⟩ := f.image.presheaf.germ_eq z hzU hzU _ 0 e
  rw [map_pow, map_zero] at e'
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hzV
  have h0 : f.image.presheaf.map (homOfLE hWV).op (f.image.presheaf.map iU.op s) = 0 := by
    have hx := congrArg (f.image.presheaf.map (homOfLE hWV).op) e'
    rw [map_pow, map_zero] at hx
    exact (hred ⟨W, hW⟩).eq_zero _ ⟨n, hx⟩
  rw [← f.image.presheaf.germ_res iU z hzV, ← f.image.presheaf.germ_res (homOfLE hWV) z hzW]
  simp only [CommRingCat.comp_apply] at h0 ⊢
  rw [h0, map_zero]

theorem image_irreducible {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IrreducibleSpace X] :
    IrreducibleSpace f.image := by
  have h1 : IsIrreducible (Set.range f.toImage) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
  have h2 := h1.closure
  rw [f.toImage.denseRange.closure_range] at h2
  exact (irreducibleSpace_def _).mpr h2

theorem leafImageIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] (hX : IsIntegral X) :
    IsIntegral f.image := by
  have := image_isReduced f
  have := image_irreducible f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def LeafQProjImm : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (N : ℕ) (φ : Spec (CommRingCat.of A) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace k N),
    IsImmersion φ ∧ QuasiCompact φ ∧
    φ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N = Spec.map (CommRingCat.ofHom (algebraMap k A))

theorem LeafProjModel_of (h1 : LeafQProjImm) : LateralTheory.E.LeafCloseBCut.LeafProjModel := by
  intro k _ A _ _ _ _
  obtain ⟨N, φ, hi, hq, hc⟩ := h1 k A
  refine ⟨φ.image, φ.imageι ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N, φ.toImage, leafImageIntegral φ inferInstance,
    ?_, inferInstance, ?_⟩
  · have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
    infer_instance
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact hc

end LateralTheory.E.LeafProjModelPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPtVPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafPtVPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling
  LateralTheory.E.SecondDegreeKilling.Comp LateralTheory.E.SecondDegreeKilling.Nbhd

theorem isZero_sec_empty (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    IsZero (F.obj.obj (op X)) :=
  (Sheaf.isTerminalOfBotCover F X (Scheme.bot_mem_grothendieckTopology (P := @Etale) X)).isZero

theorem isZero_free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  ext1
  ext1 U
  by_cases hU : IsEmpty U.unop
  · exact (isZero_sec_empty R ((free R).obj (yoneda.obj X)) U.unop).eq_of_tgt _ _
  · have hE : IsEmpty (ULift.{1} (unop U ⟶ X)) := ⟨fun f => by
      obtain ⟨x⟩ := not_isEmpty_iff.1 hU; exact IsEmpty.false (f.down.base x)⟩
    haveI : Subsingleton ↑(((freeP R).obj (yoneda.obj X)).obj U) := by
      change Subsingleton (ULift.{1} (unop U ⟶ X) →₀ ULift.{1} R); infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

theorem isZero_chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rcases p with _ | k
    · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) 0)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro j; change -(j : ℤ) ≠ (k : ℤ) + 1; omega)
  · exact (isZero_free_empty R X).of_iso (chainsXIso R (sch.obj X) p)

theorem isIso_inr (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (hK : ∀ n, IsZero (K.X n)) :
    IsIso (mappingCone.inr φ) := by
  have : ∀ p, IsIso ((mappingCone.inr φ).f p) := fun p => ⟨⟨(mappingCone.snd φ).v p p (add_zero p), by simp, by
    rw [← mappingCone.id_X φ p (p + 1) rfl, (hK (p + 1)).eq_of_tgt ((mappingCone.fst φ).1.v p (p + 1) rfl) 0]
    simp⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem fgt_bij (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} [IsEmpty X] {E : Spc}
    (f : sch.obj X ⟶ E) (n : ℤ) : Function.Bijective (fgt R f F n) := by
  haveI := isIso_inr R ((chains R).map f) (isZero_chains_empty R X)
  exact hH.1 R (mappingCone.inr ((chains R).map f)) F n

theorem rpl_zero (hH : Hyps) (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') [IsEmpty U']
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (he : pl q i e n = 0)
    (x : Hrel (ZMod q) (sch.map f) (tw q i) n) : rpl q i f f' u e comm n x = 0 := by
  apply (fgt_bij hH (ZMod q) (tw q i) (sch.map f') n).1
  rw [map_zero]
  refine (relNat (ZMod q) (tw q i) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) n x).trans ?_
  change pl q i e n _ = 0
  rw [he]; rfl

theorem isEmpty_pullback_closed_subscheme_section_into_complement {B W Y S : Scheme.{0}} (ι : W ⟶ B) (V : B.Opens) (hVW : (V : Set B) = (Set.range ι)ᶜ)
    (p : Y ⟶ B) (s : S ⟶ B) (hs : Set.range ⇑s ⊆ (V : Set B)) :
    IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun x => by
  have h1 : (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s ≫ s) x = (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x := by
    rw [pullback.condition]
  have h2 : (pullback.snd (pullback.snd p s ≫ s) ι ≫ ι) x ∈ (V : Set B) := by
    rw [← h1]; apply hs; simp only [Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
  rw [hVW] at h2; simp only [Scheme.Hom.comp_apply] at h2; exact h2 ⟨_, rfl⟩⟩

theorem LeafPtV_of : LateralTheory.E.SecondDegreeKilling.LeafPtV := by
  intro hH q _ k _ hq i B W Y Y' toK ι _ V hVW p g hp hgp U A _ t hA hV m hpl y
  haveI := isEmpty_pullback_closed_subscheme_section_into_complement ι V hVW (g ≫ p) (t ≫ U.hom) hV
  let wA : pullback (pullback.snd (g ≫ p) (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶
      pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι :=
    pullback.map _ ι _ ι (fibMap g p (t ≫ U.hom)) (𝟙 W) (𝟙 B)
      (by rw [Category.comp_id, ← Category.assoc (fibMap g p (t ≫ U.hom)), pullback.lift_snd, Category.comp_id]) (by simp)
  have commA : prS (g ≫ p) ι (t ≫ U.hom) ≫ fibMap g p (t ≫ U.hom) = wA ≫ prS p ι (t ≫ U.hom) :=
    (pullback.lift_fst _ _ _).symm
  have hA : prS p ι (t ≫ U.hom) ≫ tY p U t = tW p ι U t ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have hB : prS (g ≫ p) ι (t ≫ U.hom) ≫ tY (g ≫ p) U t = tW (g ≫ p) ι U t ≫ prU (g ≫ p) ι U :=
    (pullback.lift_fst _ _ _).symm
  have hC : prU (g ≫ p) ι U ≫ mY p g U = mW p g ι U ≫ prU p ι U := (pullback.lift_fst _ _ _).symm
  have E1 : tY (g ≫ p) U t ≫ mY p g U = fibMap g p (t ≫ U.hom) ≫ tY p U t := by
    simp only [tY, mY, fibMap, pullback.map_comp, Category.id_comp, Category.comp_id]
  have c1 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (tY (g ≫ p) U t ≫ mY p g U) =
      (tW (g ≫ p) ι U t ≫ mW p g ι U) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mY p g U) hB).trans ((Category.assoc _ _ _).trans
      ((congrArg (tW (g ≫ p) ι U t ≫ ·) hC).trans (Category.assoc _ _ _).symm)))
  have c2 : prS (g ≫ p) ι (t ≫ U.hom) ≫ (fibMap g p (t ≫ U.hom) ≫ tY p U t) =
      (wA ≫ tW p ι U t) ≫ prU p ι U := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ tY p U t) commA).trans ((Category.assoc _ _ _).trans
      ((congrArg (wA ≫ ·) hA).trans (Category.assoc _ _ _).symm)))
  have E2 : tW (g ≫ p) ι U t ≫ mW p g ι U = wA ≫ tW p ι U t := by
    simp only [tW, mW, wA, pullback.map_comp]
    congr 1
  rw [rpl_comp q i _ _ _ _ _ _ _ _ _ c1, rpl_congr q i _ _ _ _ _ _ c1 c2 E2 E1, ← rpl_comp q i _ _ _ _ _ hA _ _ commA c2]
  exact rpl_zero hH q i _ _ _ _ commA m hpl _

end LateralTheory.E.LeafPtVPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHPtPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf

theorem germ (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B : Scheme.{0}} (U : B.Etale) (x : U.left)
    {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (he : ∀ j, IsIso (e j)) (hy : ∀ j, (a j).left (y j) = x)
    (hq : ∀ j, IsUnit ((q : ℕ) : D.obj j))
    (hcomp : ∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left)
    (ht : ∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t)
    (s : Sec (tw q i) U.left) (hs : Sec.res t s = 0) :
    ∃ (U' : B.Etale) (a' : U' ⟶ U) (y' : U'.left), a'.left y' = x ∧ Sec.res a'.left s = 0 := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  have hB1 : B1 := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, eq, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  set z : Ht q (sp (D.obj j)) 0 i := eq _ (Sec.res (e j ≫ (a j).left) s) with hz
  have h0 : pull _ (spMap (c.ι.app j).hom) _ _ z = 0 := by
    rw [hz, spMap, hnat, ← res_comp, ht, hs, map_zero]
  obtain ⟨k, f, hk⟩ := (hB1 q D c hc 0 i).2 j z (hq j) h0
  rw [hz, spMap, hnat, ← res_comp, hcomp] at hk
  have hk' : Sec.res (e k ≫ (a k).left) s = 0 := (eq _).injective (by rw [hk, map_zero])
  refine ⟨V k, a k, y k, hy k, ?_⟩
  have := congrArg (Sec.res (inv (e k))) hk'
  rw [← res_comp, IsIso.inv_hom_id_assoc] at this
  simpa using this

def LeafSHNb : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left), (∀ j, IsIso (e j)) ∧ (∀ j, (a j).left (y j) = x) ∧ (∀ j, IsUnit ((q : ℕ) : D.obj j)) ∧
    (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
    (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧ SH c.pt ∧
    (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left)

def LeafSHTop : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) {J : Type} [SmallCategory J] [Nonempty J]
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
  (t : Sp c.pt ⟶ U.left), (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) →
  (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left) →
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a' : U' ⟶ U), S a' ∧ ∃ t' : Sp c.pt ⟶ U'.left, t' ≫ a'.left = t)

theorem LeafSHPt_of (hN : LeafSHNb) (hT : LeafSHTop) : LeafSHPt := by
  intro hH q _ k _ hq i B U s0 x
  obtain ⟨J, _, _, D, c, hc, V, a, y, e, t, he, hy, hqj, hcomp, ht, hSH, hcof⟩ := hN hH q k hq U s0 x
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨hO, hL⟩ := hT U x D c V a e t ht hcof
  exact ⟨c.pt, inferInstance, t, hSH, hO, hL, fun s hs => germ hH q i U x D c hc V a y e t he hy hqj hcomp ht s hs⟩

end LateralTheory.E.LeafSHPtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensUPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTensUPPf
open LateralTheory.E.LeafTwTensExPf
open Classical

variable {R : Type} [CommRing R] {I J K : Cx R}

theorem lift_lo (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  simp [Pair.lift, lo]

theorem lift_nat (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    ((K.X w).obj.map g.op).hom ∘ₗ μ.lift U w = μ.lift V w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  have e := tres_tmul I J g w ⟨(s, t), h⟩ a b
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (Tens.res g w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [e]
  change Sec.res g (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) = μ.lift V w (lo I J ⟨(s, t), h⟩ (Sec.res g a ⊗ₜ Sec.res g b))
  rw [lift_lo, lift_lo, μ.nat]

theorem lift_d (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    ((K.d w (w + 1)).hom.app (op U)).hom ∘ₗ μ.lift U w = μ.lift U (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  change Sec.map (K.d w (w + 1)) (μ.lift U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) =
    μ.lift U (w + 1) (dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)))
  rw [dT_tmul, map_add, map_zsmul, lift_lo, lift_lo, lift_lo, μ.leibniz, Units.smul_def]

def liftP (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (lift_nat μ g.unop w).symm

theorem tensorPresheafLift_comm (μ : Pair I J K) (w : ℤ) :
    liftP μ w ≫ (K.d w (w + 1)).hom = dTP I J w ≫ liftP μ (w + 1) := by
  ext U : 2
  exact ModuleCat.hom_ext (lift_d μ U.unop w)

theorem etale_tensor_presheaf_lift_is_local_iso {T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (liftP τ w) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {U} y => by
    obtain ⟨S, hS, hP⟩ := hτ.1 U w y
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨x, hx⟩⟩
  have : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (liftP τ w) := ⟨fun {X} x y hxy => by
    let x' : Tens I J X.unop w := x
    let y' : Tens I J X.unop w := y
    have hxy' : τ.lift X.unop w x' = τ.lift X.unop w y' := hxy
    have h0 : τ.lift X.unop w (x' - y') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy'
    obtain ⟨S, hS, hP⟩ := hτ.2 X.unop w (x' - y') h0
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hS
    intro V g hg
    have h1 : Tens.res g w (x' - y') = 0 := hP V g hg
    rw [map_sub, sub_eq_zero] at h1
    exact h1⟩
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem etale_tensor_pairing_universal_property_holds : LateralTheory.E.LeafPairExtPf2.LeafTensUP := by
  intro R _ I J T K τ hτ μ
  have hb : ∀ w, Function.Bijective (fun g : (T.X w).obj ⟶ (K.X w).obj => liftP τ w ≫ g) :=
    fun w => etale_tensor_presheaf_lift_is_local_iso τ hτ w _ (K.X w).property
  choose u0 hu0' using fun w => (hb w).2 (liftP μ w)
  have hu0 : ∀ w, liftP τ w ≫ u0 w = liftP μ w := hu0'
  let u : T ⟶ K :=
    { f := fun w => ⟨u0 w⟩
      comm' := by
        rintro i j rfl
        apply Sheaf.hom_ext
        change u0 i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ u0 (i + 1)
        have key : liftP τ i ≫ (u0 i ≫ (K.d i (i + 1)).hom) = liftP τ i ≫ ((T.d i (i + 1)).hom ≫ u0 (i + 1)) := by
          rw [← Category.assoc, ← Category.assoc, hu0, tensorPresheafLift_comm, tensorPresheafLift_comm, Category.assoc, hu0]
        exact (etale_tensor_presheaf_lift_is_local_iso τ hτ i _ (K.X (i + 1)).property).1 key }
  refine ⟨u, fun U s t w h a b => ?_⟩
  have e := congrArg (fun f => (f.app (op U)).hom (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b))) (hu0 w)
  simp only at e
  rw [← lift_lo τ, ← lift_lo μ]
  exact e

end LateralTheory.E.LeafTensUPPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTripleFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafTripleFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem pb_lift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {f : D ⟶ Sp R} {v : C ⟶ D} (hs : IsPullback v c f (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w)) c
      (pullback.snd f (incl h)) (toR R') := by
  have e1 : pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ pullback.fst f (incl h) = v :=
    pullback.lift_fst _ _ _
  have t : IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫
      pullback.fst f (incl h)) c f (toR R' ≫ incl h) := by rw [e1, toR_incl]; exact hs
  exact IsPullback.of_right t (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (incl h))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def LeafPairRel : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → ∀ (hs : IsPullback v0 c0 q (toR R)),
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (E1 : Scheme.{0}) (e1 : E1 ⟶ pullback q (incl h)) (w1 : C1 ⟶ E1),
      FP (e1 ≫ pullback.snd q (incl h)) ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ pullback.snd q (incl h)) (toR R') ∧
      γ1 ≫ pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) = w1 ≫ e1

theorem tripleDescent_of_pairRelation (hR : LeafPairRel) : LeafTripleFP := by
  intro k _ Ω _ _ R hRfg C0 C1 C2 c0 γ1 γ2 h2 D0 D1 q d1 v0 v1 hq hq1 hs0 hs1 hc
  obtain ⟨R', h, hR', E2, e2, w2, hf2, hs2, hc2⟩ :=
    hR k Ω R hRfg (γ1 ≫ c0) γ2 h2 (d1 ≫ q) v1 hq1 hs1
  have hsnd : pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]) ≫
      pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR', _, _, _, pullback.snd q (incl h),
    pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]), e2,
    pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs0.w),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs1.w), w2, ?_⟩
  refine ⟨fp_snd _ _ hq, ?_, ?_, pb_lift h hs0, ?_, ?_, ?_, hc2⟩
  · rw [hsnd]; exact fp_snd _ _ hq1
  · rw [hsnd]; exact hf2
  · rw [hsnd]; exact pb_lift h hs1
  · rw [hsnd]; exact hs2
  · apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]

end LateralTheory.E.LeafTripleFPPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPfC
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LocSecPfC

variable (R : Type) [CommRing R] (X : Scheme.{0})

def eqv (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃ Sec G X :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ G).trans <|
  (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv (yoneda.obj X ⋙ uliftFunctor.{1}) G.obj).trans
  (uliftYonedaEquiv.{1} (X := X) (F := G.obj ⋙ forget _))

theorem eqv_apply (G : Shv R) (f : (free R).obj (yoneda.obj X) ⟶ G) :
    eqv R X G f = (f.hom.app (op X)).hom (freeGen R _ X (𝟙 X)) := by
  rfl

def eqvAdd (G : Shv R) : ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X :=
  { eqv R X G with
    map_add' := fun f g => by
      change eqv R X G (f + g) = eqv R X G f + eqv R X G g
      rw [eqv_apply, eqv_apply, eqv_apply]
      rfl }

theorem homSec : LateralTheory.E.LocSecPfB.HomSec := by
  intro R _ X
  refine ⟨eqvAdd R X, fun φ f => ?_⟩
  change eqv R X _ (f ≫ φ) = Sec.map φ (eqv R X _ f)
  rw [eqv_apply, eqv_apply]
  rfl

theorem LocSec_of (h2 : LateralTheory.E.LocSecPfB.ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPfB.LocSec_of homSec h2

end LateralTheory.E.LocSecPfC
end
end

