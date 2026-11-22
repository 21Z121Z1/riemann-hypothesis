import Development.EtaleCohomology.EtaleSheaves.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.EtaleCohomology.EtaleSheaves.Bundle0044
import Development.EtaleCohomology.EtaleSheaves.Bundle0043
import Development.EtaleCohomology.EtaleSheaves.Bundle0047

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDimBoundPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafDimBoundPf

theorem dim_le_of_quasiFinite (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.QuasiFinite A S] : ringKrullDim S ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := hPQ.le
  refine lt_of_le_of_ne (fun x hx => hle hx) ?_
  intro h
  apply hPQ.ne
  have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)
  exact PrimeSpectrum.ext this

theorem dim_le_of_stdSmooth1 (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] : ringKrullDim S ≤ ringKrullDim R + 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S
  let _ : Algebra (MvPolynomial (Fin 1) R) S := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) R) S := hg
  have h1 := dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at h1
  simpa using h1

theorem dim_affineOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim (V : Set X) = ringKrullDim Γ(X, V) := by
  have h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V)) :=
    (Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq
  rw [h1]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

theorem dim_affineOpen_Spec_le (A : CommRingCat.{0}) {U : (Spec A).Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(Spec A, U) ≤ ringKrullDim A := by
  rw [← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]
  exact topologicalKrullDim_subspace_le _ _

theorem LeafDimBound_of : LateralTheory.E.LeafDescendVCut.LeafDimBound := by
  intro k _ Ω _ _ R hR D0 q hq
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := hq.exists_isStandardSmoothOfRelativeDimension x
  have : IsNoetherianRing Γ(Sp R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Sp R, U) Γ(D0, V) := (q.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V) := hs
  refine ⟨(V : Set D0), V.isOpen, hx, ?_⟩
  rw [dim_affineOpen hV]
  calc ringKrullDim Γ(D0, V) ≤ ringKrullDim Γ(Sp R, U) + 1 := dim_le_of_stdSmooth1 _ _
    _ ≤ ringKrullDim R + 1 := by
      gcongr
      exact dim_affineOpen_Spec_le (CommRingCat.of R) hU

end LateralTheory.E.LeafDimBoundPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDimOpenPf
section
open AlgebraicGeometry CategoryTheory LateralTheory.E.E4 Topology

namespace LateralTheory.E.LeafDimOpenPf

theorem dim_mono {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem dim_basicOpen (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (g : A) (hg : g ≠ 0) {n : ℕ} (hn : Algebra.trdeg k A = n) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) = n := by
  let B := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain B := IsLocalization.isDomain_localization hle
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective B hle)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers g)
  have htr : Algebra.trdeg k B = n := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A B, hn]
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B g).isEmbedding
      (PrimeSpectrum.localization_away_comap_range B g),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq k B htr]

theorem LeafDimOpen_of : LateralTheory.E.LeafCloseBCut.LeafDimOpen := by
  intro k _ X b _ hX U hU hne
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨A0, _, _, _, _, _, j0, _, ⟨p0, hp0⟩, -, htr0⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x0
  obtain ⟨n, -, htn⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A0
  have hK := htr0.symm.trans htn
  have hup : topologicalKrullDim X ≤ n := by
    refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, le_of_eq ?_⟩
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans
      (GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans hK))
  refine hup.trans ?_
  have hVo : IsOpen (j0 ⁻¹' U) := hU.preimage j0.isOpenEmbedding.continuous
  have hpV : p0 ∈ j0 ⁻¹' U := by simpa [Set.mem_preimage, hp0] using hx0
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV hVo
  have hg : g ≠ 0 := by
    rintro rfl; exact (PrimeSpectrum.mem_basicOpen _ _).mp hpg (Ideal.zero_mem _)
  have hd := dim_basicOpen k A0 g hg htn
  calc (n : WithBot ℕ∞) = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0)) := hd.symm
    _ = topologicalKrullDim (j0 '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0))) :=
      (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
        (j0.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
        (by rw [Set.range_comp]; exact congrArg _ Subtype.range_coe)).symm
    _ ≤ topologicalKrullDim U := dim_mono (by rintro _ ⟨q, hq, rfl⟩; exact hsub hq)

end LateralTheory.E.LeafDimOpenPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafEvMkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafEvMkPf

variable {R : Type} [CommRing R]

def preLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.ofHom (Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down))
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y'
    obtain ⟨y⟩ := y'
    have := ha V.unop U.unop g.unop y
    simp only [Sec.res, Quiver.Hom.op_unop, op_unop] at this
    dsimp [freeP]
    change (Finsupp.lift (F.obj.obj V) (ULift.{1} R) (ULift.{1} (P.obj V)) (fun y => a V.unop y.down))
        (Finsupp.mapDomain (fun x : ULift.{1} (P.obj U) => ULift.up (P.map g x.down)) (Finsupp.single (ULift.up y) 1)) =
      F.obj.map g ((Finsupp.lift (F.obj.obj U) (ULift.{1} R) (ULift.{1} (P.obj U)) (fun y => a U.unop y.down)) (Finsupp.single (ULift.up y) 1))
    rw [Finsupp.mapDomain_single, Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index, Finsupp.sum_single_index]
    · simpa using this.symm
    all_goals simp

theorem preLift_app {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((preLift a ha).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = a U x := by
  show (Finsupp.lift (F.obj.obj (op U)) (ULift.{1} R) (ULift.{1} (P.obj (op U))) (fun y => a U y.down)) (Finsupp.single (ULift.up x) 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

def shLift {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (preLift a ha) F.property)

theorem shLift_gen {P : PSh} {F : Shv R} (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U) (ha) (U : Scheme.{0})
    (x : P.obj (op U)) : ((shLift a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  unfold freeGen
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyLift Scheme.etaleTopology (preLift a ha) F.property).app (op U)).hom _ = _
  rw [toSheafify_sheafifyLift]
  exact preLift_app a ha U x

variable {E : Spc} {I : Cx R} {n : ℤ}

def comp (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : ((chains R).obj E).X (-(p : ℤ)) ⟶ I.X s :=
  (chainsXIso R E p).hom ≫ shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x)

theorem comp_key (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p q : ℕ) (hq : q = p) (s : ℤ) (h : -(p : ℤ) + n = s) (h' : -(q : ℤ) + n = s)
    (e : ((chains R).obj E).X (-(p : ℤ)) = ((chains R).obj E).X (-(q : ℤ))) :
    (chainsXIso R E p).inv ≫ eqToHom e ≫ comp a ha q s h' =
      shLift (P := E.obj (op (SimplexCategory.mk p))) (a p s h) (fun V U g x => ha p s h V U g x) := by
  subst hq
  simp [comp]

theorem LeafEvMk_of : LateralTheory.E.ChernClassExistence.LeafEvMk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk fun i j hij => if hi : i ≤ 0 then
      eqToHom (congrArg (fun k => ((chains R).obj E).X k) (by omega : i = -(((-i).toNat : ℕ) : ℤ))) ≫
        comp a ha ((-i).toNat) j (by omega) else 0, ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dif_pos (by omega), comp_key a ha p _ (by omega) s h]
  exact shLift_gen _ _ U x

end LateralTheory.E.LeafEvMkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueExtendPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

lemma dominant_of_generic {C W : Scheme.{0}} (e : W ⟶ C) [IsOpenImmersion e] (x : C)
    (hx : IsGenericPoint x (⊤ : Set C)) (g : Spec (C.presheaf.stalk x) ⟶ W)
    (hg : g ≫ e = C.fromSpecStalk x) : IsDominant g := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro w
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← hg] at hpt
  have he : e (g pt) = x := hpt
  have hmem : g pt ∈ Set.range g := ⟨_, rfl⟩
  have h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply h1
  rw [e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]
  show e w ∈ closure {x}
  rw [show closure ({x} : Set C) = (⊤ : Set C) from hx]
  trivial

theorem LeafGlueExtend_of : LateralTheory.E.LeafExtendCut.LeafGlueExtend := by
  intro C X S _ sC p _ x hx ψ H
  choose U hyU hxU f hf1 hf2 using H
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)
  have hcompat0 : ∀ i j : C,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    have : IsReduced (pullback (U i).ι (U j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    let g := pullback.lift ((U i).fromSpecStalkOfMem x (hxU i))
      ((U j).fromSpecStalkOfMem x (hxU j))
      (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
    have : IsDominant g :=
      dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g
        (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
    refine ext_of_isDominant_of_isSeparated p ?_ g ?_
    · simp only [Category.assoc, hf2]; rw [pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j :=
    fun i j => hcompat0 i j
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · have := 𝒰.ι_glueMorphisms f hcompat x
    rw [← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]
    change _ ≫ 𝒰.f x ≫ _ = _
    rw [this]
    exact hf1 x
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)
    rw [𝒰.ι_glueMorphisms_assoc f hcompat y]
    exact hf2 y

end LateralTheory.E.LeafGlueExtendPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafInj0Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_pts {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop}
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧
      Cov U' (fun U'' b => P U'' (b ≫ a))) : Cov U P := by
  choose U' a y hy hC using h
  choose T hT hP using hC
  let R : Sieve U :=
    { arrows := fun {Z} g => ∃ x, ∃ b : Z ⟶ U' x, T x b ∧ g = b ≫ a x
      downward_closed := by
        rintro Z W g ⟨x, b, hb, rfl⟩ h
        exact ⟨x, h ≫ b, (T x).downward_closed hb h, by simp⟩ }
  refine ⟨R, ?_, ?_⟩
  · have h0 : Sieve.ofArrows U' a ∈ (EtTop B) U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨z, y z, hy z⟩
    refine (EtTop B).transitive h0 R ?_
    intro Z f hf
    obtain ⟨W, g, f', hf', rfl⟩ := hf
    cases hf' with
    | mk x =>
      refine (EtTop B).superset_covering ?_ ((EtTop B).pullback_stable g (hT x))
      intro V c hc
      exact ⟨x, c ≫ g, hc, by simp⟩
  · rintro Z g ⟨x, b, hb, rfl⟩
    exact hP x Z b hb

def LeafInj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

def LeafInj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

theorem LeafInj0_of (hW : LeafInj0W) (hV : LeafInj0V) : LateralTheory.E.LeafDegCut.LeafInj0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp1 hp2 hp3 hS U c hc
  apply cov_of_pts
  intro x
  by_cases hx : U.hom x ∈ Set.range ι
  · exact hW hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c x hx
  · exact hV hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c hc x hx
end LateralTheory.E.LeafInj0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafIrredPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafIrredPf

lemma mem_range {C0 D0 S T : Scheme.{0}} {v0 : C0 ⟶ D0} {c0 : C0 ⟶ T} {q : D0 ⟶ S} {t : T ⟶ S}
    (h : IsPullback v0 c0 q t) (x : D0) (y : T) (hxy : q x = t y) : x ∈ Set.range v0 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t) x y hxy
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← hz, ← h.isoPullback_inv_fst]
  rfl

lemma spec_gen {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (y : Sp Ω) (p : Sp R) :
    toR R y ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) ((toR R) y) p).mp
  intro a ha
  have hA : (toR R).base y = PrimeSpectrum.comap (algebraMap R Ω) y := by
    rw [Spec.map_base]; rfl
  change a ∈ ((toR R).base y).asIdeal at ha
  rw [hA] at ha
  let y' : PrimeSpectrum Ω := y
  have ha' : algebraMap R Ω a ∈ y'.asIdeal := ha
  rw [Ideal.eq_bot_of_prime y'.asIdeal, Ideal.mem_bot] at ha'
  have ha := ha'
  have : a = 0 := Subtype.ext (by simpa using ha)
  rw [this]; exact p.asIdeal.zero_mem

theorem LeafIrred_of : LeafIrred := by
  intro k _ Ω _ _ R _ C0 D0 c0 q v0 hc hq h
  obtain ⟨hint, -, -⟩ := hc
  have := hint
  have := hq
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : IrreducibleSpace C0 := irreducibleSpace_of_isIntegral C0
  have hirr : IsIrreducible (Set.range v0) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C0).image v0 v0.continuous.continuousOn
  have hdense : Dense (Set.range v0) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨c⟩ := (inferInstance : Nonempty C0)
    have hopen : IsOpen (q '' U) := q.isOpenMap U hU
    have hmem : toR R (c0 c) ∈ q '' U := (spec_gen R (c0 c) (q x)).mem_open hopen ⟨x, hx, rfl⟩
    obtain ⟨x', hx'U, hx'⟩ := hmem
    exact ⟨x', hx'U, mem_range h x' (c0 c) hx'⟩
  have : IsIrreducible (Set.univ : Set D0) := by
    rw [← hdense.closure_eq]; exact hirr.closure
  exact { isPreirreducible_univ := this.2, toNonempty := ⟨this.1.some⟩ }

end LateralTheory.E.LeafIrredPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKill1Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev YA {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) : Scheme.{0} :=
  pullback (toBY p U) t

abbrev prA {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback (pullback.snd (toBY p U) t ≫ t ≫ U.hom) ι ⟶ YA p U t :=
  pullback.fst _ _

abbrev aW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback (pullback.snd (toBY p U) t ≫ t ≫ U.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (pullback.fst (toBY p U) t) (𝟙 W) (𝟙 B)
    (by erw [Category.comp_id]; exact (pullback.condition_assoc _).symm) (by simp)

abbrev ptA (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A]
    (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prA p ι U t) (aW p ι U t) (pullback.fst (toBY p U) t) (pullback.lift_fst _ _ _).symm m

def LeafStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y ⟶ B), IsProper p → ∀ (U : B.Etale) (m : ℤ) (y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → ptA q i p ι U t m y = 0) →
  Cov U (fun _ a => rY q i p ι a m y = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (U : B.Etale) (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
  ¬ Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) → ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prA p ι U t)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1)
  (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) →
  ptA q i (g2 ≫ g1 ≫ p) ι U t 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0

end LateralTheory.E.LeafKill1Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLocalExtendPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafLocalExtendPf

lemma specMap_comp_fromSpecStalkOfMem {C : Scheme.{0}} (U : C.Opens) {x y : C} (h : x ⤳ y)
    (hyU : y ∈ U) (hxU : x ∈ U) :
    Spec.map (C.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hyU =
      U.fromSpecStalkOfMem x hxU := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma existence_of_isProper {X S : Scheme.{0}} (p : X ⟶ S) [IsProper p] :
    ValuativeCriterion.Existence p := by
  have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  exact this.1

theorem LeafLocalExtend_of : LateralTheory.E.LeafExtendCut.LeafLocalExtend := by
  intro C X S _ sC p _ x y hx h hv hfr ψ hψ
  have hdom : IsDomain (C.presheaf.stalk y) := inferInstance
  let alg : Algebra (C.presheaf.stalk y) (C.presheaf.stalk x) :=
    (C.presheaf.stalkSpecializes h).hom.toAlgebra
  let fld : Field (C.presheaf.stalk x) := IsFractionRing.toField (C.presheaf.stalk y)
  have hsq : CommSq ψ (Spec.map (C.presheaf.stalkSpecializes h)) p (C.fromSpecStalk y ≫ sC) :=
    ⟨by rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, hψ]⟩
  let sq : ValuativeCommSq p :=
    @ValuativeCommSq.mk _ _ p (C.presheaf.stalk y) _ hdom hv (C.presheaf.stalk x) fld alg hfr
      ψ (C.fromSpecStalk y ≫ sC) hsq
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (existence_of_isProper p sq).exists_lift
  change Spec.map (C.presheaf.stalkSpecializes h) ≫ l = ψ at hl1
  change l ≫ p = C.fromSpecStalk y ≫ sC at hl2
  obtain ⟨U, hyU, f, hf1, hf2⟩ := spread_out_of_isGermInjective' sC p l hl2
  have hxU : x ∈ U := h.mem_open U.2 hyU
  refine ⟨U, hyU, hxU, f, ?_, hf2⟩
  rw [← hl1, hf1, ← Category.assoc, specMap_comp_fromSpecStalkOfMem U h hyU hxU]

end LateralTheory.E.LeafLocalExtendPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNegPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNegPf

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  change IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i
  change -(i : ℤ) ≠ n
  omega

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) :
    IsZero ((res R F).X n) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

theorem cone_isZero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (p : ℤ) (hp : 0 < p) :
    IsZero ((mappingCone ((chains R).map f)).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply mappingCone.ext_from _ (p + 1) p rfl
  · exact (chains_isZero R U (p + 1) (by omega)).eq_of_src _ _
  · exact (chains_isZero R E p hp).eq_of_src _ _

theorem cochain_eq_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain (mappingCone ((chains R).map f)) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (res_isZero R F q hq).eq_of_tgt _ _
  · exact (cone_isZero R f p (by omega)).eq_of_src _ _

theorem LeafNeg_of : LateralTheory.E.LeafDegCut.LeafNeg := by
  intro R _ U E f F m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  have hx : x = y := by
    ext1
    rw [cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]
  rw [hx]

end LateralTheory.E.LeafNegPf
end
end

