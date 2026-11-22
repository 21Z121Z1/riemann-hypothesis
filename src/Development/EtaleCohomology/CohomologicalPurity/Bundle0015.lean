import Development.EtaleCohomology.CohomologicalPurity.Bundle0007
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
import Development.EtaleCohomology.CohomologicalPurity.Bundle0010

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def chainsP (R : Type) [CommRing R] : Spc ⥤ ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ :=
  (SimplicialObject.whiskering _ _).obj (freeP R) ⋙ AlgebraicTopology.alternatingFaceMapComplex _

def LeafQisLocal : Prop := ∀ (R : Type) [CommRing R] (E E' : Spc) (f : E ⟶ E'),
  (∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  (∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  QuasiIso ((chains R).map f)

def LeafAugLocal : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n) ∧
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n)

theorem LeafLocCutAug.goal_of (hq : LeafQisLocal) (hl : LeafAugLocal) : EtaleLocAug := by
  intro J _ D X c ho hcov hdir hc R _
  exact hq R _ _ (aug _ hc) (fun n => (hl J D X c ho hcov hdir hc R n).1) (fun n => (hl J D X c ho hcov hdir hc R n).2)

theorem LeafLocCutAll.goal_of (hb : EtaleLocBase) (hq : LeafQisLocal) (hl : LeafAugLocal) : LeafLoc :=
  LeafLocCut.goal_of hb (LeafLocCutAug.goal_of hq hl)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocExcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem five_bij {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*} [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3] [AddCommGroup B4]
    [AddCommGroup B5] (f1 : A1 →+ A2) (f2 : A2 →+ A3) (f3 : A3 →+ A4) (f4 : A4 →+ A5)
    (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (v1 : A1 →+ B1) (v2 : A2 →+ B2) (v3 : A3 →+ B3) (v4 : A4 →+ B4) (v5 : A5 →+ B5)
    (hf2 : Function.Exact f1 f2) (hf3 : Function.Exact f2 f3) (hf4 : Function.Exact f3 f4)
    (hg2 : Function.Exact g1 g2) (hg3 : Function.Exact g2 g3) (hg4 : Function.Exact g3 g4)
    (c1 : ∀ x, g1 (v1 x) = v2 (f1 x)) (c2 : ∀ x, g2 (v2 x) = v3 (f2 x)) (c3 : ∀ x, g3 (v3 x) = v4 (f3 x))
    (c4 : ∀ x, g4 (v4 x) = v5 (f4 x))
    (h1 : Function.Surjective v1) (h2 : Function.Bijective v2) (h4 : Function.Bijective v4)
    (h5 : Function.Injective v5) : Function.Bijective v3 := by
  refine ⟨(injective_iff_map_eq_zero v3).2 fun a ha => ?_, fun b => ?_⟩
  · have e4 : f3 a = 0 := h4.1 (by rw [← c3, ha]; simp)
    obtain ⟨a2, rfl⟩ := (hf3 a).1 e4
    have e2 : g2 (v2 a2) = 0 := by rw [c2, ha]
    obtain ⟨b1, hb1⟩ := (hg2 _).1 e2
    obtain ⟨a1, rfl⟩ := h1 b1
    have e1 : f1 a1 = a2 := h2.1 (by rw [← c1, hb1])
    subst e1
    exact (hf2 _).2 ⟨a1, rfl⟩
  · obtain ⟨a4, ha4⟩ := h4.2 (g3 b)
    have e5 : f4 a4 = 0 := h5 (by rw [← c4, ha4, map_zero]; exact (hg4 _).2 ⟨b, rfl⟩)
    obtain ⟨a3, ha3⟩ := (hf4 a4).1 e5
    have e3 : g3 (b - v3 a3) = 0 := by rw [map_sub, c3, ha3, ha4, sub_self]
    obtain ⟨b2, hb2⟩ := (hg3 _).1 e3
    obtain ⟨a2, rfl⟩ := h2.2 b2
    refine ⟨a3 + f2 a2, ?_⟩
    rw [map_add, ← c2, hb2]
    abel

theorem mono_sch_open {X : Scheme.{0}} (U : X.Opens) : Mono (sch.map U.ι) := by
  have hy : Mono (yoneda.map U.ι) := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun T => ?_
    exact (mono_iff_injective _).2 fun a b h => (cancel_mono U.ι).1 h
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun _ => hy

theorem eqv_of_loc (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    {Y : Scheme.{0}} (g : Y ⟶ X) (F : Shv R) : Eqv R (pullback.snd π (sch.map g)) F :=
  fun n => @a1 R _ _ _ _ (L R Y g) F n

theorem eqv_base (a1 : A1) {X : Scheme.{0}} {E : Spc} {π : E ⟶ sch.obj X} (L : Loc π) (R : Type) [CommRing R]
    (F : Shv R) : Eqv R π F := by
  have hi : IsIso (sch.map (𝟙 X)) := inferInstance
  have e : pullback.fst π (sch.map (𝟙 X)) ≫ π = pullback.snd π (sch.map (𝟙 X)) ≫ sch.map (𝟙 X) := pullback.condition
  have h1 : Eqv R (pullback.fst π (sch.map (𝟙 X)) ≫ π) F := by
    rw [e]; exact eqv_comp (eqv_of_loc a1 L R _ F) (eqv_iso _ F)
  have e' : π = inv (pullback.fst π (sch.map (𝟙 X))) ≫ pullback.fst π (sch.map (𝟙 X)) ≫ π :=
    (IsIso.inv_hom_id_assoc _ _).symm
  rw [e']
  exact eqv_comp (eqv_iso _ F) h1

theorem fgt_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  have e : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P := pushout.inl_desc _ _ _
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, e]

theorem hom_nat (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right _ _ x) = pull _ φ.left _ _ (pull _ P.hom _ n x) := by
  rw [← pull_comp, ← pull_comp, Arrow.w φ]

theorem LeafLocExc_of (bd : LeafBd) : LeafLocExc := by
  intro a1 q X U E π L
  obtain ⟨δ, ex, nat, -⟩ := bd
  have hm : Mono (opn U).hom := mono_sch_open U
  have hm' : Mono (abv U π).hom := by
    change Mono (pullback.fst π (sch.map U.ι)); have := mono_sch_open U; infer_instance
  have eR : ∀ i n, Function.Bijective (pull _ (abvMap U π).right (tw q i) n) := fun i =>
    eqv_base a1 L (ZMod q) (tw q i)
  have eL : ∀ i n, Function.Bijective (pull _ (abvMap U π).left (tw q i) n) := fun i =>
    eqv_of_loc a1 L (ZMod q) U.ι (tw q i)
  intro n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact five_bij (pull _ (opn U).hom (tw q i) m) (δ q (opn U) m i) (Hs.fgt q (opn U) (m + 1) i)
    (pull _ (opn U).hom (tw q i) (m + 1))
    (pull _ (abv U π).hom (tw q i) m) (δ q (abv U π) m i) (Hs.fgt q (abv U π) (m + 1) i)
    (pull _ (abv U π).hom (tw q i) (m + 1))
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _) (Hs.pull q (abvMap U π) (m + 1) i)
    (pull _ (abvMap U π).right _ _) (pull _ (abvMap U π).left _ _)
    (ex q _ hm m i).2.1 (ex q _ hm m i).2.2 (ex q _ hm (m + 1) i).1
    (ex q _ hm' m i).2.1 (ex q _ hm' m i).2.2 (ex q _ hm' (m + 1) i).1
    (hom_nat q _ m i) (fun x => (nat q _ _ (abvMap U π) hm' hm m i x).symm) (fgt_nat q _ (m + 1) i)
    (hom_nat q _ (m + 1) i)
    (eR i m).2 (eL i m) (eR i (m + 1)) (eL i (m + 1)).1

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocHenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    apply pushout.hom_ext <;> (simp [dbl.map]; try rfl)
  rw [e, pull_id]

theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

theorem abv_ext {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {Q : Arrow Spc} (α β : Q ⟶ abv U π)
    (hr : α.right = β.right) (hm : α ≫ abvMap U π = β ≫ abvMap U π) : α = β := by
  apply Arrow.hom_ext _ _ _ hr
  apply pullback.hom_ext
  · have wa := Arrow.w α
    have wb := Arrow.w β
    change α.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ α.right at wa
    change β.left ≫ pullback.fst π (sch.map U.ι) = Q.hom ≫ β.right at wb
    rw [hr] at wa
    exact wa.trans wb.symm
  · exact congrArg CommaMorphism.left hm

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h3 : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h1 ≫ opnMap g U' U h2 = opnMap (f ≫ g) U'' U h3 := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem LeafLocHen_of (hI : LeafIndExc) (hZ : LeafZ) (hA : LeafAbv) : LeafLocHen := by
  intro hyp H d P V q hq hfg h
  obtain ⟨a1, -, -, a4, -, -, -, -, b1, -, -, -⟩ := hyp
  have := P.cl
  set A := Γ(P.X, V.1)
  set I := P.ι.ker.ideal V
  set φ := eta H P V
  set g := V.2.fromSpec
  set f : Spec (H.obj A I) ⟶ Spec A := Spec.map (CommRingCat.ofHom φ)
  have hqA : IsUnit (q : A) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have zB := (hZ P.X P.Z P.ι V (H.obj A I) φ).2 P.U P.hU
  have zA := (hZ P.X P.Z P.ι V A (RingHom.id A)).2 P.U P.hU
  rw [Ideal.map_id] at zA
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ g = g := by
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  rw [e1] at zA
  have hle : off (H.obj A I) (I.map φ) ≤ f ⁻¹ᵁ (off A I) := by
    rw [zB, zA]; intro x hx; exact hx
  have ind := hI a1 a4 b1 q φ I hfg (H.ind A I) hqA hle
  obtain ⟨eA, eAr, eAm⟩ := hA _ _ g _ P.U zA
  obtain ⟨eB, eBr, eBm⟩ := hA _ _ (f ≫ g) _ P.U zB
  have sq : eB.hom ≫ abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = opnMap f _ _ hle ≫ eA.hom := by
    apply abv_ext
    · rw [Arrow.comp_right, Arrow.comp_right, eBr, eAr]
      exact (Category.id_comp (sch.map f)).trans (Category.comp_id (sch.map f)).symm
    · rw [Category.assoc, Category.assoc, abvRel_abvMap, eBm, eAm, opnMap_comp]
  have e : abvRel P.U (sch.map f) (sch.map (f ≫ g)) (sch.map g) h = eB.inv ≫ opnMap f _ _ hle ≫ eA.hom := by
    rw [Iso.eq_inv_comp, sq]
  rw [e]
  exact exc_comp q (exc_iso q eB.symm) (exc_comp q ind (exc_iso q eA))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocPrdPfX
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem opnMap_comp_RLocP {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens)
    (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp]

theorem hs_pull_id_RLocP (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  have e : dbl.map (𝟙 P) = 𝟙 _ := by
    apply pushout.hom_ext <;> (simp [dbl.map]; rfl)
  rw [e, pull_id]

theorem LeafLocPrd_of (hCl : LeafCl) (hPR : LeafPrdRing) (hZ : LeafZ) (hAbv : LeafAbv) (hAN : LeafActNat) : LeafLocPrd := by
  intro hyp H d P V q _ hq hG
  have a6 : DivisorNaturality := hyp.2.2.2.2.1
  haveI := P.cl
  have hcl : IsCl d (fcl d) := pick_spec (hCl hyp d)

  have hqA : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
    simpa using this
  have hoff : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B),
      off B ((P.ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
    fun B _ φ => (hZ P.X P.Z P.ι V B φ).2 P.U P.hU
  have e0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
    have e := hoff Γ(P.X, V.1) (RingHom.id _)
    rw [Ideal.map_id] at e
    rw [e]; rfl
  have h0 : off Γ(P.X, V.1) (P.ι.ker.ideal V) ≤ V.2.fromSpec ⁻¹ᵁ P.U := le_of_eq e0
  haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  obtain ⟨c, hcdef⟩ : ∃ c, c = Hs.pull q (opnMap V.2.fromSpec _ _ h0) _ _ (fcl d q P) := ⟨_, rfl⟩
  have hc : ∀ (B : Type) [CommRing B] (φ : Γ(P.X, V.1) →+* B) (x : Fin d → B) hx h, φ.Etale →
      Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B ((P.ι.ker.ideal V).map φ)) (off _ (P.ι.ker.ideal V)) h) _ _ c
        = thom d q B ((P.ι.ker.ideal V).map φ) x hx := by
    intro B _ φ x hx h hφ
    obtain ⟨z, hz⟩ := (hZ P.X P.Z P.ι V B φ).1
    haveI : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr hφ
    have h' : off B ((P.ι.ker.ideal V).map φ) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ P.U :=
      le_of_eq (hoff B φ)
    rw [hcdef, ← hs_pull_comp, opnMap_comp_RLocP _ _ _ _ _ _ _ h']
    exact (hcl q).1 P hq B _ x hx _ z h' inferInstance hz
  have key := hPR hyp H d q Γ(P.X, V.1) (P.ι.ker.ideal V) hqA hG.1 hG.2 c hc

  have hU' := hoff _ (eta H P V)
  obtain ⟨e, he1, he2⟩ := hAbv _ P.X (hensTo H P V) _ P.U hU'
  intro n i
  have hh : off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)) ≤
      Spec.map (CommRingCat.ofHom (eta H P V)) ⁻¹ᵁ off Γ(P.X, V.1) (P.ι.ker.ideal V) := by
    rw [hoff _ (eta H P V), e0]; intro x hx; exact hx
  have hk := key hh n i
  have hpe : Function.Bijective (Hs.pull q e.hom (n + 2 * d) (i + d)) :=
    Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv _ _,
      fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id_RLocP],
      fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id_RLocP]⟩
  have hcomp : ∀ a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i,
      Hs.pull q e.hom _ _ (Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) =
      Hs.act q (P := opn (off (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ((P.ι.ker.ideal V).map (eta H P V)))) a
        (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (eta H P V))) _ _ hh) _ _ c) := by
    intro a
    refine (hAN a6 q _ _ e.hom n (2 * d) i d a _).trans ?_
    rw [he1]
    erw [pull_id]
    rw [← hs_pull_comp, he2, hcdef, ← hs_pull_comp, opnMap_comp_RLocP]
  refine (Function.Bijective.of_comp_iff' hpe _).1 ?_
  have hf := funext hcomp
  rw [show (⇑(Hs.pull q e.hom (n + 2 * d) (i + d)) ∘ fun a : Ht q (sch.obj (Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)))) n i =>
      Hs.act q (P := abv P.U (sch.map (hensTo H P V))) a
        (Hs.pull q (abvMap P.U (sch.map (hensTo H P V))) _ _ (fcl d q P))) = _ from hf]
  exact hk

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafOffContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def OffContN (r : ℕ) : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (x : Fin r → A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span (Set.range x)) D s t n i

def OffContBasic : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (f : A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span {f}) D s t n i

def OffContStep : Prop := A1 → A4 → B1 → LeafBd → LeafExc → OffContBasic → ∀ r : ℕ, OffContN r → OffContN (r + 1)

theorem offContN_zero (hb : OffContBasic) (a1 : A1) (a4 : A4) (b1 : B1) : OffContN 0 := by
  intro q A B _ _ φ x hq J _ _ D s t hc he n i
  have hx : Ideal.span (Set.range x) = Ideal.span {(0 : A)} := by
    rw [Set.range_eq_empty, Ideal.span_empty, Ideal.span_singleton_eq_bot.mpr rfl]
  rw [hx]
  exact hb a1 a4 b1 q φ 0 hq J D s t hc he n i

theorem offContN_all (hb : OffContBasic) (hs : OffContStep) (a1 : A1) (a4 : A4) (b1 : B1) (bd : LeafBd)
    (ex : LeafExc) : ∀ r, OffContN r := by
  intro r
  induction r with
  | zero => exact offContN_zero hb a1 a4 b1
  | succ r ih => exact hs a1 a4 b1 bd ex hb r ih

theorem leafOffCont_of (hb : OffContBasic) (hs : OffContStep) : LeafOffCont := by
  intro a1 a4 b1 bd ex q A B _ _ φ I hI hq J _ _ D s t hc he n i
  obtain ⟨S, hS⟩ := hI
  have h := offContN_all hb hs a1 a4 b1 bd ex S.card q φ (fun k => (S.equivFin.symm k : A)) hq J D s t hc he n i
  have hr : Set.range (fun k => (S.equivFin.symm k : A)) = (S : Set A) := by
    ext a; constructor
    · rintro ⟨k, rfl⟩; exact (S.equivFin.symm k).2
    · intro ha; exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩
  rw [hr, hS] at h
  exact h

theorem off_span_singleton (A : Type) [CommRing A] (f : A) :
    ((off A (Ideal.span {f}) : Set (Spec (CommRingCat.of A))) =
      ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A))) := by
  change (PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

theorem off_span_union (A : Type) [CommRing A] (u v : Set A) :
    off A (Ideal.span (u ∪ v)) = off A (Ideal.span u) ⊔ off A (Ideal.span v) := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span (u ∪ v) : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus ((Ideal.span u : Ideal A) : Set A))ᶜ ∪
      (PrimeSpectrum.zeroLocus ((Ideal.span v : Ideal A) : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.zeroLocus_union, Set.compl_inter]

theorem range_fin_succ {A : Type} {r : ℕ} (x : Fin (r + 1) → A) :
    Set.range x = Set.range (fun k : Fin r => x k.castSucc) ∪ {x (Fin.last r)} := by
  rw [Set.union_singleton]
  ext a; constructor
  · rintro ⟨k, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · exact Set.mem_insert_of_mem _ ⟨k', rfl⟩
    · exact Set.mem_insert _ _
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafPBInvSp : Prop := ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (sp R)

def LeafPBCmp : Prop := A1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ i : ℤ, Eqv _ e (tw q i)

def LeafAffEqv : Prop := A1 → ∀ (q : ℕ) [NeZero q] {E E' : Spc} (e : E ⟶ E'),
  (∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
    (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) →
  ∀ i : ℤ, Eqv _ e (tw q i)

def LeafPBMap : Prop := ∀ (N : ℕ) (R : Type) [CommRing R],
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx (pullback V (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)

theorem leafPBCmp_of (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPBCmp := by
  intro hA1 q _ N R _ _
  obtain ⟨V, e, h1, h2, h3⟩ := hMap N R
  exact ⟨V, e, h1, h2, hAff hA1 q e h3⟩

theorem leafPBInvSp : LeafPBInvSp := by
  intro q R _ hq U ⟨x⟩
  have f : U ⟶ Spec (CommRingCat.of R) := x
  have h1 := hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have h2 := h1.map f.appTop.hom
  simpa using h2

theorem pull_cast' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast', (hA q).2.1 f hE]
  | succ k ih =>
    show pull _ f _ _ ((cup q (cpow q x k) x).cast (by push_cast; ring) (by push_cast; ring)) =
      (cup q (cpow q (pull _ f _ _ x) k) (pull _ f _ _ x)).cast (by push_cast; ring) (by push_cast; ring)
    rw [pull_cast', (hA q).1, ih]

theorem LeafPB_of' (hGeo : LeafGeo) (hCmp : LeafPBCmp) : LeafPB := by
  have hInv := leafPBInvSp
  intro hA1 hA6 hD1 q _ N R _ hq n i
  obtain ⟨V, e, h1, h2, h3⟩ := hCmp hA1 q N R hq
  have hD := hD1 q V (hInv q R hq) n i
  have hPR : Inv q (PR N 0 R) := hGeo.2.1 q N 0 R hq
  refine (Function.Bijective.of_comp_iff' (h3 i n) _).1 ?_
  convert hD using 1
  funext a
  simp only [Function.comp_apply, poly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast', (hA6 q).1, pull_cpow' hA6 q e hPR, ← pull_comp, h1, hyp, (hA6 q).2.2.1 e _ hPR, h2]

theorem LeafPB_of (hGeo : LeafGeo) (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPB :=
  LeafPB_of' hGeo (leafPBCmp_of hMap hAff)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdHocPfX
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem sq (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (f : E' ⟶ E)
    (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X) (h : f ≫ π = π') {n m i k : ℤ} (x : Ht q E n i) (b : Hs q (opn U) m k) :
    Hs.pull q (abvRel U f π' π h) _ _ (Hs.act q (P := abv U π) x (Hs.pull q (abvMap U π) _ _ b)) =
      Hs.act q (P := abv U π') (pull _ f _ _ x) (Hs.pull q (abvMap U π') _ _ b) := by
  have e := AN a6 q _ _ (abvRel U f π' π h) n m i k x (Hs.pull q (abvMap U π) _ _ b)
  rw [← hs_pull_comp, abvRel_abvMap] at e
  exact e

theorem prd_sum (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (U : X.Opens) {A : Type} (E : A → PSh) (P : PSh) (g : ∀ a, E a ⟶ P) (t : IsColimit (Cofan.mk P g))
    (π : P ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X) (h : ∀ a, g a ≫ π = π' a) {m k : ℤ} (b : Hs q (opn U) m k)
    (hb : ∀ a, Prd q U (E := disc.obj (E a)) (disc.map (π' a)) b) :
    Prd q U (E := disc.obj P) (disc.map π) b := by
  intro n i
  have h' : ∀ a, disc.map ((Cofan.mk P g).inj a) ≫ disc.map π = disc.map (π' a) := fun a => by
    rw [← disc.map_comp]; exact congrArg disc.map (h a)
  have tS : IsColimit (Cofan.mk (disc.obj P) fun a => disc.map (g a)) := isColimitCofanMkObjOfIsColimit disc E g t
  have hΦ := S (ZMod q) (tw q i) A (fun a => disc.obj (E a)) _ ⟨tS⟩ n
  have hΨ := HS q X U A E (Cofan.mk P g) ⟨t⟩ π π' h' (n + m) (i + k)
  have hP : Function.Bijective (Pi.map fun a (x : Ht q (disc.obj (E a)) n i) =>
      Hs.act q (P := abv U (disc.map (π' a))) x (Hs.pull q (abvMap U (disc.map (π' a))) _ _ b)) :=
    Function.Bijective.piMap fun a => hb a n i
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  convert hP.comp hΦ using 1
  all_goals try rfl
  funext x
  funext a
  exact sq AN a6 q U _ _ _ (h' a) x b

theorem inj_aug_RPrdH {J : Type} [SmallCategory J] (D : J ⥤ PSh) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc : Coc D c) (N : SimplexCategoryᵒᵖ) (σ : Fin (N.unop.len + 1) ⥤ J) :
    inj D N σ ≫ ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X) = c (σ.obj 0) := by
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ (σ.map (homOfLE (Fin.zero_le 0)))) U) x

theorem LeafPrdHoc_of (lvl : LeafPrdLevel) (L : LeafLevel) (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) :
    LeafPrdHoc := by
  intro hyp q _ J _ D X U c hc m k b hb
  refine lvl hyp q X U _ (aug c hc) m k b fun N => ?_
  exact prd_sum S HS AN hyp.2.2.2.2.1 q U (fun σ : Fin (N.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) ((hoc D).obj N)
    (inj D N) (L J D N).some ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X)
    (fun σ : Fin (N.unop.len + 1) ⥤ J => c (σ.obj 0)) (inj_aug_RPrdH D c hc N) b
    (fun σ : Fin (N.unop.len + 1) ⥤ J => hb (σ.obj 0))

end LateralTheory.CohomologicalPurity.TubeCut
end
end

