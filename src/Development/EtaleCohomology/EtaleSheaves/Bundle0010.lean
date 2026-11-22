import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.Bundle0004

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafCover2Pf

variable (R : Type) [CommRing R]

theorem pre_eq {P Q : PSh} (G : Shv R) (φ : Q ⟶ P) (u v : (free R).obj P ⟶ G)
    (h : (free R).map φ ≫ u = (free R).map φ ≫ v) :
    (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ u.hom) =
      (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ v.hom) := by
  have k := congrArg (fun w => toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ w.hom) h
  exact (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) u.hom).trans
    (k.trans (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) v.hom).symm)

theorem gen_eq {P Q : PSh} (G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : Q ⟶ P) (a b : (freeP R).obj P ⟶ G)
    (h : (freeP R).map φ ≫ a = (freeP R).map φ ≫ b) (Y : Scheme.{0}) (y : Q.obj (op Y)) :
    a.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) := by
  have e : ((freeP R).map φ).app (op Y) (ModuleCat.freeMk (ULift.up y)) =
      ModuleCat.freeMk (ULift.up (φ.app _ y)) := by
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have h3 := congrArg (fun w => w (ModuleCat.freeMk (ULift.up y)))
    (congrArg (fun t => ConcreteCategory.hom t) (NatTrans.congr_app h (op Y)))
  simp only [NatTrans.comp_app] at h3
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e] at h3
  exact h3

theorem loc_eq {P : PSh} (G : Shv R) (a b : (freeP R).obj P ⟶ G.obj) (X : Scheme.{0}) (x : P.obj (op X))
    (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X)
    (h : ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
      a.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x)))) :
    a.app (op X) (ModuleCat.freeMk (ULift.up x)) = b.app (op X) (ModuleCat.freeMk (ULift.up x)) := by
  have key : ∀ (c : (freeP R).obj P ⟶ G.obj) (Y : Scheme.{0}) (k : Y ⟶ X),
      G.obj.map k.op (c.app (op X) (ModuleCat.freeMk (ULift.up x))) = c.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) := by
    intro c Y k
    have n1 := ConcreteCategory.congr_hom (c.naturality k.op) (ModuleCat.freeMk (ULift.up x))
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
    rw [← n1]
    congr 1
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have hE := Presheaf.IsSheaf.hom_ext G.2 ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (a.app (op X) (ModuleCat.freeMk (ULift.up x)))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (b.app (op X) (ModuleCat.freeMk (ULift.up x))))) (by
      intro I
      ext1
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      erw [key a, key b]
      exact h _ _ I.hf)
  have := ConcreteCategory.congr_hom hE (1 : ULift R)
  simpa using this

theorem LeafCover2_of : LateralTheory.E.D2.LeafCover2 := by
  intro R _ U V E f g hf hg hc
  refine ⟨hf, hg, fun n => ⟨fun {G} u v huv => ?_⟩⟩
  induction n using Opposite.rec with | op n => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = SimplexCategory.mk m := ⟨n.len, rfl⟩
  have h1 : (free R).map (f.app _) ≫ u = (free R).map (f.app _) ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have h2 : (free R).map (g.app _) ≫ u = (free R).map (g.app _) ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  have p1 := pre_eq R G _ u v h1
  have p2 := pre_eq R G _ u v h2
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (P := (freeP R).obj (E.obj (op (SimplexCategory.mk m)))) _ _ _ G.2 ?_
  apply NatTrans.ext
  funext Y
  induction Y using Opposite.rec with | op X => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  obtain ⟨S, hS, hk⟩ := hc m X x
  refine loc_eq R G _ _ X x S hS ?_
  intro Y k hk'
  rcases hk Y k hk' with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]; exact gen_eq R _ _ _ _ p1 Y y
  · rw [← hy]; exact gen_eq R _ _ _ _ p2 Y y

end LateralTheory.E.LeafCover2Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut

open LateralTheory.E.E4

def LeafMV : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens), U ⊔ V = ⊤ →
  ∀ n : ℤ, ∃ δ : H R (sch.obj (U ⊓ V).toScheme) F n →+ H R (sch.obj X) F (n + 1),
    ∀ x : H R (sch.obj X) F (n + 1),
      (pull R (sch.map U.ι) F (n + 1) x = 0 ∧ pull R (sch.map V.ι) F (n + 1) x = 0) ↔ x ∈ δ.range

def LeafCover : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ U V : C.Opens, U ⊔ V = ⊤ ∧ ∀ W ∈ ({U, V, U ⊓ V} : Set C.Opens),
    ∃ (B : Type) (_ : CommRing B) (_ : IsDedekindDomain B) (_ : Algebra Ω B) (_ : Algebra.FiniteType Ω B),
      Nonempty (W.toScheme ≅ Sp B)

def isoH (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (e : X ≅ Y) (n : ℤ) :
    H R (sch.obj Y) F n ≃ H R (sch.obj X) F n where
  toFun := pull R (sch.map e.hom) F n
  invFun := pull R (sch.map e.inv) F n
  left_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  right_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem finite_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Finite (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Finite (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Finite (H R (sch.obj V.toScheme) F (n + 1))) :
    Finite (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  let φ := (pull R (sch.map U.ι) F (n + 1)).prod (pull R (sch.map V.ι) F (n + 1))
  have hker : φ.ker = δ.range := by
    ext x
    rw [← hδ x, AddMonoidHom.mem_ker]
    simp [φ, Prod.ext_iff]
  have : Finite φ.ker := by
    rw [hker]
    exact Set.finite_range δ |>.to_subtype
  have : Finite (H R (sch.obj X) F (n + 1) ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_addSubgroup_quotient φ.ker

theorem subsingleton_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Subsingleton (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Subsingleton (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Subsingleton (H R (sch.obj V.toScheme) F (n + 1))) :
    Subsingleton (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj X) F (n + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hδ z).1 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

theorem goal_of (hH0 : H0TwistOverClosedField) (hMV : LeafMV) (hCov : LeafCover) : LeafCurve := by
  intro hH q _ Ω _ _ hq i hB C c hc
  have hC2 : C2 := hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, V, hUV, hW⟩ := hCov Ω c hc

  have key : ∀ W ∈ ({U, V, U ⊓ V} : Set C.Opens), ∀ m : ℤ,
      (m = 0 ∨ m = 1 → Finite (Ht q (sch.obj W.toScheme) m i)) ∧ (2 ≤ m → Subsingleton (Ht q (sch.obj W.toScheme) m i)) := by
    intro W hWm m
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := hW W hWm
    have eq := isoH (ZMod q) (tw q i) e m
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases hm with rfl | rfl
      · have h0 := hH0 hH q Ω hq i
        have := h0.1
        have hbij := h0.2 (Spec.map (CommRingCat.ofHom (algebraMap Ω B)) : Sp B ⟶ Sp Ω)
        have : Finite (Ht q (sch.obj (Sp B)) 0 i) := Finite.of_surjective _ hbij.2
        exact Finite.of_equiv _ eq
      · have := hB B
        exact Finite.of_equiv _ eq
    · have := hC2 q Ω B hq m i hm
      exact eq.symm.injective.subsingleton
  have hU : U ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  have hV : V ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  have hI : U ⊓ V ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  refine ⟨?_, ?_, ?_⟩
  · have := finite_of_mv hMV hH (ZMod q) (tw q i) C U V hUV 0 ((key _ hI 0).1 (Or.inl rfl))
      ((key _ hU 1).1 (Or.inr rfl)) ((key _ hV 1).1 (Or.inr rfl))
    simpa using this
  · have := finite_of_mv hMV hH (ZMod q) (tw q i) C U V hUV 1 ((key _ hI 1).1 (Or.inr rfl))
      (by have := (key _ hU (1 + 1)).2 (by norm_num); exact Finite.of_subsingleton)
      (by have := (key _ hV (1 + 1)).2 (by norm_num); exact Finite.of_subsingleton)
    exact this
  · intro m hm
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = k + 1 := ⟨m - 1, by ring⟩
    exact subsingleton_of_mv hMV hH (ZMod q) (tw q i) C U V hUV k ((key _ hI k).2 (by omega))
      ((key _ hU (k + 1)).2 (by omega)) ((key _ hV (k + 1)).2 (by omega))

end LateralTheory.E.E4.CurveCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDiagCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafDiagCut

def LeafConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n),
  HK.pull R φ F n x = 0 ↔ ∃ r : HK R (mappingCone φ) F n, HK.pull R (mappingCone.inr φ) F n r = x

def LeafThomRel : Prop := E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
  (W : (pullback p p).Opens), (W : Set ↥(pullback p p)) = (Set.range (pullback.diagonal p))ᶜ →
  ∃ θ : Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d),
    ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens), (U : Set X) = (Set.range x)ᶜ →
      ∃ (g : U.toScheme ⟶ W.toScheme) (hg : g ≫ W.ι = U.ι ≫ pullback.lift (p ≫ x) (𝟙 X) (by simp [hx])),
        ∀ r : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d), ∃ m : ℤ, r = m • HK.pull (ZMod q)
          (mappingCone.map ((chains _).map (sch.map U.ι)) ((chains _).map (sch.map W.ι)) ((chains _).map (sch.map g))
            ((chains _).map (sch.map (pullback.lift (p ≫ x) (𝟙 X) (by simp [hx]))))
            (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hg]))
          (tw q d) (2 * d) θ

theorem hkPull_comp {R : Type} [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem goal_of (h1 : LeafConeExact) (h2 : LeafThomRel) : E8.LeafDiag := by
  intro B q _ k _ _ hq X p _ d _
  have hcl : IsClosed (Set.range (pullback.diagonal p)) := (pullback.diagonal p).isClosedEmbedding.isClosed_range
  let W0 : (pullback p p).Opens := ⟨(Set.range (pullback.diagonal p))ᶜ, hcl.isOpen_compl⟩
  obtain ⟨θ, hθ⟩ := h2 B q k hq p d W0 rfl
  refine ⟨HK.pull (ZMod q) (mappingCone.inr ((chains _).map (sch.map W0.ι))) (tw q d) (2 * d) θ, ?_, ?_⟩
  · intro W hW
    have hWW : W = W0 := TopologicalSpace.Opens.ext hW
    subst hWW
    exact (h1 _ _ _ _ _).mpr ⟨θ, rfl⟩
  · intro x hx U hU c hc
    obtain ⟨g, hg, hr⟩ := hθ x hx U hU
    obtain ⟨r, rfl⟩ := (h1 _ _ _ _ c).mp hc
    obtain ⟨m, rfl⟩ := hr r
    refine ⟨m, ?_⟩
    rw [map_zsmul]
    congr 1
    show _ = HK.pull _ _ _ _ (HK.pull _ _ _ _ θ)
    rw [← hkPull_comp, ← hkPull_comp]
    congr 1
    simp [mappingCone.map]

end LateralTheory.E.LeafDiagCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExciseCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def relMapBC (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) {T : Scheme.{0}} (s : T ⟶ X) (i n : ℤ) :=
  relMap q (pullback.map (ι' ≫ f) s f s ι' (𝟙 T) (𝟙 X) (by simp) (by simp)) (pullback.snd ι s)
    (pullback.map (ι' ≫ f) s ι s g (𝟙 T) (𝟙 X) (by simp [w]) (by simp)) (pullback.snd f s) (by rw [pullback.lift_snd, pullback.lift_snd]) i n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

def LeafConeFive : Prop := ∀ (R : Type) [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R a F n)) → (∀ n, Function.Bijective (HK.pull R b F n)) →
  ∀ n, Function.Bijective (HK.pull R (mappingCone.map φ₁ φ₂ a b comm) F n)

def ExcisionRelationSquare : Prop := Base → ∀ (q : ℕ) [NeZero q] {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z)
  (f : X' ⟶ X) (w : ι' ≫ f = g ≫ ι) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact ι] [QuasiSeparated ι]
  [QuasiCompact ι'] [QuasiSeparated ι'], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ n,
    Function.Bijective (relMapBC q ι' ι g f w s i n)) →
  ∀ n, Function.Bijective (relMap q ι' ι g f w i n)

def LeafExciseLocal : Prop := Base → ∀ (q : ℕ) [NeZero q] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [IsProper f]
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
  IsIso (f ∣_ U) → ∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ i n : ℤ,
  Function.Bijective (relMapBC q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition s i n)

theorem goal_of (h1 : ExcisionRelationSquare) (h2 : LeafExciseLocal) : EtaleExcise := by
  intro base q _ X' X Z _ f _ ι _ hq U hU hiso n i
  exact h1 base q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition hq i
    (fun A _ s hA m => h2 base q f ι hq U hU hiso A s hA i m) n

end LateralTheory.E.E8.ExciseCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeoCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoCut

def FamilyV {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeoV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → FamilyV (k := k) X c0 γ1 γ2

def LeafClosed : Prop := ∀ (B : Scheme.{0}) (V : B.Opens),
  ∃ (W : Scheme.{0}) (ι : W ⟶ B), IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ

def LeafBdry : Prop := ∀ {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), IsClosedImmersion ι → IrreducibleSpace Y →
  topologicalKrullDim Y < ⊤ → (p ⁻¹' (Set.range ι)ᶜ).Nonempty →
  topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim Y

theorem goal_of (hV : LeafGeoV) (hC : LeafClosed) (hB : LeafBdry) : LateralTheory.E.E4.LeafGeo := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, hc0, hall⟩ := hV k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, f2, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨W, ι, hι, hWV⟩ := hC B V
  exact ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hι, hWV, hs, m0, m1, m2, f1, f2, dB,
    lt_of_lt_of_le (hB π ι hι irr fin (hWV ▸ ne)) dY, P0, P1, P2, w1, w2⟩

end LateralTheory.E.LeafGeoCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeomPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2

namespace LateralTheory.E.LeafGeomPf

def vec0 {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Fin (a + b) → Scheme.Γ.obj (op X) :=
  ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
    ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).1

def First {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin a => vec0 V W x (Fin.castAdd b i)) = ⊤

def Second {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X : Scheme.{0}}
    (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  Ideal.span (Set.range fun i : Fin b => vec0 V W x (Fin.natAdd a i)) = ⊤

def LeafHalf1 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₁ : Spc) (f₁ : U₁ ⟶ PB (bsumOf V W)) (p₁ : U₁ ⟶ PB V), Mono f₁ ∧
    p₁ ≫ PB.pr V = f₁ ≫ PB.pr _ ∧ p₁ ≫ PB.line V = f₁ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), First V W x → ∃ y : Sx U₁ n X, (f₁.app _).app _ y = x

def LeafHalf2 : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ (U₂ : Spc) (f₂ : U₂ ⟶ PB (bsumOf V W)) (p₂ : U₂ ⟶ PB W), Mono f₂ ∧
    p₂ ≫ PB.pr W = f₂ ≫ PB.pr _ ∧ p₂ ≫ PB.line W = f₂ ≫ PB.line _ ∧
    ∀ (n : ℕ) (X : Scheme.{0}) (x : Sx (PB (bsumOf V W)) n X), Second V W x → ∃ y : Sx U₂ n X, (f₂.app _).app _ y = x

def LeafLocal : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) (n : ℕ) (X : Scheme.{0})
  (x : Sx (PB (bsumOf V W)) n X), ∃ S : Sieve X, S ∈ Scheme.etaleTopology X ∧ ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
    First V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) ∨
    Second V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) (hL : LeafLocal) : LateralTheory.E.D2.LeafGeom := by
  intro E a b V W
  obtain ⟨U₁, f₁, p₁, m₁, e₁, l₁, s₁⟩ := h1 V W
  obtain ⟨U₂, f₂, p₂, m₂, e₂, l₂, s₂⟩ := h2 V W
  refine ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, ?_, e₁, l₁, e₂, l₂⟩
  intro n X x
  obtain ⟨S, hS, hk⟩ := hL V W n X x
  refine ⟨S, hS, fun Y k hk' => ?_⟩
  rcases hk Y k hk' with h | h
  · exact Or.inl (s₁ n Y _ h)
  · exact Or.inr (s₂ n Y _ h)

end LateralTheory.E.LeafGeomPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostCut
open LateralTheory.E.E4

def rmap (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) : mappingCone ((chains R).map f') ⟶ mappingCone ((chains R).map f) :=
  mappingCone.map _ _ ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])

abbrev fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

abbrev rpull (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) : Hrel R f F n →+ Hrel R f' F n :=
  HK.pull R (rmap R f f' u e comm) F n

abbrev rpl (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (n : ℤ) : Hrel (ZMod q) (sch.map f) (tw q i) n →+ Hrel (ZMod q) (sch.map f') (tw q i) n :=
  rpull (ZMod q) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (tw q i) n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def LeafRelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def LeafGhostRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (y : Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n),
    ∃ c : Hrel (ZMod q) (sch.map ι) (tw q i) n,
      rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y =
        rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p) pullback.condition n c

open CochainComplex.HomComplex in
theorem relExact : LeafRelExact := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    simp [zcomp]
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp [zcomp]

open CochainComplex.HomComplex in
theorem relNat : LeafRelNat := by
  intro R _ F U E U' E' f f' u e comm n y
  have key : mappingCone.inr ((chains R).map f') ≫ rmap R f f' u e comm =
      (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [rmap, mappingCone.map]
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, key, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

theorem goal_of_all (hEx : LeafRelExact) (hNat : LeafRelNat) (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n a ha
  obtain ⟨y, rfl⟩ := hEx (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) n a ha
  obtain ⟨c, hc⟩ := hCore hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA n y
  refine ⟨fgt (ZMod q) (sch.map ι) (tw q i) n c, ?_⟩
  have e1 := hNat (ZMod q) (tw q i) (sch.map ι) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.snd (g2 ≫ g1 ≫ p) ι)) (sch.map (g2 ≫ g1 ≫ p))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]) n c
  have hsq : pullback.fst (g2 ≫ g1 ≫ p) ι ≫ (g2 ≫ g1) =
      pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm
  have e2 := hNat (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp))) (sch.map (g2 ≫ g1))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hsq]) n y
  change pull _ _ _ _ _ = pull _ _ _ _ _
  rw [← e1, ← e2]
  exact congrArg _ hc.symm

theorem goal_of (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := goal_of_all relExact relNat hCore

end LateralTheory.E.LeafGhostCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLevelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafLevelPf

abbrev cone0 (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) : Cx R :=
  mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g))

def LeafDisc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (g : P ⟶ Q) (n : ℤ),
  Subsingleton (HK R (mappingCone ((chains R).map (disc.map g))) F n) → Subsingleton (HK R (cone0 R g) F n)

def LeafFilt : Prop := GlobalTheory.EtC.A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E'),
  (∀ p : ℕ, ∀ n : ℤ, n < c - p → Subsingleton (HK R (cone0 R (f.app (op (SimplexCategory.mk p)))) F n)) →
  ∀ n : ℤ, n < c → Subsingleton (HK R (mappingCone ((chains R).map f)) F n)

theorem LeafLevel_of (hRel : LateralTheory.E.t_E6Cut.LeafRel) (hD : LeafDisc) (hF : LeafFilt) :
    LateralTheory.E.t_E6Cut.LeafLevel := by
  intro hA1 R _ F c E E' f h
  unfold LateralTheory.E.t_E6Cut.Conn
  rw [hRel R F c]
  apply hF hA1 R F c f
  intro p n hn
  apply hD R F _ n
  have hp := h p
  unfold LateralTheory.E.t_E6Cut.Conn at hp
  rw [hRel R F (c - p)] at hp
  exact hp n hn

end LateralTheory.E.LeafLevelPf
end
end

