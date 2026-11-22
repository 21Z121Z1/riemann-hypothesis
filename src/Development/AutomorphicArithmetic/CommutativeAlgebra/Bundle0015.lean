import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0011
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c c' : ℤ} (h : c' ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F c' f :=
  fun n => ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

private theorem conn_square {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {E₁ E₂ E₃ E₄ : Spc} {u : E₁ ⟶ E₂}
    {v : E₃ ⟶ E₄} {a : E₁ ⟶ E₃} {b : E₂ ⟶ E₄} (w : u ≫ b = a ≫ v) (ha : Eqv R a F) (hb : Eqv R b F)
    (hu : Conn R F c u) : Conn R F c v := by
  have key : ∀ (n : ℤ) (x : H R E₄ F n), pull R a F n (pull R v F n x) = pull R u F n (pull R b F n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, w]
  have inj : ∀ n : ℤ, Function.Injective (pull R u F n) → Function.Injective (pull R v F n) := by
    intro n hi x y h
    exact (hb n).1 (hi ((key n x).symm.trans ((congrArg _ h).trans (key n y))))
  have sur : ∀ n : ℤ, Function.Surjective (pull R u F n) → Function.Surjective (pull R v F n) := by
    intro n hs y
    obtain ⟨z, hz⟩ := hs (pull R a F n y)
    obtain ⟨x, rfl⟩ := (hb n).2 z
    exact ⟨x, (ha n).1 ((key n x).trans hz)⟩
  intro n
  exact ⟨fun hn => ⟨inj n ((hu n).1 hn).1, sur n ((hu n).1 hn).2⟩, fun hn => inj n ((hu n).2 hn)⟩

private theorem eqv_of_iso {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

private theorem conn_level {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {P Q : PSh} (ψ : P ⟶ Q) {Z Z' : Scheme.{0}}
    (k : Z' ⟶ Z) (e : yoneda.obj Z ≅ Q) (e' : yoneda.obj Z' ≅ P) (h : e'.hom ≫ ψ = yoneda.map k ≫ e.hom)
    (hk : Conn R F c (sch.map k)) : Conn R F c (disc.map ψ) := by
  refine conn_square (u := sch.map k) (a := (disc.mapIso e').hom) (b := (disc.mapIso e).hom) ?_
    (eqv_of_iso _) (eqv_of_iso _) hk
  change disc.map (yoneda.map k) ≫ disc.map e.hom = disc.map e'.hom ≫ disc.map ψ
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem cech_zero {V Y : Scheme.{0}} (f : V ⟶ Y) :
    ∃ e : yoneda.obj V ≅ (cech f).obj (op (SimplexCategory.mk 0)),
      e.hom ≫ (cechAug f).app (op (SimplexCategory.mk 0)) = yoneda.map f := by
  let π₀ : Fin 1 → (yoneda.obj V ⟶ yoneda.obj Y) := fun _ => yoneda.map f
  let h : yoneda.obj V ⟶ widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ :=
    WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  let k : widePullback (yoneda.obj Y) (fun _ : Fin 1 => yoneda.obj V) π₀ ⟶ yoneda.obj V :=
    WidePullback.π π₀ 0
  have hk : h ≫ k = 𝟙 _ := WidePullback.lift_π _ _ _ _ _
  have hb : h ≫ WidePullback.base π₀ = yoneda.map f := WidePullback.lift_base _ _ _ _
  have kh : k ≫ h = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [Category.assoc, Category.id_comp]
      change k ≫ h ≫ k = k
      rw [hk, Category.comp_id]
    · rw [Category.assoc, hb, Category.id_comp]
      exact WidePullback.π_arrow π₀ 0
  exact ⟨⟨h, k, hk, kh⟩, hb⟩

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_cover {V Y : Scheme.{0}} (f : V ⟶ Y)
    (hcov : ∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) :
    Smooth f := by
  obtain ⟨ι, O, j, hj, -, hc, hf⟩ := hcov
  let 𝒰 : V.OpenCover := Scheme.Cover.mkOfCovers ι O j (fun y => by
    obtain ⟨a, x, hx⟩ := hc y
    exact ⟨a, x, hx⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun a => ?_
  have := hf a
  change Smooth (j a ≫ f)
  infer_instance

theorem UpperTheory.connectivity_of_cech_disjoint_cover :
    LeafLevel → A1 → A2 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {V Y : Scheme.{0}} (f : V ⟶ Y) [Surjective f], (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ V), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : V, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ f)) → ∀ W : Y.Opens,
      Conn R F c (sch.map (f ⁻¹ᵁ W).ι) → (∀ (Z : Scheme.{0}) (g : Z ⟶ Y), (∃ (ι : Type) (O : ι → Scheme.{0}) (j : ∀ a, O a ⟶ Z), (∀ a, IsOpenImmersion (j a)) ∧ (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) ∧ (∀ y : Z, ∃ a, y ∈ Set.range (j a)) ∧ ∀ a, IsOpenImmersion (j a ≫ g)) → Conn R F (c - 1) (sch.map (g ⁻¹ᵁ W).ι)) → Conn R F c (sch.map W.ι) := by
  intro hL a1 a2 R _ F c V Y f _ hcov W h0 hp
  obtain ⟨ψ, hψ, hlev⟩ := UpperTheory.cech_nerve_restrict_open f W
  have hsm : Smooth f := smooth_of_cover f hcov
  have hsmW : Smooth (f ∣_ W) := MorphismProperty.of_isPullback (P := @Smooth) (isPullback_morphismRestrict f W).flip hsm
  have hsuW : Surjective (f ∣_ W) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict f W).flip inferInstance
  have eV := a2 R f F
  have eW := a2 R (f ∣_ W) F
  have hψc : Conn R F c ψ := by
    refine hL a1 R F c ψ fun p => ?_
    rcases p with _ | p
    · obtain ⟨e, he⟩ := cech_zero f
      obtain ⟨e', he'⟩ := hlev 0 V f e he
      have h0' : Conn R F (c - ((0 : ℕ) : ℤ)) (sch.map (f ⁻¹ᵁ W).ι) := by simpa using h0
      exact conn_level _ _ e e' he' h0'
    · obtain ⟨Z, g, e, hg, hc⟩ := UpperTheory.cech_nerve_representable_disjoint f hcov (p + 1)
      obtain ⟨e', he'⟩ := hlev (p + 1) Z g e hg
      exact conn_level _ _ e e' he' (conn_mono (by push_cast; omega) (hp Z g hc))
  exact conn_square hψ eW eV hψc

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EquivOfConstantSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.SimplicialRelations
open SimplicialObject Simplicial

private theorem qi_of_ed (R : Type) [CommRing R] (A : SimplicialObject.Augmented PSh)
    (ed : Augmented.ExtraDegeneracy A) :
    QuasiIso ((chainsN R).map (X := A.left) (Y := disc.obj A.right) A.hom) := by
  let W := (Augmented.whiskering PSh (Shv R)).obj (free R)
  let φ : A ⟶ Augmented.const.obj A.right :=
    { left := A.hom, right := 𝟙 _, w := by
        change A.hom ≫ 𝟙 _ = A.hom ≫ (SimplicialObject.const PSh).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id] }
  have h1 := (ed.map (free R)).homotopyEquiv.quasiIso_hom
  have h2 := ((Augmented.ExtraDegeneracy.const A.right).map (free R)).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (W.map φ)
  have hp : (Augmented.point ⋙ ChainComplex.single₀ _).map (W.map φ) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map ((free R).map (𝟙 A.right)) = 𝟙 _
    rw [(free R).map_id, CategoryTheory.Functor.map_id]
  rw [hp] at nat
  have nat' := nat.trans (Category.comp_id (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj A)))
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj (Augmented.const.obj A.right))) := h2
  have key : QuasiIso ((Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (W.map φ) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app (W.obj (Augmented.const.obj A.right))) := by
    rw [nat']; exact h1
  exact (quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (W.obj (Augmented.const.obj A.right)))).1 key

variable {X M : RF} (ρ : X.Hom M) (hc : ρ.Const)
  (hr : ∀ {A : Type} [CommRing A] {x y : X.obj A}, ρ.app A x = ρ.app A y → X.rel x y)
  (γ : M.Hom X) (hγ : ∀ {A : Type} [CommRing A] (m : M.obj A), ρ.app A (γ.app A m) = m)

include hc in
private theorem ρ_eq {A : Type} [CommRing A] {n : ℕ} {x : Fin n → X.obj A} (hx : ∀ i j, X.rel (x i) (x j)) (i j : Fin n) :
    ρ.app A (x i) = ρ.app A (x j) := hc (hx i j)

private def sv {A : Type} [CommRing A] {n : ℕ} (x : Fin (n + 1) → X.obj A) : Fin (n + 2) → X.obj A :=
  Fin.cons (γ.app A (ρ.app A (x 0))) x

include hc hr hγ in
private theorem sv_rel {A : Type} [CommRing A] {n : ℕ} {x : Fin (n + 1) → X.obj A} (hx : ∀ i j, X.rel (x i) (x j))
    (i j : Fin (n + 2)) : X.rel (sv ρ γ x i) (sv ρ γ x j) := by
  have key : ∀ k, ρ.app A (sv ρ γ x k) = ρ.app A (x 0) := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [sv, hγ]
    · simpa [sv] using ρ_eq ρ hc hx k 0
  exact hr ((key i).trans (key j).symm)

private theorem sv_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (x : Fin (n + 1) → X.obj A) :
    sv ρ γ (fun i => X.map f (x i)) = fun i => X.map f (sv ρ γ x i) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [sv, ρ.nat, γ.nat]
  · simp [sv]

include hc in
private theorem sv_δ {A : Type} [CommRing A] {n : ℕ} {x : Fin (n + 2) → X.obj A} (hx : ∀ i j, X.rel (x i) (x j))
    (i j : Fin (n + 2)) : sv ρ γ x (i.succ.succAbove j) = sv ρ γ (fun k => x (i.succAbove k)) j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Fin.succ_succAbove_zero]
    simp only [sv, Fin.cons_zero]
    rw [ρ_eq ρ hc hx 0 (i.succAbove 0)]
  · rw [Fin.succ_succAbove_succ]
    simp [sv]

include hc in
private theorem sv_σ {A : Type} [CommRing A] {n : ℕ} (x : Fin (n + 1) → X.obj A) (i : Fin (n + 1)) (j : Fin (n + 3)) :
    sv ρ γ x (Fin.predAbove i.succ j) = sv ρ γ (fun k => x (Fin.predAbove i k)) j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · have h0 : Fin.predAbove i.succ (0 : Fin (n + 3)) = 0 := by
      simp [Fin.predAbove]
    have h1 : Fin.predAbove i (0 : Fin (n + 2)) = 0 := by
      simp [Fin.predAbove]
    rw [h0]
    simp [sv, h1]
  · rw [Fin.succ_predAbove_succ]
    simp [sv]

private def augOf : SimplicialObject.Augmented PSh :=
  { left := CN X, right := M.psh, hom := CN.proj ρ hc }

private def sZ (hr' : ∀ {A : Type} [CommRing A] (x : X.obj A), X.rel x x) : M.psh ⟶ (CN X).obj (op (SimplexCategory.mk 0)) where
  app U := TypeCat.ofHom fun (m : M.obj Γ(U.unop, ⊤)) => ⟨fun _ => γ.app _ m, fun _ _ => hr' _⟩
  naturality U V f := by
    refine ConcreteCategory.hom_ext _ _ fun m => Subtype.ext (funext fun _ => ?_)
    exact γ.nat f.unop.appTop.hom m

include hc hr hγ in
private def sN (n : ℕ) : (CN X).obj (op (SimplexCategory.mk n)) ⟶ (CN X).obj (op (SimplexCategory.mk (n + 1))) where
  app U := TypeCat.ofHom fun (x : {x : Fin (n + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}) =>
    ⟨sv ρ γ x.1, sv_rel ρ hc hr γ hγ x.2⟩
  naturality U V f := by
    refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
    exact sv_map ρ γ f.unop.appTop.hom x.1

include hr hγ in
private def edOf : Augmented.ExtraDegeneracy (augOf ρ hc) where
  s' := sZ γ (fun _ => hr rfl)
  s n := sN ρ hc hr γ hγ n
  s'_comp_ε := by
    ext U m
    exact hγ m
  s₀_comp_δ₁ := by
    ext U x
    refine Subtype.ext (funext fun (i : Fin 1) => ?_)
    have : i = 0 := Subsingleton.elim _ _
    subst this
    rfl
  s_comp_δ₀ n := by
    ext U x
    refine Subtype.ext (funext fun i => ?_)
    change sv ρ γ x.1 (Fin.succAbove 0 i) = x.1 i
    simp [sv]
  s_comp_δ n i := by
    ext U x
    refine Subtype.ext (funext fun j => ?_)
    exact sv_δ ρ hc γ x.2 i j
  s_comp_σ n i := by
    ext U x
    refine Subtype.ext (funext fun j => ?_)
    exact sv_σ ρ hc γ x.1 i j

end UpperTheory.SimplicialRelations

theorem UpperTheory.equiv_of_constant_section :
    A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {X M : RF} (ρ : X.Hom M) (hc : ρ.Const), (∀ {A : Type} [CommRing A] {x y : X.obj A}, ρ.app A x = ρ.app A y → X.rel x y) → ∀ γ : M.Hom X, (∀ {A : Type} [CommRing A] (m : M.obj A), ρ.app A (γ.app A m) = m) → Eqv R (CN.proj ρ hc) F := by
  intro hA R _ F X M ρ hc hr γ hγ n
  have q : QuasiIso ((chainsN R).map (CN.proj ρ hc)) :=
    UpperTheory.SimplicialRelations.qi_of_ed R (UpperTheory.SimplicialRelations.augOf ρ hc) (UpperTheory.SimplicialRelations.edOf ρ hc hr γ hγ)
  have q2 : QuasiIso ((chains R).map (CN.proj ρ hc)) := by
    change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map (CN.proj ρ hc)) ComplexShape.embeddingDownNat)
    infer_instance
  exact hA R ((chains R).map (CN.proj ρ hc)) F n
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteExtPullbackIntegralClosureEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.PullbackAlongInclusion

section
variable (A K L : Type) [CommRing A] [Field K] [Algebra A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

private abbrev Idx : Type := {E : IntermediateField K L // FiniteDimensional K E}

omit [Algebra A K] in
private theorem idx_directed : IsDirected (Idx K L) (· ≤ ·) :=
  ⟨fun a b => by
    haveI := a.2
    haveI := b.2
    exact ⟨⟨a.1 ⊔ b.1, inferInstance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

private noncomputable def incl {E F : IntermediateField K L} (h : E ≤ F) :
    integralClosure A E →ₐ[A] integralClosure A F :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

private noncomputable def toL (E : IntermediateField K L) :
    integralClosure A E →ₐ[A] integralClosure A L :=
  (E.val.restrictScalars A).mapIntegralClosure

private noncomputable def ringD : Idx K L ⥤ CommRingCat.{0} where
  obj E := CommRingCat.of (integralClosure A E.1)
  map f := CommRingCat.ofHom (incl A K L (leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def ringC : Cocone (ringD A K L) where
  pt := CommRingCat.of (integralClosure A L)
  ι := { app := fun E => CommRingCat.ofHom (toL A K L E.1).toRingHom
         naturality := fun _ _ _ => by ext; rfl }

private theorem ringC_isColimit [Algebra.IsAlgebraic K L] : Nonempty (IsColimit (ringC A K L)) := by
  haveI := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := inferInstance
  haveI : ReflectsColimitsOfShape (Idx K L) (forget CommRingCat) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    have hx : IsIntegral K (x.1 : L) := Algebra.IsIntegral.isIntegral _
    let E : Idx K L := ⟨IntermediateField.adjoin K {x.1}, IntermediateField.adjoin.finiteDimensional hx⟩
    have hm : x.1 ∈ E.1 := IntermediateField.mem_adjoin_simple_self K x.1
    have hi : IsIntegral A (⟨x.1, hm⟩ : E.1) :=
      (isIntegral_algHom_iff (E.1.val.restrictScalars A) E.1.val.toRingHom.injective).1 x.2
    exact ⟨E, ⟨⟨x.1, hm⟩, hi⟩, rfl⟩
  · intro a b xa xb h
    haveI := a.2
    haveI := b.2
    refine ⟨⟨a.1 ⊔ b.1, inferInstance⟩, homOfLE (le_sup_left (a := a.1)),
      homOfLE (le_sup_right (b := b.1)), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integralClosure A L => (z : L)) h

omit [Algebra A K] [IsScalarTower A K L] [Field K] [Algebra K L] in
private theorem aic [IsAlgClosed L] : AIC (integralClosure A L) := by
  intro p hp hdeg
  have hd : (p.map (algebraMap (integralClosure A L) L)).degree ≠ 0 := by
    rw [hp.degree_map]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral (integralClosure A L) a := ⟨p, hp, by rw [← Polynomial.eval_map]; exact ha⟩
  have hA : IsIntegral A a := isIntegral_trans a hint
  refine ⟨⟨a, hA⟩, ?_⟩
  have h2 : algebraMap (integralClosure A L) L (Polynomial.eval ⟨a, hA⟩ p) = 0 := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact ha
  exact Subtype.ext h2

end

private theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

private theorem pull_of_comp (q : ℕ) (m i : ℤ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (e : g.comp f = h) (x : Ht q (sp R) m i) :
    pull _ (spMap g) _ m (pull _ (spMap f) _ m x) = pull _ (spMap h) _ m x := by
  rw [← pull_comp, spMap_comp, e]

end UpperTheory.PullbackAlongInclusion

open UpperTheory.PullbackAlongInclusion in
theorem UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero :
    Hyps → ∀ (q : ℕ) [NeZero q] (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
        [IsFractionRing A K], IsUnit (q : A) → ∀ (m i : ℤ), 0 < m → ∀ x : Ht q (sp A) m i,
        ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F) (_ : IsScalarTower A K F) (_ : FiniteDimensional K F),
          pull _ (spMap (algebraMap A (integralClosure A F))) _ m x = 0 := by
  intro h q _ A K _ _ _ _ _ hq m i hm x
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB1, -, -, -, hB5, -⟩ := h
  let L := AlgebraicClosure K
  haveI : IsDirected (Idx K L) (· ≤ ·) := idx_directed K L
  haveI : Nonempty (Idx K L) := ⟨⟨⊥, inferInstance⟩⟩
  haveI : IsFiltered (Idx K L) := isFiltered_of_directed_le_nonempty _
  obtain ⟨hc⟩ := ringC_isColimit A K L
  let j0 : Idx K L := ⟨⊥, inferInstance⟩
  have hqE : ∀ E : IntermediateField K L, IsUnit ((q : integralClosure A E)) := fun E => by
    simpa using hq.map (algebraMap A (integralClosure A E))
  have hqL : IsUnit ((q : integralClosure A L)) := by
    simpa using hq.map (algebraMap A (integralClosure A L))
  have e1 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1)) (toL A K L j0.1).toRingHom
    (algebraMap A (integralClosure A L)) (toL A K L j0.1).comp_algebraMap x
  haveI := hB5 q (integralClosure A L) (aic A L) hqL m i hm
  have hzero : pull _ (spMap ((ringC A K L).ι.app j0).hom) _ m
      (pull _ (spMap (algebraMap A (integralClosure A j0.1))) _ m x) = 0 :=
    e1.trans (Subsingleton.elim _ _)
  obtain ⟨k, f, hk⟩ := (hB1 q (ringD A K L) (ringC A K L) hc m i).2 j0 _ (hqE _) hzero
  refine ⟨k.1, inferInstance, inferInstance, inferInstance, inferInstance, k.2, ?_⟩
  have e2 := pull_of_comp q m i (algebraMap A (integralClosure A j0.1))
    (incl A K L (leOfHom f)).toRingHom (algebraMap A (integralClosure A k.1))
    (incl A K L (leOfHom f)).comp_algebraMap x
  exact e2.symm.trans hk
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteSpanKummerSelmerRepresentatives
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : divisor (x ^ n) = n • (divisor x : Divisor k K) := by
  induction n with
  | zero => simp [divisor_one]
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

theorem UpperTheory.exists_finite_span_kummerSelmer_representatives :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], ∃ (n : ℕ) (v : Fin n → K), ∀ f ∈ SelAll k K q, ∃ g ∈ SelAll k K q, (∃ c : Fin n → k, (g : K) = ∑ i, c i • v i) ∧ ∃ u : Kˣ, f = g * u ^ q := by
  intro k K _ _ _ _ _ q _
  have hcl : algebraicClosure k K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_algebraicClosure_iff] at hz
    rw [IntermediateField.mem_bot]
    exact minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz.isIntegral))
  obtain ⟨x, hxt, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K := Module.finrank_pos
  set E : Divisor k K := genus k K • poleDivisor x with hE
  have hdegE : (genus k K : ℤ) ≤ Divisor.deg E := by
    rw [hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]
    have h1 : (1 : ℤ) ≤ (Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K : ℤ) := by
      exact_mod_cast hd
    have h2 : (0 : ℤ) ≤ (genus k K : ℤ) := by positivity
    nlinarith
  set V := (q • E).L with hV
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun i => (b i : K), ?_⟩
  intro f hf
  have hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K) := hf
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  let D : Divisor k K := Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))
  have hD : divisor (f : K) = q • D := by
    ext w
    simp only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel', divisor_apply]
    rw [divisor_apply]
    exact hf' w
  have hdegD : Divisor.deg D = 0 := by
    have h0 := Divisor.deg_divisor (k := k) (f : K)
    rw [hD, map_nsmul, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq
    · exact h
  have hri := Divisor.riemann_inequality hcl (D + E)
  rw [map_add, hdegD, zero_add] at hri
  have hpos : 0 < Module.finrank k (D + E).L := by omega
  obtain ⟨⟨h, hmem⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hh : h ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hle := (Divisor.mem_L_iff_le hh).mp hmem
  let u : Kˣ := Units.mk0 h hh
  have hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q := by simp [u]
  have hgne : ((f * u ^ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h) := by
    rw [hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]
  have hgV : ((f * u ^ q : Kˣ) : K) ∈ V := by
    rw [hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]
    have h3 : D + divisor h + E = divisor h + (D + E) := by abel
    rw [h3]
    exact nsmul_nonneg hle q
  refine ⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩
  · intro w
    rw [← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · refine ⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩
    have hs := b.sum_repr ⟨_, hgV⟩
    have hs' := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs'
    exact hs'.symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSubalgebraEqRangeGermToFunctionField
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HypercohomologyPostClEqClComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
end

