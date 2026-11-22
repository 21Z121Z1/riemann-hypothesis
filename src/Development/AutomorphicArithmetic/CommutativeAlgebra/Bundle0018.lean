import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.InverseDerivation

variable {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) (A : CommRingCat.{0})

private abbrev BD : Prop :=
  Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))

private abbrev BG : Prop :=
  Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))

variable {ρ σ A}

private noncomputable def invD (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : a.D.obj A :=
  (Equiv.ofBijective _ hd).symm p

private noncomputable def invG (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : a.G.obj A :=
  (Equiv.ofBijective _ hg).symm p

private theorem invD_fst (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : ρ.d.app A (invD hd p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invD_snd (hd : BD ρ σ A) (p : b.D.obj A × c.D.obj A) : σ.d.app A (invD hd p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hd p)

private theorem invG_fst (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : ρ.g.app A (invG hg p) = p.1 := by
  exact congrArg Prod.fst (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invG_snd (hg : BG ρ σ A) (p : b.G.obj A × c.G.obj A) : σ.g.app A (invG hg p) = p.2 := by
  exact congrArg Prod.snd (Equiv.ofBijective_apply_symm_apply _ hg p)

private theorem invD_eq (hd : BD ρ σ A) {x : a.D.obj A} {p : b.D.obj A × c.D.obj A}
    (h1 : ρ.d.app A x = p.1) (h2 : σ.d.app A x = p.2) : invD hd p = x := by
  apply hd.1
  refine (Equiv.ofBijective_apply_symm_apply _ hd p).trans ?_
  exact Prod.ext h1.symm h2.symm

private theorem invG_eq (hg : BG ρ σ A) {x : a.G.obj A} {p : b.G.obj A × c.G.obj A}
    (h1 : ρ.g.app A x = p.1) (h2 : σ.g.app A x = p.2) : invG hg p = x := by
  apply hg.1
  refine (Equiv.ofBijective_apply_symm_apply _ hg p).trans ?_
  exact Prod.ext h1.symm h2.symm

private noncomputable def lift (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) : J ⥤ Ob a A where
  obj j := ⟨invD hd ((y.obj j).pt, (z.obj j).pt)⟩
  map {i j} f := ⟨invG hg ((y.map f).1, (z.map f).1), by
    refine hd.1 (Prod.ext ?_ ?_)
    · change ρ.d.app A _ = ρ.d.app A (a.smul A _ _)
      rw [ρ.eq, invD_fst, invD_fst, invG_fst]
      exact (y.map f).2
    · change σ.d.app A _ = σ.d.app A (a.smul A _ _)
      rw [σ.eq, invD_snd, invD_snd, invG_snd]
      exact (z.map f).2⟩
  map_id j := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A 1 = (y.map (𝟙 j)).1
      rw [y.map_id]
      exact map_one (ρ.g.app A).hom
    · change σ.g.app A 1 = (z.map (𝟙 j)).1
      rw [z.map_id]
      exact map_one (σ.g.app A).hom
  map_comp {i j l} f g := by
    refine Subtype.ext (invG_eq hg ?_ ?_)
    · change ρ.g.app A (invG hg _ * invG hg _) = (y.map (f ≫ g)).1
      rw [y.map_comp]
      refine (map_mul (ρ.g.app A).hom _ _).trans ?_
      change ρ.g.app A _ * ρ.g.app A _ = _
      rw [invG_fst, invG_fst]
      rfl
    · change σ.g.app A (invG hg _ * invG hg _) = (z.map (f ≫ g)).1
      rw [z.map_comp]
      refine (map_mul (σ.g.app A).hom _ _).trans ?_
      change σ.g.app A _ * σ.g.app A _ = _
      rw [invG_snd, invG_snd]
      rfl

private theorem lift_fst (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ ρ.fn A = y := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
    rw [invD_fst]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨ρ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob b A) = y.obj i
      rw [invD_fst]
    · change (⟨ρ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob b A) = y.obj j
      rw [invD_fst]
    · change ρ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (y.map f).1
      rw [invG_fst]

private theorem lift_snd (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (y : J ⥤ Ob b A) (z : J ⥤ Ob c A) :
    lift hd hg y z ⋙ σ.fn A = z := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
    rw [invD_snd]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨σ.d.app A (invD hd ((y.obj i).pt, (z.obj i).pt))⟩ : Ob c A) = z.obj i
      rw [invD_snd]
    · change (⟨σ.d.app A (invD hd ((y.obj j).pt, (z.obj j).pt))⟩ : Ob c A) = z.obj j
      rw [invD_snd]
    · change σ.g.app A (invG hg ((y.map f).1, (z.map f).1)) = (z.map f).1
      rw [invG_snd]

private theorem lift_comp (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] (w : J ⥤ Ob a A) :
    lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) = w := by
  refine Functor.hext (fun j => ?_) (fun i j f => ?_)
  · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
    rw [invD_eq hd rfl rfl]
  · refine Ob.hom_heq ?_ ?_ _ _ ?_
    · change (⟨invD hd (ρ.d.app A (w.obj i).pt, σ.d.app A (w.obj i).pt)⟩ : Ob a A) = w.obj i
      rw [invD_eq hd rfl rfl]
    · change (⟨invD hd (ρ.d.app A (w.obj j).pt, σ.d.app A (w.obj j).pt)⟩ : Ob a A) = w.obj j
      rw [invD_eq hd rfl rfl]
    · change invG hg (ρ.g.app A (w.map f).1, σ.g.app A (w.map f).1) = (w.map f).1
      exact invG_eq hg rfl rfl

private theorem comp_inj (hd : BD ρ σ A) (hg : BG ρ σ A)
    {J : Type} [Category.{0} J] {w w' : J ⥤ Ob a A}
    (h1 : w ⋙ ρ.fn A = w' ⋙ ρ.fn A) (h2 : w ⋙ σ.fn A = w' ⋙ σ.fn A) : w = w' := by
  calc w = lift hd hg (w ⋙ ρ.fn A) (w ⋙ σ.fn A) := (lift_comp hd hg w).symm
    _ = lift hd hg (w' ⋙ ρ.fn A) (w' ⋙ σ.fn A) := by rw [h1, h2]
    _ = w' := lift_comp hd hg w'

end UpperTheory.InverseDerivation

open UpperTheory.InverseDerivation in
theorem UpperTheory.isIso_stackProductPair_of_bijective :
    ∀ (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c),
        (∀ A, Function.Bijective (fun x : a.D.obj A => ((ρ.d.app A x, σ.d.app A x) : b.D.obj A × c.D.obj A))) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => ((ρ.g.app A g, σ.g.app A g) : b.G.obj A × c.G.obj A))) →
        IsIso (Sp.pair E ρ σ) := by
  intro E a b c ρ σ hd hg
  refine isIso_of_bijective_on_simplices _ (fun k T => ?_)
  let A : CommRingCat := Scheme.Γ.obj (op T)
  change Function.Bijective
    (fun p : (E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob a A) =>
      (((p.1, p.2 ⋙ ρ.fn A), p.2 ⋙ σ.fn A) :
        ((E.obj (op (SimplexCategory.mk k))).obj (op T) × (Fin (k+1) ⥤ Ob b A)) × (Fin (k+1) ⥤ Ob c A)))
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext h1 (comp_inj (hd A) (hg A) h2 h3)
  · refine ⟨(q.1.1, lift (hd A) (hg A) q.1.2 q.2), ?_⟩
    simp only [lift_fst, lift_snd]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MemRangeOfProperGenericFibreSeparated
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

set_option maxHeartbeats 400000 in
theorem UpperTheory.mem_range_of_proper_generic_fibre_separated :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {B Y D C : Scheme.{0}} (ι : Sp R ⟶ B) [IsOpenImmersion ι] (π : Y ⟶ B) [IsSeparated π] [IrreducibleSpace Y] (j : D ⟶ Y) [IsOpenImmersion j], Dense (Set.range j) → ∀ (q : D ⟶ Sp R), j ≫ π = q ≫ ι → ∀ (c : C ⟶ Sp Ω) [IsProper c] (v : C ⟶ D), IsPullback v c q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) → ∀ (y : Y), π y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) → y ∈ Set.range j := by
  intro R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy
  set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg
  let U' : Y.Opens := π ⁻¹ᵁ ι.opensRange
  have hjU : Set.range j ⊆ Set.range U'.ι := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    show π (j d) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let jU : D ⟶ U' := IsOpenImmersion.lift U'.ι j hjU
  have hjUf : jU ≫ U'.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let w : (U' : Scheme) ⟶ Sp R := IsOpenImmersion.lift ι (U'.ι ≫ π) hπU
  have hw : w ≫ ι = U'.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hjw : jU ≫ w = q := by
    rw [← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]
  haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance
  haveI : IsSeparated w := IsSeparated.of_comp w ι
  let m : C ⟶ pullback w g := pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])
  have hm : m ≫ pullback.snd w g = c := pullback.lift_snd _ _ _
  haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance
  haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)
  have hleft : IsPullback m v (pullback.fst w g) jU := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip
    rw [hm, hjw]
    exact hpb.flip
  have hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU :=
    (Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm
  have hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m := by
    intro z hz
    have e := IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)
    have hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU) := by
      rw [e]
      exact hz
    obtain ⟨t, rfl⟩ := hz'
    refine ⟨hleft.isoPullback.inv t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hI]
  obtain ⟨p, hp⟩ := hy
  have hyU : y ∈ U' := by
    show π y ∈ ι.opensRange
    rw [← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let yU : U' := ⟨y, hyU⟩
  have e1 : ι (w yU) = π y := by
    show (w ≫ ι) yU = π y
    rw [hw]
    rfl
  have hwy : w yU = g p := by
    apply ι.isOpenEmbedding.injective
    rw [e1, ← hp]
    rfl
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy
  have hξ : genericPoint Y ∈ Set.range j := by
    rw [(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]
    exact hd.nonempty
  obtain ⟨d, hdξ⟩ := hξ
  have hsp : jU d ⤳ yU := by
    apply (U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    have e2 : U'.ι (jU d) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, hjUf, hdξ]
    rw [e2]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', hx'sp, hx'fst⟩ := UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)
  have hx'm : x' ∈ Set.range m := hrange ⟨d, hx'fst.symm⟩
  have hy'm : y' ∈ Set.range m := hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm
  obtain ⟨c0, hc0⟩ := hy'm
  refine ⟨v c0, ?_⟩
  have h1 : pullback.fst w g (m c0) = jU (v c0) := by
    rw [← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]
  rw [← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.NerveFirstProjection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A)
    (h : Ideal.span (Set.range v) = ⊤) (a b : A) (hab : ∀ j, a * v j = b * v j) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range v) := by rw [h]; trivial
  have key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [sub_mul, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have h2 := key 1 h1
  rw [mul_one] at h2
  exact sub_eq_zero.1 h2

private theorem fam_inj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (x y : Fin (m + 1) → (L2 D d).obj A)
    (hx : ∀ i j, (L2 D d).rel (x i) (x j)) (hy : ∀ i j, (L2 D d).rel (y i) (y j))
    (h1 : ∀ i, (fstV D d).app A (x i) = (fstV D d).app A (y i))
    (h2 : (x 0).1.1.2 (Fin.last d) = (y 0).1.1.2 (Fin.last d)) : x = y := by
  have hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc :=
    fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j
  have hr : ∀ i, (x i).1.1.1 = (y i).1.1.1 := fun i => congrArg (fun z => z.1.1) (h1 i)
  refine funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))
  obtain ⟨-, u, hu⟩ := hx i 0
  obtain ⟨-, u', hu'⟩ := hy i 0
  have huu : (u : A) = u' := by
    refine unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_
    have e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc := congrFun hu _
    have e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc := congrFun hu' _
    change (u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc
    rw [← e1, hv i j, e2, hv 0 j]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d) := congrFun hu _
    have e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d) := congrFun hu' _
    change (x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)
    rw [e1, e2, huu, h2]
  · exact hv i j

private theorem fam_surj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (c : Fin (m + 1) → (Vec D d).obj A) (hc : ∀ i j, (Vec D d).rel (c i) (c j)) (t : A) :
    ∃ x : Fin (m + 1) → (L2 D d).obj A, (∀ i j, (L2 D d).rel (x i) (x j)) ∧
      (∀ i, (fstV D d).app A (x i) = c i) ∧ (x 0).1.1.2 (Fin.last d) = t := by
  have hex : ∀ i, ∃ u : Aˣ, (c i).1.2 = fun j => (u : A) * (c 0).1.2 j := fun i => (hc i 0).2
  choose u hu using hex
  have hu0 : (u 0 : A) = 1 := by
    refine unit_unique (c 0).1.2 (c 0).2 _ _ fun j => ?_
    have e : (c 0).1.2 j = (u 0 : A) * (c 0).1.2 j := congrFun (hu 0) j
    rw [← e, one_mul]
  refine ⟨fun i => ⟨⟨((c i).1.1, Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t)),
      span_snoc _ _ (c i).2⟩, ?_⟩, fun i j => ⟨(hc i j).1, u i * (u j)⁻¹, funext fun k => ?_⟩,
      fun i => Subtype.ext (Prod.ext rfl (funext fun k => ?_)), ?_⟩
  · change Ideal.span (Set.range fun j : Fin d =>
      Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) j.castSucc) = ⊤
    simpa using (c i).2
  · have hinv : ((u j : A)) * (((u j)⁻¹ : Aˣ) : A) = 1 := Units.mul_inv _
    refine Fin.lastCases ?_ (fun k => ?_) k
    · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) (Fin.last d) =
        ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) (Fin.last d)
      simp only [Fin.snoc_last, Units.val_mul]
      linear_combination (-(u i : A) * t) * hinv
    · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc =
        ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) k.castSucc
      simp only [Fin.snoc_castSucc, Units.val_mul]
      have e1 : (c i).1.2 k = (u i : A) * (c 0).1.2 k := congrFun (hu i) k
      have e2 : (c j).1.2 k = (u j : A) * (c 0).1.2 k := congrFun (hu j) k
      rw [e1, e2]
      linear_combination (-(u i : A) * (c 0).1.2 k) * hinv
  · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc = (c i).1.2 k
    simp
  · change Fin.snoc (α := fun _ => A) (c 0).1.2 ((u 0 : A) * t) (Fin.last d) = t
    simp [hu0]

theorem UpperTheory.nerve_first_projection :
    ∀ (D : Type) [CommRing D] (d : ℕ) (n : SimplexCategoryᵒᵖ) (T : Scheme.{0}), Function.Bijective fun x : ((CN (L2 D d)).obj n).obj (op T) => (((CN.map (fstV D d) (fstV_rel D d)).app n).app (op T) x, (x.1 0).1.1.2 (Fin.last d)) := by
  intro D _ d n T
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 : (x.1 0).1.1.2 (Fin.last d) = (y.1 0).1.1.2 (Fin.last d) := congrArg Prod.snd hxy
    refine Subtype.ext (fam_inj D d _ x.1 y.1 x.2 y.2 (fun i => ?_) h2)
    exact congrFun (congrArg Subtype.val h1) i
  · rintro ⟨c, t⟩
    obtain ⟨x, hx, hc, ht⟩ := fam_surj D d _ c.1 c.2 t
    refine ⟨⟨x, hx⟩, Prod.ext (Subtype.ext (funext hc)) ht⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedByUnits
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

private theorem specOf_prime {B : Type} [CommRing B] {T : Scheme.{0}} (ξ : B →+* Γ(T, ⊤)) (t : T) :
    (show PrimeSpectrum B from specOf ξ t).asIdeal =
      ((show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).asIdeal).comap ξ := by
  rfl

private theorem specOf_mem {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens)
    (hU : IsCompl' J U) {T : Scheme.{0}} (ξ : B →+* Γ(T, ⊤)) (hξ : J.map ξ = ⊤) (t : T) : specOf ξ t ∈ U := by
  rw [hU, specOf_prime]
  intro h
  have h1 : J.map ξ ≤ (show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).asIdeal := Ideal.map_le_iff_le_comap.2 h
  rw [hξ] at h1
  exact (show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).isPrime.ne_top (top_le_iff.1 h1)

private theorem specOf_inj {B : Type} [CommRing B] {T : Scheme.{0}} [IsAffine T] {ξ ξ' : B →+* Γ(T, ⊤)}
    (h : specOf ξ = specOf ξ') : ξ = ξ' := by
  have h1 := (cancel_epi T.toSpecΓ).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

private theorem exists_specOf {B : Type} [CommRing B] {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of B)) :
    ∃ ξ : B →+* Γ(T, ⊤), specOf ξ = f := by
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop).hom, ?_⟩
  rw [specOf, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem map_eq_top {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens)
    (hU : IsCompl' J U) {T : Scheme.{0}} [IsAffine T] (ξ : B →+* Γ(T, ⊤)) (h : ∀ t : T, specOf ξ t ∈ U) :
    J.map ξ = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hne
  have hbij : Function.Surjective T.toSpecΓ :=
    (T.toSpecΓ.homeomorph).surjective
  obtain ⟨t, ht⟩ := hbij (show Spec Γ(T, ⊤) from (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(T, ⊤)))
  have h1 := (hU _).1 (h t)
  apply h1
  rw [specOf_prime, ht]
  exact Ideal.map_le_iff_le_comap.1 hJm

private noncomputable def pointsMap {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens) (hU : IsCompl' J U)
    (P : PSh) (ψ : ∀ T : Scheme.{0}, P.obj (op T) → (B →+* Γ(T, ⊤)))
    (hnat : ∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P.obj (op T)), ψ T' (P.map f.op x) = f.appTop.hom.comp (ψ T x))
    (htop : ∀ (T : Scheme.{0}) (x : P.obj (op T)), J.map (ψ T x) = ⊤) : P ⟶ yoneda.obj (U : Scheme.{0}) where
  app T := TypeCat.ofHom fun x => IsOpenImmersion.lift U.ι (specOf (ψ T.unop x)) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact specOf_mem J U hU _ (htop T.unop x) t)
  naturality T T' g := by
    ext x
    change IsOpenImmersion.lift U.ι _ _ = g.unop ≫ IsOpenImmersion.lift U.ι _ _
    apply (cancel_mono U.ι).1
    rw [Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, comp_specOf]
    exact congrArg specOf (hnat g.unop x)

theorem represented_by_units :
    ∀ {B : Type} [CommRing B] (J : Ideal B) (U : (Spec (CommRingCat.of B)).Opens), IsCompl' J U → ∀ (P : PSh) (ψ : ∀ T : Scheme.{0}, P.obj (op T) → (B →+* Γ(T, ⊤))), (∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P.obj (op T)), ψ T' (P.map f.op x) = f.appTop.hom.comp (ψ T x)) → (∀ (T : Scheme.{0}) (x : P.obj (op T)), J.map (ψ T x) = ⊤) → (∀ (T : Scheme.{0}) (ξ : B →+* Γ(T, ⊤)), J.map ξ = ⊤ → ∃! x, ψ T x = ξ) → ∃ φ : P ⟶ yoneda.obj (U : Scheme.{0}), (∀ (T : Scheme.{0}) (x : P.obj (op T)), φ.app (op T) x ≫ U.ι = specOf (ψ T x)) ∧ ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro B _ J U hU P ψ hnat htop huniq
  have hfac : ∀ (T : Scheme.{0}) (x : P.obj (op T)),
      (pointsMap J U hU P ψ hnat htop).app (op T) x ≫ U.ι = specOf (ψ T x) := fun T x =>
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨pointsMap J U hU P ψ hnat htop, hfac, fun T hT => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · have h1 : specOf (ψ T x) = specOf (ψ T y) := by
      rw [← hfac, ← hfac, hxy]
    exact (huniq T _ (htop T x)).unique rfl (specOf_inj h1).symm
  · obtain ⟨ξ, hξ⟩ := exists_specOf (g ≫ U.ι)
    have hmem : ∀ t : T, specOf ξ t ∈ U := fun t => by
      rw [hξ]
      have h2 : (g ≫ U.ι) t ∈ Set.range U.ι := ⟨(show T ⟶ (U : Scheme.{0}) from g) t, rfl⟩
      rwa [Scheme.Opens.range_ι] at h2
    obtain ⟨x, hx, -⟩ := huniq T ξ (map_eq_top J U hU ξ hmem)
    refine ⟨x, (cancel_mono U.ι).1 ?_⟩
    rw [hfac, hx, hξ]

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassOfBoundedOfCyclesLift
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory

set_option backward.isDefEq.respectTransparency false in
private theorem hb_step {C : Type*} [Category C] [Preadditive C] (K D : CochainComplex C ℤ)
    (H : ∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 →
      ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f)
    (n p₀ : ℤ) (z : Cochain K D n) (hz : δ n (n + 1) z = 0)
    (hv : ∀ (p q : ℤ) (hpq : p + n = q), p₀ < p → z.v p q hpq = 0) :
    ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q), p₀ ≤ p →
      (z - δ (n - 1) n γ).v p q hpq = 0 := by
  have hf : z.v p₀ (p₀ + n) rfl ≫ D.d (p₀ + n) (p₀ + n + 1) = 0 := by
    have h0 := congrArg (fun c => Cochain.v c p₀ (p₀ + n + 1) (by omega)) hz
    simp only [Cochain.zero_v] at h0
    rw [δ_v n (n + 1) rfl z p₀ (p₀ + n + 1) (by omega) (p₀ + n) (p₀ + 1) (by omega) rfl,
      hv (p₀ + 1) (p₀ + n + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at h0
    exact h0
  obtain ⟨g, hg⟩ := H p₀ (p₀ + n) (z.v p₀ (p₀ + n) rfl) hf
  refine ⟨Cochain.single g (n - 1), ?_⟩
  intro p q hpq hp
  rw [Cochain.sub_v, δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
    Cochain.single_v_eq_zero g (n - 1) (p + 1) q (by omega) (by omega), comp_zero, smul_zero, add_zero]
  rcases hp.lt_or_eq with hlt | rfl
  · rw [hv p q hpq hlt, Cochain.single_v_eq_zero g (n - 1) p (q - 1) (by omega) (by omega), zero_comp,
      sub_zero]
  · subst hpq
    rw [Cochain.single_v, hg, sub_self]

end UpperTheory

theorem UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift :
    ∀ (K D : Cx ℤ) [K.IsStrictlyLE 0] (a : ℤ) [D.IsStrictlyGE a], (∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 → ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f) → ∀ n : ℤ, Subsingleton (CohomologyClass K D n) := by
  intro K D _ a _ H n
  have hz0 : ∀ (z : Cocycle K D n) (k : ℕ), ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q),
      -(k : ℤ) < p → ((z : Cochain K D n) - δ (n - 1) n γ).v p q hpq = 0 := by
    intro z k
    induction k with
    | zero =>
      refine ⟨0, fun p q hpq hp => ?_⟩
      exact (K.isZero_of_isStrictlyLE 0 p (by simpa using hp)).eq_of_src _ _
    | succ k ih =>
      obtain ⟨γ, hγ⟩ := ih
      obtain ⟨γ', hγ'⟩ := UpperTheory.hb_step K D H n (-(k : ℤ)) ((z : Cochain K D n) - δ (n - 1) n γ)
        (by rw [δ_sub, z.δ_eq_zero, δ_δ, sub_zero]) (fun p q hpq hp => hγ p q hpq hp)
      refine ⟨γ + γ', fun p q hpq hp => ?_⟩
      rw [δ_add, ← sub_sub]
      exact hγ' p q hpq (by push_cast at hp; omega)
  have all : ∀ z : Cocycle K D n, CohomologyClass.mk z = 0 := by
    intro z
    obtain ⟨γ, hγ⟩ := hz0 z (n - a + 1).toNat
    have hk := Int.self_le_toNat (n - a + 1)
    have hzero : (z : Cochain K D n) - δ (n - 1) n γ = 0 := by
      apply Cochain.ext
      intro p q hpq
      rw [Cochain.zero_v]
      by_cases hp : -((n - a + 1).toNat : ℤ) < p
      · exact hγ p q hpq hp
      · exact (D.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, γ, (sub_eq_zero.mp hzero).symm⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [all x, all y]
end

