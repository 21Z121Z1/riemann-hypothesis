import Development.EtaleCohomology.EtaleTrace.Bundle0007

-- bundled from Development.EtaleCohomology.EtaleTrace.GenEtalePfCut
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineData : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom

def GenEtaleAtBot : Prop := ∀ {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (π : X ⟶ P) (U : P.Opens), IsAffineOpen U →
  (U : Set P).Nonempty → IsAffineOpen (π ⁻¹ᵁ U) → (π.app U).hom.Finite → Function.Injective (π.app U).hom →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime,
    (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

theorem GenAffineSetup_of (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenAffineSetup := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hN, hf, hi⟩ := h1 k p r π hπ hr hfin hsurj
  exact ⟨U, hU, hne, hU', hN, hf, hi, h2 π U hU hne hU' hf hi hun⟩

theorem GenEtale_of' (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenEtale :=
  GenEtale_of (GenAffineSetup_of h1 h2) etaleOverBasic

end LateralTheory.EtaleTrace.Cov
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutChartPfSect
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace LateralTheory.EtaleTrace.Cov

theorem alg_germ_eq (X : Scheme.{0}) [IsIntegral X] {V : X.Opens} (s : Γ(X, V)) {y w : X} (hy : y ∈ V) (hw : w ∈ V) :
    algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.germ V w hw s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ V y hy s) := by
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]

theorem sect_exists (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (z : X.functionField)
    (hz : ∀ y ∈ U, z ∈ loc X y) : ∃ s : Γ(X, U), ∀ (y : X) (hy : y ∈ U),
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) = z := by
  have key : ∀ y : U, ∃ (V : X.Opens) (hV : y.1 ∈ V) (s : Γ(X, V)),
      algebraMap (X.presheaf.stalk y.1) X.functionField (X.presheaf.germ V y.1 hV s) = z := by
    intro y
    obtain ⟨a, ha⟩ := hz y.1 y.2
    obtain ⟨V, hyV, s, hs⟩ := X.presheaf.exists_germ_eq (x := y.1) a
    exact ⟨V, hyV, s, by rw [hs, ha]⟩
  choose V hV s hs using key
  let W : U → X.Opens := fun y => V y ⊓ U
  let sf : ∀ y : U, Γ(X, W y) := fun y => X.presheaf.map (homOfLE inf_le_left : W y ⟶ V y).op (s y)
  have hsf : ∀ (y : U) (w : X) (hw : w ∈ W y),
      algebraMap (X.presheaf.stalk w) X.functionField (X.presheaf.germ (W y) w hw (sf y)) = z := by
    intro y w hw
    simp only [sf, TopCat.Presheaf.germ_res_apply]
    rw [alg_germ_eq X (s y) (hV y) hw.1, hs]
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro w hw
    congr 1
    refine @Scheme.germToFunctionField_injective X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ _ _ ?_
    rw [← @Scheme.algebraMap_germ_eq_germToFunctionField X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ w hw,
      ← @Scheme.algebraMap_germ_eq_germToFunctionField X _ (W i ⊓ W j) ⟨⟨w, hw⟩⟩ w hw]
    simp only [TopCat.Presheaf.germ_res_apply]
    rw [hsf i w hw.1, hsf j w hw.2]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W U (fun y => homOfLE inf_le_right)
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _, hy⟩) sf hcompat
  refine ⟨t, fun y hy => ?_⟩
  have h1 := hsf ⟨y, hy⟩ y (show y ∈ W ⟨y, hy⟩ from ⟨hV _, hy⟩)
  rw [← ht ⟨y, hy⟩] at h1
  change algebraMap _ _ (X.presheaf.germ (W ⟨y, hy⟩) y _
    (X.presheaf.map (homOfLE inf_le_right : W ⟨y, hy⟩ ⟶ U).op t)) = z at h1
  erw [TopCat.Presheaf.germ_res_apply] at h1
  exact h1

theorem sect_ext (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy t)) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro y hy
  have : s = t := by
    refine @Scheme.germToFunctionField_injective X _ U ⟨⟨y, hy⟩⟩ _ _ ?_
    rw [← @Scheme.algebraMap_germ_eq_germToFunctionField X _ U ⟨⟨y, hy⟩⟩ y hy,
      ← @Scheme.algebraMap_germ_eq_germToFunctionField X _ U ⟨⟨y, hy⟩⟩ y hy]
    exact h y hy
  rw [this]

theorem SectOfLoc_pf : SectOfLoc := by
  intro X _ U R hR
  have hex : ∀ z : R, ∃ s : Γ(X, U), ∀ (y : X) (hy : y ∈ U),
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) = z :=
    fun z => sect_exists X U z (hR z z.2)
  choose σ hσ using hex
  refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩
  · exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · intro a b; exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · exact sect_ext X U _ _ fun y hy => by simp [hσ]
  · intro a b; exact sect_ext X U _ _ fun y hy => by simp [hσ]

theorem GenOutChart_of_gen (h : ChartGen) : GenOutChart := GenOutChart_of_sect SectOfLoc_pf h

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LEmptyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LEmptyPf

theorem sec_subsingleton {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) :
    Subsingleton (Sec F X) := by
  have ht : IsTerminal (F.obj.obj (Opposite.op X)) :=
    Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)
  have hz : IsZero (F.obj.obj (Opposite.op X)) := ht.isZero
  exact ModuleCat.subsingleton_of_isZero hz

theorem pos_zero (a5 : A5) {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) (n : ℤ)
    (hn : 0 < n) (x : H R (sch.obj X) F n) : x = 0 := by
  obtain ⟨Y, f, -, -, hx⟩ := a5 R X F n hn x
  have : IsEmpty Y := Function.isEmpty f.base
  have : IsIso f := isIso_of_isEmpty f
  have h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) := by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  rw [h1, hx, map_zero]

theorem LEmpty_of : LateralTheory.EtaleTrace.LPdCut.LEmpty := by
  intro a5 a9 R _ X hX F n
  refine ⟨fun a b => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact ((a9 R F).1 _ n h).elim a b
  · obtain ⟨e, -⟩ := (a9 R F).2
    have := sec_subsingleton X F
    exact (e X).symm.injective (Subsingleton.elim _ _)
  · rw [pos_zero a5 X F n h a, pos_zero a5 X F n h b]

end LateralTheory.EtaleTrace.LEmptyPf
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LSmoothPf
section
open MvPolynomial

namespace LateralTheory.EtaleTrace.LSmoothPf

noncomputable def polyPres (k : Type) [CommRing k] (N : ℕ) :
    Algebra.SubmersivePresentation k (MvPolynomial (Fin N) k) (Fin N) PEmpty.{1} where
  toGenerators := Algebra.Generators.mvPolynomial k (Fin N)
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [Algebra.Generators.ker_eq_ker_aeval_val, ← RingHom.injective_iff_ker_eq_bot]
    intro a b h
    simpa using h
  map := PEmpty.elim
  map_inj a := by cases a
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    rw [Matrix.det_isEmpty, map_one]
    exact isUnit_one

theorem poly_ssmooth (k : Type) [CommRing k] (N : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension N k (MvPolynomial (Fin N) k) :=
  (polyPres k N).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

open CategoryTheory AlgebraicGeometry LateralTheory.EtaleTrace.LPdCut
attribute [local instance] MvPolynomial.gradedAlgebra

theorem spec_C_smooth (k : Type) [Field k] (N : ℕ) :
    SmoothOfRelativeDimension N (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := N) (R := k) (S := MvPolynomial (Fin N) k)).mpr
    (poly_ssmooth k N)

theorem Dp_cover (k : Type) [Field k] (N : ℕ) : ⨆ i, Dp k N i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i; exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · rw [eq_top_iff]
    intro p _hp
    clear _hp
    induction p using MvPolynomial.induction_on with
    | C a =>
      have ha : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0 :=
        MvPolynomial.isHomogeneous_C _ a
      have : MvPolynomial.C a = algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) ⟨_, ha⟩ := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem LSmooth_of (hC : LChart) : LSmooth := by
  intro k _ N
  choose j hj hc hr using fun i => hC k N i
  let 𝒰 : (PN k N).OpenCover := Scheme.Cover.mkOfCovers (Fin (N + 1)) _ j (fun x => by
    have hx : x ∈ (⊤ : (PN k N).Opens) := trivial
    rw [← Dp_cover k N] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : x ∈ Set.range (j i) := by rw [hr i]; exact hi
    obtain ⟨y, hy⟩ := this
    exact ⟨i, y, hy⟩) hj
  have hA : ∀ i, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) k))); infer_instance
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} N) 𝒰 (fun i => ?_)
  have h : SmoothOfRelativeDimension N (𝒰.f i ≫ PNto k N) := by
    change SmoothOfRelativeDimension N (j i ≫ PNto k N)
    rw [hc i]
    exact spec_C_smooth k N
  exact (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension.{0} N)).mp h

end LateralTheory.EtaleTrace.LSmoothPf
end

-- bundled from Development.EtaleCohomology.EtaleTrace.PtCoverPf
section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TwZeroPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

theorem primLoc_of (hS : PrimSplit) (hL : SplitLoc) : PrimLoc := by
  intro q _ U ζ ξ
  obtain ⟨e, he, hs, hx, hc⟩ := hS q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hSc, hP⟩ := hL U q e he hs
  refine ⟨S, hSc, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ) := by
    have := congrArg g.appTop.hom (hx i)
    simpa [map_mul, map_pow, hi] using this
  by_cases hcop : Nat.Coprime (i : ℕ) q
  · refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _
    rw [key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  · have h0 := hc i hcop
    rw [h0, map_zero] at hi
    have : Subsingleton Γ(V, ⊤) := subsingleton_of_zero_eq_one hi
    exact ⟨1, Subsingleton.elim _ _⟩

theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
end
end

