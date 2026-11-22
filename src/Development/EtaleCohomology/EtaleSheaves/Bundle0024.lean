import Development.EtaleCohomology.EtaleSheaves.Bundle0010
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Development.EtaleCohomology.EtaleSheaves.Bundle0009
import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0013

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafGeomPfLoc

theorem projective_bundle_direct_sum_zero_vertex_coordinates_restrict {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X Y : Scheme.{0}}
    (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (j : Fin (a + b)) :
    vec0 V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) j = Scheme.Γ.map k.op (vec0 V W x j) := by
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold vec0
  erw [h]
  rfl

theorem unit_le {X : Scheme.{0}} (f : Γ(X, ⊤)) {V : X.Opens} (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom f) := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen (U := ⊤) f
  have := hu.map (X.presheaf.map (homOfLE h).op).hom
  erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem unit_basicOpen {X : Scheme.{0}} (f : Scheme.Γ.obj (op X)) :
    IsUnit (Scheme.Γ.map (X.basicOpen f).ι.op f) := by
  rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
  exact unit_le f (X.basicOpen f).ι_image_top.le

theorem leafLocal : LeafLocal := by
  intro E a b V W n X x
  have hspan : Ideal.span (Set.range (vec0 V W x)) = ⊤ :=
    ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).2
  have hcov : TopologicalSpace.IsOpenCover (fun j => X.basicOpen (vec0 V W x j)) := by
    have := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range (vec0 V W x)) hspan
    refine le_antisymm le_top ?_
    rw [← this]
    exact iSup₂_le fun _ ⟨j, hj⟩ => hj ▸ le_iSup (fun j => X.basicOpen (vec0 V W x j)) j
  let 𝒰 := X.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology, ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, g, rfl⟩ := hk
  have hu : IsUnit (Scheme.Γ.map (g ≫ 𝒰.f j).op (vec0 V W x j)) := by
    rw [op_comp, Functor.map_comp]
    exact (unit_basicOpen (vec0 V W x j)).map (Scheme.Γ.map g.op).hom
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : (∃ i, j = Fin.castAdd b i) ∨ ∃ i, j = Fin.natAdd a i :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j
  · left
    simp only [First, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  · right
    simp only [Second, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) : LateralTheory.E.D2.LeafGeom :=
  LateralTheory.E.LeafGeomPf.LeafGeom_of h1 h2 leafLocal

end LateralTheory.E.LeafGeomPfLoc
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostRelCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

def LeafTrunc : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [HasDerivedCategory.{2} A]
  (K0 K1 K2 L : DerivedCategory A) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2),
  (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) →
  (DerivedCategory.homologyFunctor A 2).map f = 0 → (DerivedCategory.homologyFunctor A 1).map g = 0 →
  (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) →
  (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) →
  IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) →
  ∃ h : K0 ⟶ L, h ≫ ℓ = f ≫ g

def LeafRep : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∃ (A : Type 2) (_ : Category.{1} A) (_ : Abelian A) (_ : HasDerivedCategory.{2} A) (O K0 K1 K2 L : DerivedCategory A)
    (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj L)),
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) ∧
    (DerivedCategory.homologyFunctor A 2).map f = 0 ∧ (DerivedCategory.homologyFunctor A 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map ℓ)

theorem goal_of (hT : LeafTrunc) (hR : LeafRep) : LeafGhostRel := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n y
  obtain ⟨A, _, _, _, O, K0, K1, K2, L, f, g, ℓ, e0, e2, eL, hK0, hf, hg, hK2, hL, hℓ, hinj, hsurj, n0, nL⟩ :=
    hR hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨h, hh⟩ := hT A K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  obtain ⟨c, hc⟩ := hsurj n (e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map h)
  refine ⟨c, hinj n ?_⟩
  rw [n0, nL, hc, Category.assoc, ← Functor.map_comp, hh]

end LateralTheory.E.LeafGhostRelCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafJacobianPf
section
noncomputable section
open MvPolynomial TensorProduct
namespace LateralTheory.E.LeafJacobianPf

theorem mapBaseChange_bij (A ι S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra (MvPolynomial ι A) S] [IsScalarTower A (MvPolynomial ι A) S]
    (hli : LinearIndependent S fun i => KaehlerDifferential.D A S (algebraMap (MvPolynomial ι A) S (X i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D A S (algebraMap (MvPolynomial ι A) S (X i))) = ⊤) :
    Function.Bijective (KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) S) := by
  let bT := Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis A ι)
  let bS := Module.Basis.mk hli hsp.ge
  have h : KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) S = (bT.equiv bS (Equiv.refl ι)).toLinearMap := by
    refine bT.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.mk_apply]
    simp [bT, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mapBaseChange_tmul]
  rw [h]
  exact (bT.equiv bS (Equiv.refl ι)).bijective

theorem formallyEtale_of_bij (A R S : Type) [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    [Algebra R S] [IsScalarTower A R S] [Algebra.FormallySmooth A S]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange A R S)) : Algebra.FormallyEtale R S := by
  have hD : ∀ s : S, KaehlerDifferential.D R S s = 0 := by
    intro s
    obtain ⟨y, hy⟩ := h.2 (KaehlerDifferential.D A S s)
    have h2 := (KaehlerDifferential.exact_mapBaseChange_map A R S).apply_apply_eq_zero y
    rw [hy, KaehlerDifferential.map_D] at h2
    simpa using h2
  have hK : Subsingleton (KaehlerDifferential R S) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ x : KaehlerDifferential R S, x = 0 := by
      intro x
      have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
        rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨s, rfl⟩ := hy; exact hD s
      | zero => rfl
      | add a b _ _ ha hb => rw [ha, hb, add_zero]
      | smul c a _ ha => rw [ha, smul_zero]
    rw [key a, key b]
  have hH : Subsingleton (Algebra.H1Cotangent R S) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ z : Algebra.H1Cotangent R S, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ A R S z = 0 := by
        apply h.1
        rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange A R S).apply_apply_eq_zero z, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ A R S z).mp hz
      rw [← hw, Subsingleton.elim w 0, map_zero]
    rw [key a, key b]
  exact ⟨hK, hH⟩

theorem LeafJacobian_of : LateralTheory.E.LeafChartRingPf.LeafJacobian := by
  intro d e A B _ _ _ n hB g t y hli hsp
  let ψ := (sumAlgEquiv A (Fin d) (Fin e)).toRingEquiv
  let φ : MvPolynomial (Fin d ⊕ Fin e) A →+* Localization.Away g :=
    (LateralTheory.E.LeafChartRingPf.coordMap (A := A) g y t).comp ψ.toRingHom
  have hφX : ∀ i, φ (X i) = Sum.elim (fun j => algebraMap B (Localization.Away g) (t j))
      (fun k => algebraMap B (Localization.Away g) (y k)) i := by
    intro i; cases i <;> simp [φ, ψ, LateralTheory.E.LeafChartRingPf.coordMap]
  have hφ : φ.Etale := by
    letI : Algebra (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) := φ.toAlgebra
    haveI : IsScalarTower A (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        simp [RingHom.algebraMap_toAlgebra, φ, ψ, LateralTheory.E.LeafChartRingPf.coordMap,
          MvPolynomial.algebraMap_eq]
    haveI := hB.isStandardSmooth
    haveI : Algebra.FormallySmooth A B := inferInstance
    haveI : Algebra.FormallySmooth B (Localization.Away g) :=
      Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.comp A B _
    have hfam : (fun i => KaehlerDifferential.D A (Localization.Away g)
        (algebraMap (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) (X i))) =
        (Sum.elim
          (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
          (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) ∘
          Equiv.sumComm (Fin d) (Fin e) := by
      funext i
      rw [RingHom.algebraMap_toAlgebra, hφX]
      cases i <;> rfl
    have hbij := mapBaseChange_bij A (Fin d ⊕ Fin e) (Localization.Away g)
      (by rw [hfam]; exact hli.comp _ (Equiv.injective _))
      (by rw [hfam, (Equiv.surjective _).range_comp]; exact hsp)
    haveI := formallyEtale_of_bij A (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation B (Localization.Away g) := IsLocalization.Away.finitePresentation g
    haveI : Algebra.FinitePresentation A (Localization.Away g) := Algebra.FinitePresentation.trans A B _
    haveI : Algebra.FinitePresentation (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A _ _
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have hc : LateralTheory.E.LeafChartRingPf.coordMap (A := A) g y t = φ.comp ψ.symm.toRingHom := by
    refine RingHom.ext fun x => ?_
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [hc]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective ψ.symm.bijective) hφ

end LateralTheory.E.LeafJacobianPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

def L_ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x) ∧ ∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

end Basic

section Kum
variable (q : ℕ) [NeZero q]

end Kum

end LateralTheory.E.LeafKumSpecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKunGlobalCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.LeafKunnethCut

namespace LateralTheory.E.LeafKunGlobalCut

def LeafKunFT : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  (∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b) →
  ∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s],
    KunAt q s r S deg j b

def LeafKunAffine : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s],
    KunAt q s r S deg j b) →
  ∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)), KunAt q s r S deg j b

def LeafKunQcqs : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)), KunAt q s r S deg j b) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p], KunAt q p r S deg j b

theorem goal_of (h1 : LeafKunFT) (h2 : LeafKunAffine) (h3 : LeafKunQcqs) : LateralTheory.E.LeafKunnethCut.LeafKunGlobal := by
  intro hB q _ k _ _ hq Y r _ _ S _ deg j b hb hSH X p _ _
  exact h3 hB q k hq r S deg j b (h2 hB q k hq r S deg j b (h1 hB q k hq r S deg j b hb hSH)) p

end LateralTheory.E.LeafKunGlobalCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatCupPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatCupPf

section

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  rw [ComplexShape.embeddingDownNat.extendFunctor_map (C := Shv R)]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  simp only [chainsN]
  erw [Iso.inv_hom_id_assoc]
  simp
  rfl

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  have h2 : (((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (g.app (op U) x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom h2)

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  simp only [ev]
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (add_zero _) h, Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_inv_map, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem sub_pull {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') (N := N) ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  have := ConcreteCategory.congr_hom (congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [Sx.sub]
  exact this

theorem isAW_pull {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E') I n) (β : Cochain ((chains R).obj E') J m) (γ : Cochain ((chains R).obj E') K k)
    (hγ : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w h U x
  rw [ev_pull, hγ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pull, ev_pull, sub_pull, sub_pull]

theorem pull_mk {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (z : Cocycle ((chains R).obj E') (res R F) n) :
    pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) :=
  rfl

theorem zcomp_ofHom_val {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (z : Cocycle ((chains R).obj E') I n) :
    (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)).1 = (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add n) :=
  rfl

end

open CupProductRingLaws in
theorem LeafNatCup_of (hc : LeafCupSpec) : LeafNatCup := by
  intro q _ E E' f n m i j a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (hc (ZMod q) (twPair q i j) E' rfl).1 α β
  have e1 : cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    (hc (ZMod q) (twPair q i j) E' rfl).2 α β γ hγ
  have hAW := isAW_pull (twPair q i j) f rfl α.1 β.1 γ.1 hγ
  rw [← zcomp_ofHom_val, ← zcomp_ofHom_val, ← zcomp_ofHom_val] at hAW
  have e2 := (hc (ZMod q) (twPair q i j) E rfl).2 _ _ _ hAW
  rw [e1, pull_mk, pull_mk, pull_mk]
  exact e2.symm

end LateralTheory.E.LeafNatCupPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafNatOnePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatOnePf

variable {R : Type} [CommRing R]

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  unfold freeGen
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) ?_)
  exact ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (g.app (op U))) (ULift.up.{1} x)

theorem chainsXIso_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  unfold chainsXIso chains
  rw [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by omega) (by omega), Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_nat, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem LeafNatOne_of (hOne : LateralTheory.E.CupProductRingLaws.LeafOneSpec) : LateralTheory.E.CupProductRingLaws.LeafNatOne := by
  intro q _ E E' f hE'
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨(f.app (op (SimplexCategory.mk 0))).app (op U) x⟩
  obtain ⟨⟨α, hα⟩, h'⟩ := hOne q E' hE'
  rw [h' α hα]
  let β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0 :=
    zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) α (zero_add 0)
  have hβ : LateralTheory.E.CupProductRingLaws.IsOneCocycle q E β := fun U x ζ => by
    rw [← hα U ((f.app (op (SimplexCategory.mk 0))).app (op U) x) ζ]
    exact ev_pull f α.1 0 0 _ U x
  rw [(hOne q E hE).2 β hβ]
  rfl

end LateralTheory.E.LeafNatOnePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPointTransferCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def relF (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (c : H R E F n),
  pull R f F n c = 0 ↔ ∃ e : Hrel R f F n, relF R f F n e = c

def LeafRelTransfer : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d)
    (Tr : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d) →+ Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d)),
    Function.Surjective Tr ∧
      ∀ e, T (relF (ZMod q) (sch.map U.ι) (tw q d) (2 * d) e) = relF (ZMod q) (sch.map W.ι) (tw q d) (2 * d) (Tr e)

def LeafRelPoint : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) (d : ℕ) [SmoothOfRelativeDimension d r]
    (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ r = 𝟙 _ → ∀ W : Y.Opens, (W : Set Y) = (Set.range y)ᶜ →
    ∃ g : Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d), addOrderOf g = q ∧ ∀ e, ∃ m : ℤ, e = m • g

def LeafRelTransferOrd : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d)
    (Tr : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d) →+ Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d)),
    (∃ e, addOrderOf (Tr e) = q) ∧
      ∀ e, T (relF (ZMod q) (sch.map U.ι) (tw q d) (2 * d) e) = relF (ZMod q) (sch.map W.ι) (tw q d) (2 * d) (Tr e)

end LateralTheory.E.E8

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPf
section
noncomputable section
open LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafRoofEtPf

def LeafRoofEtP : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (P : Type) (_ : CommRing P) (a : B →+* P) (b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* P)
    (m : P →+* B ⧸ varIdeal φ) (e : P), a.Etale ∧ b.Etale ∧ (∀ j, a (φ (MvPolynomial.X j)) = b (MvPolynomial.X j)) ∧
    m.comp a = Ideal.Quotient.mk _ ∧ m.comp b = MvPolynomial.constantCoeff ∧
    m e = 0 ∧ e * e - e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ∧
    ∀ x, m x = 0 → x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ⊔ Ideal.span {e}

theorem LeafRoofEt_of (h : LeafRoofEtP) : LateralTheory.E.LeafRoofPf.LeafRoofEt := by
  intro d C B _ _ φ hφ
  obtain ⟨P, _, a, b, m, e, ha, hb, hab, hma, hmb, hme, he, hk⟩ := h d φ hφ
  refine ⟨P, inferInstance, a, b, m, 1 - e, ha, hb, hab, hma, hmb, by simp [hme], fun x hx => ⟨1, ?_⟩⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hk x hx)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have : (1 - e) ^ 1 * (y + r * e) = (1 - e) * y - r * (e * e - e) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ he)

end LateralTheory.E.LeafRoofEtPf
end
end

