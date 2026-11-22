import Development.EtaleCohomology.EtaleTrace.Bundle0006
import Development.EtaleCohomology.EtaleTrace.Bundle0005
import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.EtaleCohomology.KummerTheory.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.EtaleCohomology.KummerTheory.Bundle0001
import Development.EtaleCohomology.EtaleSheaves.Bundle0026
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

-- bundled from Development.EtaleCohomology.EtaleTrace.CocEqPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenEtalePfBasic
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutChartPfRing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem homog_div_mem {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (_hi : w i ≠ 0) (R : Subring K) (hκ : ∀ c, κ c ∈ R) (hw : ∀ j, w j / w i ∈ R)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g.IsHomogeneous m) : eval₂ κ w g / w i ^ m ∈ R := by
  rw [eval₂_eq, Finset.sum_div]
  refine Subring.sum_mem _ fun d hd => ?_
  have hdeg : ∑ j, d j = m := by
    rw [← hg (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : (κ (coeff d g) * ∏ j, w j ^ d j) / w i ^ m = κ (coeff d g) * ∏ j, (w j / w i) ^ d j := by
    rw [mul_div_assoc]; congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hsupp : ∏ j ∈ d.support, w j ^ d j = ∏ j, w j ^ d j :=
    Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])
  rw [hsupp, this]
  exact Subring.mul_mem _ (hκ _) (Subring.prod_mem _ fun j _ => Subring.pow_mem _ (hw j) _)

def chartVal {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K) (i : Fin (N + 1))
    (hi : w i ≠ 0) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* K :=
  (IsLocalization.Away.lift (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) (g := eval₂Hom κ w)
    (by simpa using hi.isUnit)).comp
    (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)))

theorem chartVal_mk {k : Type} [Field k] {K : Type} [Field K] (κ : k →+* K) {N : ℕ} (w : Fin (N + 1) → K)
    (i : Fin (N + 1)) (hi : w i ≠ 0)
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)) :
    chartVal κ w i hi (HomogeneousLocalization.Away.mk _ hx m g hg) = eval₂ κ w g / w i ^ m := by
  simp only [chartVal, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [coe_eval₂Hom, eval₂_pow, eval₂_X]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hi)]

def SectOfLoc : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (R : Subring X.functionField),
  (∀ z ∈ R, ∀ y ∈ U, z ∈ loc X y) →
  ∃ φ : R →+* Γ(X, U), ∀ (z : R) (y : X) (hy : y ∈ U),
    algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy (φ z)) = z

theorem ChartRing_of (h : SectOfLoc) : ChartRing := by
  intro k _ X _ p N w i hi U hU hx
  let ψ := chartVal (kHom p) w i hi
  have hR : ∀ z ∈ ψ.range, ∀ y ∈ U, z ∈ loc X y := by
    rintro _ ⟨a, rfl⟩ y hy
    obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hx a
    rw [chartVal_mk]
    have hg' : g.IsHomogeneous m := by
      simpa using (mem_homogeneousSubmodule _ _).1 hg
    exact homog_div_mem (kHom p) w i hi (loc X y) (fun c => kHom_mem_loc p y c) (fun j => hU y hy j) m g hg'
  obtain ⟨φ, hφ⟩ := h X U ψ.range hR
  refine ⟨φ.comp ψ.rangeRestrict, fun y hy m g hg => ?_⟩
  rw [RingHom.comp_apply, hφ]
  exact chartVal_mk (kHom p) w i hi hx m g hg

theorem GenOutChart_of_sect (h1 : SectOfLoc) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of (ChartRing_of h1) h2

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LFinCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LFinCut

theorem normal_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) [Smooth p] : GlobalTheory.IsNormalScheme X := by
  rw [GlobalTheory.isNormalScheme_iff]
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p fun y => ?_
  have hf : IsField ((S k).presheaf.stalk y) := isField_stalk_of_closure_mem_irreducibleComponents (S k) y (by
    have : closure ({y} : Set (S k)) = Set.univ := Set.eq_univ_of_forall fun z => subset_closure (Subsingleton.elim z y)
    rw [this, irreducibleComponents_eq_singleton]; rfl)
  let := hf.toField
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.LFinCut

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.LPdCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def Std (k : Type) [Field k] (N : ℕ) : (PN k N).Opens := ⨆ j : Fin N, Dp k N j.succ

def ZariskiLocallyAffineLine {U Y : Scheme.{0}} (f : U ⟶ Y) : Prop := ∀ y : Y, ∃ (A : Type) (_ : CommRing A)
  (j : Spec (CommRingCat.of A) ⟶ Y) (j' : Spec (CommRingCat.of (Polynomial A)) ⟶ U), IsOpenImmersion j ∧ y ∈ Set.range j ∧
    IsPullback j' (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) f j

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LIntegral : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PN k N)

def LMove : Prop := ∀ (k : Type) [Field k] (N : ℕ) (t : Pt (PNto k N)),
  ∃ g : PN k N ⟶ PN k N, IsIso g ∧ ((g ⁻¹ᵁ Std k N : (PN k N).Opens) : Set (PN k N)) = (Set.range t.1)ᶜ

def LProjn : Prop := ∀ (k : Type) [Field k] (e : ℕ), ∃ f : (Std k (e + 1)).toScheme ⟶ PN k e, ZariskiLocallyAffineLine f

def AffineLineTwistInvariance : Prop := B3 → C4 → ∀ (q : ℕ) [NeZero q] {U Y : Scheme.{0}} (f : U ⟶ Y), ZariskiLocallyAffineLine f → IsUnit (q : Γ(Y, ⊤)) →
  ∀ i : ℤ, Eqv _ (sch.map f) (tw q i)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

def LLoc : Prop := Base → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LLim : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ j, Nonempty (Ht (l ^ j) E n i ≃+ ZMod (l ^ j))) →
  (∀ j, Function.Surjective (red (l ^ (j + 1)) (l ^ j) E n i)) → Nontrivial (HQ l E n i)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn; subst hi; rfl

theorem vanish (a9 : A9) (e8 : E8) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p] (n i : ℤ)
    (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨tr, h⟩ := e8 q k hq p d
  have hs : Subsingleton (Ht q (sch.obj X) (2 * d - n) (d - i)) := (a9 _ _).1 _ _ (by omega)
  refine ⟨fun a a' => (h n i 0).unique (fun b => ?_) (fun b => ?_)⟩ <;>
    rw [Subsingleton.elim b 0, map_zero, map_zero, cast_zero, map_zero]

theorem sub_iso {R : Type} [CommRing R] {X Y : Scheme.{0}} (a : X ⟶ Y) [IsIso a] (F : Shv R) (n : ℤ)
    [h : Subsingleton (H R (sch.obj Y) F n)] : Subsingleton (H R (sch.obj X) F n) := by
  have : ∀ y, pull R (sch.map a) F n (pull R (sch.map (inv a)) F n y) = y := fun y => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨fun y y' => by rw [← this y, ← this y', Subsingleton.elim (pull R (sch.map (inv a)) F n y)]⟩

theorem goal_of (hP : LProper) (hS : LSmooth) (hI : LIntegral) (hM : LMove) (hJ : LProjn) (hA : AffineLineTwistInvariance) (hE : LEmpty)
    (hL : LLoc) (hLim : LLim) (hB : LateralTheory.KummerTheory.Bock) (hT : LateralTheory.E.LeafTwistPf.LeafTwSec) : LPd := by
  intro hb l hl k _ _ hlk d
  have hb' := hb
  obtain ⟨⟨-, -, -, -, a5, -, -, -, -, a7, a8, a9, a10, a11⟩, ⟨-, -, b3, -, -⟩, ⟨c4, -, -⟩, -, -, -, -, -, e8⟩ := hb'
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by
    rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hlk).pow j
  have hz : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have := hP k
  have := hS k
  have := hI k
  refine ⟨⟨hP k d, hS k d⟩, hI k d, fun t U hU => ?_⟩
  have hnt : Nontrivial (V l (PN k d) (2 * d)) := by
    refine hLim l _ _ 0 (fun j => ?_) (fun j => ?_)
    · obtain ⟨tr, -⟩ := e8 (l ^ j) k (hu j) (PNto k d) d
      obtain ⟨ζ⟩ := LateralTheory.E.LeafKumCut.prim_of_isAlgClosed (l ^ j) k (hu j)
      obtain ⟨e, he⟩ := hT (l ^ j) k ζ 0 d
      obtain ⟨w⟩ := hL hb _ (PN k d) _ _ (fun U x => e U (x ≫ PNto k d))
        (fun g x s => by rw [Category.assoc]; exact he g _ s) (2 * d)
      exact ⟨w.trans tr⟩
    · obtain ⟨u, δ, h⟩ := hB a7 a8 a10 a11 l j (sch.obj (PN k d)) 0
        (fun W ⟨x⟩ => unit_of ((show W ⟶ PN k d from x) ≫ PNto k d) (IsUnit.mk0 _ hlk))
      have := vanish a9 e8 (l ^ 1) k (hu 1) (PNto k d) d (2 * d + 1) 0 (by omega)
      exact fun y => ((h 1 (2 * d)).2.1 y).1 (Subsingleton.elim _ _)
  obtain ⟨z, hz0⟩ := exists_ne (0 : V l (PN k d) (2 * d))
  obtain ⟨g, hg, hgU⟩ := hM k d t
  obtain rfl : U = g ⁻¹ᵁ Std k d := TopologicalSpace.Opens.ext (hU.trans hgU.symm)
  have h1 : ∀ j, Subsingleton (Ht (l ^ j) (sch.obj (Std k d).toScheme) (2 * d) 0) := fun j => by
    cases d with
    | zero =>
      refine hE a5 a9 _ _ ⟨fun x => ?_⟩ _ _
      obtain ⟨m, -⟩ := TopologicalSpace.Opens.mem_iSup.1 x.2
      exact m.elim0
    | succ e =>
      obtain ⟨f, hf⟩ := hJ k e
      have := vanish a9 e8 (l ^ j) k (hu j) (PNto k e) e (2 * (e + 1 : ℕ)) 0 (by omega)
      exact (hA b3 c4 (l ^ j) f hf (unit_of (PNto k e) (hu j)) 0 _).2.subsingleton
  have h2 : ∀ j, Subsingleton (HtL l j (sch.obj (g ⁻¹ᵁ Std k d).toScheme) (2 * d) 0) := fun j =>
    sub_iso (g ∣_ Std k d) _ _ (h := h1 j)
  have h3 : Subsingleton (V l (g ⁻¹ᵁ Std k d).toScheme (2 * d)) := inferInstance
  exact ⟨z, hz0, Subsingleton.elim _ _⟩

end LateralTheory.EtaleTrace.LPdCut

end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.PtCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TwZeroPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_sec_eq_of_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS y z (fun _ g hg => hP _ g hg)

theorem tz_twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen (q := q) 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  Loc U fun V g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem TwZero_of_primLoc (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hP : PrimLoc) : TwZero := by
  intro q _ U ζ ξ
  obtain ⟨-, -, T3⟩ := hTw q 0
  apply tz_sec_eq_of_loc
  obtain ⟨S, hS, hP'⟩ := hP q U ζ ξ
  refine ⟨S, hS, fun _ g hg => ?_⟩
  obtain ⟨a, ha⟩ := hP' _ g hg
  rw [T3, T3]
  exact (tz_twGen_eq_of_pow _ _ a ha).symm

end LateralTheory.EtaleTrace
end
end

