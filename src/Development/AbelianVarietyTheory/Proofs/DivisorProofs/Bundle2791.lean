import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThickEndo

variable {S S' : Scheme.{0}}

theorem homEquiv_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Hom.mul_def,
    Hom.mul_def, Functor.obj.μ_def, ← comp_lift_assoc, ← Category.assoc (lift _ _),
    Functor.Monoidal.lift_μ, CategoryTheory.Functor.map_comp]

theorem homEquiv_symm_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : X ⟶ (Over.pullback φ).obj A) :
    ((Over.mapPullbackAdj φ).homEquiv X A).symm (a * b) =
      ((Over.mapPullbackAdj φ).homEquiv X A).symm a * ((Over.mapPullbackAdj φ).homEquiv X A).symm b := by
  apply ((Over.mapPullbackAdj φ).homEquiv X A).injective
  rw [homEquiv_mul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

theorem homEquiv_symm_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (q : Y ⟶ (Over.pullback t).obj A) :
    (((Over.mapPullbackAdj t).homEquiv Y A).symm q).left = q.left ≫ pullback.fst A.hom t := by
  have := homEquiv_left' t (((Over.mapPullbackAdj t).homEquiv Y A).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

variable {R : Type} [CommRing R] (I : Ideal R) {B : Type} [CommRing B] [IsLocalRing B]

theorem le_comap_of_mem_range {φ : CommRingCat.of R ⟶ CommRingCat.of B}
    (h : Spec.map φ (closedPoint B) ∈ Set.range (thick R I 0)) :
    I ≤ (maximalIdeal B).comap φ.hom := by
  obtain ⟨y, hy⟩ := h
  intro a ha
  have h1 : a ∈ ((thick R I 0) y).asIdeal := by
    show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)]
    exact zero_mem _
  rw [hy] at h1
  exact h1

def lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ.hom
    ((Ideal.pow_right_mono hI (e + 1)).trans (Ideal.le_comap_pow _ _))))

variable {I}

theorem lev_thick (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    lev I φ hI e ≫ thick R I e = thick B (maximalIdeal B) e ≫ Spec.map φ := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem adicLevelMap_lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom)
    (e : ℕ) : adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ lev I φ hI (e + 1) =
      lev I φ hI e ≫ thickTrans R I e := by
  rw [lev, lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact Ideal.Quotient.ringHom_ext rfl

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

section Main

variable {R : Type} [CommRing R] {I : Ideal R} {G : Over (Sp R)} [GrpObj G] {B : Type} [CommRing B]
  [IsLocalRing B] {φ : CommRingCat.of R ⟶ CommRingCat.of B} (hI : I ≤ (maximalIdeal B).comap φ.hom)

abbrev lvl (e : ℕ) : Over (Sp (R ⧸ I ^ (e + 1))) := Over.mk (lev I φ hI e)

def incl (e : ℕ) : (Over.map (thick R I e)).obj (lvl hI e) ⟶ Over.mk (Spec.map φ) :=
  Over.homMk (thick B (maximalIdeal B) e) (lev_thick φ hI e).symm

def red (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) : lvl hI e ⟶ thickObj R I e G :=
  (Over.mapPullbackAdj (thick R I e)).homEquiv (lvl hI e) G (incl hI e ≫ x)

theorem red_fst (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left :=
  homEquiv_left' _ _

theorem red_snd (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.snd G.hom (thick R I e) = lev I φ hI e :=
  Over.w (red hI e x)

omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [GrpObj G] in
theorem thickMap_snd (e : ℕ) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem red_succ (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ (red hI (e + 1) x).left =
      (red hI e x).left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · rw [Category.assoc, red_fst, Category.assoc, thickMap_fst, red_fst]
    exact adicLevelMap_ι_assoc (maximalIdeal B) (Nat.le_succ (e + 1)) x.left
  · rw [Category.assoc, red_snd, Category.assoc, thickMap_snd, ← Category.assoc, red_snd, adicLevelMap_lev]

variable (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G)

def fam (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ G.left :=
  (red hI e x ≫ b e).left ≫ pullback.fst G.hom (thick R I e)

variable {b}

theorem fam_adic (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : IsAdicFamily (maximalIdeal B) (fam hI b x) := fun e => by
  simp only [fam, Over.comp_left, Category.assoc]
  rw [← Category.assoc (adicLevelMap _ _), red_succ, Category.assoc, ← Category.assoc (thickMap R I e G),
    hb, Category.assoc, thickMap_fst]

variable (b) in
theorem fam_over (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    fam hI b x e ≫ G.hom = adicLevelι (maximalIdeal B) (e + 1) ≫ Spec.map φ := by
  have hw : (b e).left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w (b e)
  simp only [fam, Over.comp_left, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((b e).left), hw, ← Category.assoc, red_snd, lev_thick]

variable [IsAdicComplete (maximalIdeal B) B]

theorem exists_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : ∃ g : Sp B ⟶ G.left, g ≫ G.hom = Spec.map φ ∧
      ∀ e, adicLevelι (maximalIdeal B) (e + 1) ≫ g = fam hI b x e :=
  (existsUnique_over_of_isAdicFamily (Spec.map φ) G.hom (fam_adic hI hb x) (fam_over hI b x)).exists

def lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : Over.mk (Spec.map φ) ⟶ G :=
  Over.homMk (exists_lim hI hb x).choose (exists_lim hI hb x).choose_spec.1

theorem lim_level (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    thick B (maximalIdeal B) e ≫ (lim hI hb x).left = fam hI b x e :=
  (exists_lim hI hb x).choose_spec.2 e

theorem incl_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    incl hI e ≫ lim hI hb x = ((Over.mapPullbackAdj (thick R I e)).homEquiv _ G).symm (red hI e x ≫ b e) := by
  apply Over.OverMorphism.ext
  rw [homEquiv_symm_left', Over.comp_left]
  exact lim_level hI hb x e

theorem lim_mul (hmon : ∀ e, IsMonHom (b e))
    (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x y : Over.mk (Spec.map φ) ⟶ G) : lim hI hb (x * y) = lim hI hb x * lim hI hb y := by
  have he : ∀ e, incl hI e ≫ lim hI hb (x * y) = incl hI e ≫ (lim hI hb x * lim hI hb y) := by
    intro e
    have := hmon e
    rw [comp_mul, incl_lim, incl_lim, incl_lim, red, comp_mul, homEquiv_mul', mul_comp, homEquiv_symm_mul']
    rfl
  exact Over.OverMorphism.ext (hom_ext_of_isHausdorff (maximalIdeal B) fun e => congrArg (·.left) (he e))

end Main

end GlobalTheory.ThickEndo

open GlobalTheory.ThickEndo in

theorem GlobalTheory.exists_mul_map_points_of_thickEndo : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  intro R _ I G _ b hmon hb B _ _ _ s hs
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hI := le_comap_of_mem_range I hs
  refine ⟨lim hI hb, fun x y => lim_mul hI hmon hb x y, fun x e => ⟨(red hI e x).left, red_fst hI e x, ?_⟩⟩
  rw [lim_level hI hb x e]
  simp only [fam, Over.comp_left, Category.assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_finiteType_int_of_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  first | exact @GlobalTheory.RatModel.exists_affineOpen_finiteType_int | exact GlobalTheory.RatModel.exists_affineOpen_finiteType_int | (intros; apply GlobalTheory.RatModel.exists_affineOpen_finiteType_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  first | exact @GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | exact GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | (intros; apply GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KodairaNefBig

theorem isAffine_of_dim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) :
    IsAffine X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : U = ⊤ := eq_top_iff.2 fun x _ => by
    rw [GlobalTheory.FlagQ.eq_genericPoint_of_krullDim_zero h x]; exact hmem
  subst hU'
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso X.topIso.inv

theorem prod_le {d : ℕ} (q : ℤ) (hq : 1 ≤ q) (n : Fin (d + 1) → Fin 2 → ℤ)
    (h0 : ∀ j, 0 ≤ n 0 j ∧ n 0 j ≤ 2) (hs : ∀ (i : Fin d) j, 0 ≤ n i.succ j ∧ n i.succ j ≤ q)
    (a : Fin (d + 1) → Fin 2) : ∏ i, n i (a i) ≤ 2 * q ^ d := by
  rw [Fin.prod_univ_succ]
  have hp : ∏ i : Fin d, n i.succ (a i.succ) ≤ ∏ _i : Fin d, q :=
    Finset.prod_le_prod (fun i _ => (hs i _).1) fun i _ => (hs i _).2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact mul_le_mul (h0 _).2 hp (Finset.prod_nonneg fun i _ => (hs i _).1) (by norm_num)

end GlobalTheory.KodairaNefBig

open GlobalTheory.KodairaNefBig in

theorem GlobalTheory.exists_ample_add_eff_of_isNef_isBig : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  intro hNN X _ _ p hp N hN hnef hbig
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨D, hD, -⟩ := hbig.growth
  cases D with
  | zero =>
    have := isAffine_of_dim_zero (X := X) (by simpa using hD)
    refine ⟨1, N, hN, 0, one_pos, isAmpleLB_of_isAffine hN, CartierDiv.eff_zero, ?_⟩
    rw [one_smul, ← toPic_apply, map_zero, add_zero]
  | succ d =>
    have := isNoetherian_of_isProjOver hp
    have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℂ X) (GlobalTheory.structureModule X)
      hp' (d := d + 1) (by rw [QCoh.suppDim_structureModule]; exact hD.le)
    let P : Fin 2 → LB X := ![N, A]
    have hPn : ∀ j, IsNef ℂ (P j) := fun j => by
      fin_cases j
      exacts [hnef, hA.isNef]
    have hP : ∀ j, (P j).IsLB := fun j => (hPn j).isLB
    have hI : ∀ a : Fin (d + 1) → Fin 2, 0 ≤ interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
      fun a => hNN.1.interNum_nonneg hp' hD fun i => hPn (a i)
    set S : ℤ := ∑ a : Fin (d + 1) → Fin 2, interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hI a
    have hT : 0 < topSelfIntersection ℂ N (d + 1) := (hNN.2.2.isBig_iff hp' hD hnef).1 hbig
    set q : ℕ := 2 * (d + 1) * S.toNat + 1 with hqdef
    have hqS : (q : ℤ) = 2 * (d + 1) * S + 1 := by
      rw [hqdef]; push_cast [Int.toNat_of_nonneg hS0]; ring
    have hq1 : (1 : ℤ) ≤ q := by rw [hqS]; nlinarith
    let L : LB X := tens A (lbPow N q)
    have hL : IsAmpleLB L := IsAmpleLB.tens_of_isNef hNN ℂ X p hp A _ hA (hnef.pow hA q)
    let B : LB X := lbPow A 2
    have hB : IsAmpleLB B := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
    let M : LB X := tens (lbPow N q) (dual A)
    have hM : M.IsLB := isLB_tens (isLB_lbPow hN q) (isLB_dual hA.isLB)
    have hclsL : cls L hL.isLB = (q : ℤ) • cls N hN + cls A hA.isLB := by
      rw [cls_tens hA.isLB (isLB_lbPow hN q), cls_lbPow hN, natCast_zsmul, add_comm]
    have hclsB : cls B hB.isLB = (2 : ℤ) • cls A hA.isLB := by
      rw [cls_lbPow hA.isLB]; norm_cast
    have hclsM : cls M hM = (q : ℤ) • cls N hN - cls A hA.isLB := by
      rw [cls_tens (isLB_lbPow hN q) (isLB_dual hA.isLB), cls_lbPow hN, cls_dual hA.isLB,
        natCast_zsmul, sub_eq_add_neg]
    have e : cls L hL.isLB = cls M hM + cls B hB.isLB := by
      rw [hclsL, hclsM, hclsB]; abel

    have e₁ := hV.interNum_of_cls_eq_sum hP (Q := fun _ => L) (fun _ => hL.isLB)
      (fun _ => ![(q : ℤ), 1]) (fun _ => by
        rw [Fin.sum_univ_two, hclsL]
        simp [P])
    have hlow : (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) ≤ topSelfIntersection ℂ L (d + 1) := by
      rw [topSelf_def ℂ L, e₁]
      have hnn : ∀ a : Fin (d + 1) → Fin 2,
          0 ≤ (∏ i, (![(q : ℤ), 1] : Fin 2 → ℤ) (a i)) * interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
        fun a => mul_nonneg (Finset.prod_nonneg fun i _ => by
          rcases Fin.exists_fin_two.1 ⟨a i, rfl⟩ with h | h <;> rw [h] <;> simp <;> omega) (hI a)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a)
        (Finset.mem_univ (fun _ => (0 : Fin 2))))
      simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

    let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![0, 2] (fun _ => ![(q : ℤ), 1])
    have e₂ := hV.interNum_of_cls_eq_sum hP (Q := Fin.cons B (fun _ : Fin d => L))
      (Fin.cases hB.isLB fun _ => hL.isLB) n (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_zero, n]
          rw [hclsB]
          simp [P]
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_succ, n]
          rw [hclsL]
          simp [P])
    have hup : interNum ℂ (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
        ≤ 2 * (q : ℤ) ^ d * S := by
      rw [e₂, hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hI a)
      refine prod_le (q : ℤ) hq1 n (fun j => ?_) (fun i j => ?_) a
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n]
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n] <;> omega
    have hineq : ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
        (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection ℂ L (d + 1) := by
      have hqd : (0 : ℤ) < (q : ℤ) ^ d := pow_pos (by omega) d
      have hd1 : (0 : ℤ) ≤ (d : ℤ) + 1 := by positivity
      calc ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
            (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
          ≤ ((d : ℤ) + 1) * (2 * (q : ℤ) ^ d * S) := mul_le_mul_of_nonneg_left hup hd1
        _ = (q : ℤ) ^ d * (2 * (d + 1) * S) := by ring
        _ < (q : ℤ) ^ d * q := mul_lt_mul_of_pos_left (by rw [hqS]; omega) hqd
        _ = (q : ℤ) ^ (d + 1) * 1 := by ring
        _ ≤ (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ topSelfIntersection ℂ L (d + 1) := hlow
    obtain ⟨r, hr, hs⟩ := exists_hasNonzeroSec_pow_of_ample_sub_ample ℂ X hp' d hD.le L B M hL hB hM
      e hineq
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨q * r, lbPow A r, isLB_lbPow hA.isLB r, divOfSec (isLB_lbPow hM r) s hs,
      Nat.mul_pos (Nat.succ_pos _) hr, (isAmpleLB_pow_iff hA.isLB hr).2 hA,
      eff_divOfSec_of_sec _ s hs, ?_⟩
    rw [← toPic_apply, (presents_divOfRatSec _ (isRatSec_ratOfSec s hs)).toPic_eq,
      cls_lbPow hA.isLB, cls_lbPow hM, hclsM]
    first
      | module
      | (simp only [← natCast_zsmul, smul_sub, smul_smul, Nat.cast_mul]; rw [mul_comm (r : ℤ)]; abel)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerateStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  first | exact @GlobalTheory.IdGenRat.exists_sections_vanish_generate | exact GlobalTheory.IdGenRat.exists_sections_vanish_generate | (intros; apply GlobalTheory.IdGenRat.exists_sections_vanish_generate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleNefSmall

theorem mem_nonzeroLocus_secPow_one {X : Scheme.{0}} {L : LB X} (s : L.Sec) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) : x ∈ Out.nonzeroLocus (Cartier.secPow s 1) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  show x ∈ X.basicOpen (resG X (Cartier.lbPow_U L 1 (fun _ => i)).le (s.f i) ^ 1)
  rw [pow_one]
  unfold resG
  rw [Scheme.basicOpen_res]
  exact ⟨(Cartier.lbPow_U L 1 (fun _ => i)).ge (X.basicOpen_le _ hi), hi⟩

end GlobalTheory.AmpleNefSmall

namespace GlobalTheory.AmpleNefSmall

open ProjSpace in

theorem exists_ample_nef_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∃ A : HermLB p, IsAmpleLB A.B ∧ A.IsNef D ∧ ∃ s ∈ A.smallSec, s ≠ 0 := by
  intro hAr k _ X _ p D hX
  obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
  have := hj
  have := hX.finite
  have := isProper_str k N
  have : IsProper p := hjp ▸ inferInstance
  let B : LB X := (O1 k N).pull j
  have hB : B.IsLB := LB.isLB_pull (O1_isLB k N) j
  let c : Fin (N + 1) → B.Sec := fun a => Cartier.secPull (coord k N a) j
  have hc : ⨆ a, Out.nonzeroLocus (c a) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord k N).ge (Opens.mem_top (j x)))
    refine Opens.mem_iSup.2 ⟨a, ?_⟩
    show x ∈ Out.nonzeroLocus (Cartier.secPull (coord k N a) j)
    rw [Cartier.nonzeroLocus_secPull]
    exact ha
  let A₀ : HermLB p := HermLB.fs p hB c hc (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  have hsmall : ∀ a, c a ∈ A₀.smallSec := by
    intro a σ y
    have e (a) : Weight.combVal p σ c 1 a = secVal _ σ (c a) := by
      simp [Weight.combVal, Matrix.one_apply]
    refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := hB) (he := fun a => e a ▸ secVal_mem _)
      (h := Weight.noCommonZero_combVal hc (M := 1) (by simp)) y)
    exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
      (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))
  have hgen : ∀ x : X, CharZero (X.residueField x) →
      ∃ i, x ∈ Out.nonzeroLocus (Cartier.secPow (c i) 1 : (A₀.pow 1).B.Sec) := fun x _ =>
    have ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top x))
    ⟨a, mem_nonzeroLocus_secPow_one _ ha⟩
  obtain ⟨t, ht, hnef⟩ := GlobalTheory.NefOfGen.nef_of_gen hAr k X p D hX A₀ 1 (N + 1)
    (fun i => Cartier.secPow (c i) 1) le_rfl hgen (HermLB.semiPos_fs hB c hc _ _ _)
    (ProjModel.nefFib_of_isAmpleLB A₀ hA)
  refine ⟨A₀.shift (fun _ => t) fun _ => rfl, hA, hnef, ?_⟩
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top (genericPoint X)))
  refine ⟨c a, fun σ y => ?_, fun h0 => ?_⟩
  · refine le_of_eq_of_le (HermLB.nsq_shift A₀ (fun _ => t) (fun _ => rfl) (secVal p σ (c a)) y) ?_
    have h1 := hsmall a σ y
    have h2 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 := Weight.nsq_nonneg (A₀.φ σ) (secVal p σ (c a)) y
    nlinarith
  · have e : c a = (0 : B.Sec) := h0
    rw [e] at ha
    simp [Out.nonzeroLocus] at ha

end GlobalTheory.AmpleNefSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.ExpFrame

theorem exists_isFactorAH_frame_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg e he M hM
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, hu, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  exact ⟨u, Hm, χ, fun z => by rw [hu, hu₀], hAH⟩

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatementStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExistsFrameStatement : ExFrameSt := by
  first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)
end

