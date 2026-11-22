import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafRetractOfCoinduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.PicSpec

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  Eq.symm (NatTrans.naturality_apply φ.hom g.op x)

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (ψ : F ⟶ G) (φ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (Sec.map ψ x) = Sec.map (ψ ≫ φ) x := rfl

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  simpa [Sec.map] using this

theorem res_isZero {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs

theorem resι_d {R : Type} [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι res
  rw [Category.assoc, (injectiveResolution F).ι'.comm 0 1]
  simp

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  have h2 := congrArg (fun f => f.hom (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u))) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

theorem glMat_map {U V : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem generalLinearGroup_det_map_fin_one {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f M) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M) := by
  ext
  simp [RingHom.map_det]

theorem glMat_δ1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (((ofCat (glCat 1)).δ 1).app (op U) y) =
      glMat (((ofCat (glCat 1)).δ 0).app (op U) y) * glMat (((ofCat (glCat 1)).δ 2).app (op U) y) := by
  have h : ((show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 2) =
      (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 1 ≫
        (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 1 2 :=
    ComposableArrows.map'_comp _ 0 1 2
  exact h

theorem face_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) (i : Fin 3) :
    (L.app (op (SimplexCategory.mk 1))).app (op U) ((E.δ i).app (op U) x) =
      ((ofCat (glCat 1)).δ i).app (op U) ((L.app (op (SimplexCategory.mk 2))).app (op U) x) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.δ_naturality L i) (op U)) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  rw [NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x, glMat_map, generalLinearGroup_det_map_fin_one]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 0) * lineUnit L (x.face 2) := by
  unfold lineUnit Sx.face
  rw [face_nat, face_nat, face_nat, glMat_δ1, map_mul]

def fam {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ Gm).X s) U
  | 1, s, h, _, x => Sec.map ((res ℤ Gm).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
  | _, _, _, _, _ => 0

theorem fam_zero {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0})
    (x : Sx E 0 U) : fam L 0 s h U x = 0 := rfl

theorem fam_add_two {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -((p + 2 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E (p + 2) U) : fam L (p + 2) s h U x = 0 := rfl

theorem fam_one {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : fam L 1 0 h U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  simp [fam, Sec.map]

theorem fam_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0})
    (g : V ⟶ U) (x : Sx E p U) : Sec.res g (fam L p s h U x) = fam L p s h V (x.res g) := by
  match p with
  | 0 => simp [fam_zero]
  | 1 =>
    simp only [fam]
    rw [sec_map_res, sec_map_res, unitSec_res, lineUnit_res]
  | p + 2 => simp [fam_add_two]

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem ev_zero_cochain {E : Spc} {I : Cx ℤ} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains ℤ).obj E) I n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 0 0 p s h U x).2.2.1

theorem fam_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains ℤ).obj E) (res ℤ Gm) 1)
    (hα : ∀ p s h U x, ev α p s h U x = fam L p s h U x) : δ 1 2 α = 0 := by
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).2.2.1
  intro p t ht U x
  rw [ev_zero_cochain]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).1 x, hα, fam_zero, sec_map_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key : ev (δ 1 2 α) 1 1 ht U x = Sec.map ((res ℤ Gm).d 0 1) (ev α 1 0 (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ev α 0 1 (by simp) U (x.face i) :=
      (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, fam_zero, fam_one, smul_zero, Finset.sum_const_zero, add_zero, sec_map_comp, resι_d]
    rfl
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key : ev (δ 1 2 α) 2 0 ht U x = Sec.map ((res ℤ Gm).d (-1) 0) (ev α 2 (-1) (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ev α 1 0 (by simp) U (x.face i) :=
      (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, fam_one]
    rw [show fam L 2 (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face,
      unitSec_mul, sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  | p + 3 =>
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 (p + 2) (t - 1) t (by omega) ht x
    rw [key]
    simp only [hα, fam_add_two, sec_map_zero, zero_add, smul_zero, Finset.sum_const_zero]

theorem exists_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' ℤ (fam L) (fam_nat L)
  refine ⟨Cocycle.mk α 2 (by norm_num) (fam_cocycle L α hα), fun U x => ?_, fun U x => ?_⟩
  · exact (hα 0 1 _ U x).trans (fam_zero L 1 _ U x)
  · exact (hα 1 0 _ U x).trans (fam_one L _ U x)

theorem spec {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = picClass L ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨γ, h0, h1⟩ := exists_cocycle L
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
    ⟨_, γ, rfl, h0, h1⟩

theorem cocycle_ext {E : Spc} (γ γ' : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = ev γ'.1 0 1 (by simp) U x)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = ev γ'.1 1 0 (by simp) U x) : γ = γ' := by
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).2.2.1 _ _ fun p s h U x => ?_)
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    exact h0 U x
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact h1 U x
  | p + 2 =>
    have hZ := res_isZero Gm s (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.PicSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GrpTangentPt

variable {S : Scheme.{0}} {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

def sqZeroMapPt {M N : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N] (l : M →ₗ[R'] N) :
    Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' N)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' M)) ≫ x) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMapPt_comp {M N P : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
    [AddCommGroup P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
    (l : M →ₗ[R'] N) (l' : N →ₗ[R'] P) :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = sqZeroMapPt x (l' ∘ₗ l) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

abbrev epsScalePt (c : R') : epsPtR x ⟶ epsPtR x := sqZeroMapPt x (c • (LinearMap.id : R' →ₗ[R'] R'))

lemma epsScalePt_left (c : R') : (epsScalePt x c).left = spMap (epsScaleR c) := rfl

lemma sqZeroMapPt_comp_eq {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M]
    [IsCentralScalar R' M] (l : R' →ₗ[R'] M) (l' : M →ₗ[R'] R') :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = epsScalePt x (l' (l 1)) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

lemma epsScalePt_one : epsScalePt x (1 : R') = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

variable {G : Over S} [GrpObj G]

lemma epsScalePt_zero_comp {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x 0 ≫ w = 1 := by
  let π : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have e : (1 : epsPtR x ⟶ G) = π ≫ (1 : Over.mk x ⟶ G) := (comp_one π).symm
  rw [e]
  ext1
  rw [Over.comp_left, Over.comp_left, ← hw, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScalePt_add_comp (a b : R') {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x (a + b) ≫ w = (epsScalePt x a ≫ w) * (epsScalePt x b ≫ w) := by
  let i₁ := LinearMap.inl R' R' R'
  let i₂ := LinearMap.inr R' R' R'
  have key : sqZeroMapPt x (i₁ + i₂) ≫ w = (sqZeroMapPt x i₁ ≫ w) * (sqZeroMapPt x i₂ ≫ w) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R' R' R')).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom
        (fun z => ⟨1, one_pos, TrivSqZeroExt.map i₁ z, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
  have := congrArg (sqZeroMapPt x (a • LinearMap.fst R' R' R' + b • LinearMap.snd R' R' R') ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMapPt_comp_eq] at this
  simpa [i₁, i₂] using this

theorem tanadd : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left →
    ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left →
      wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  intro S G _ R' _ x w hw a b wa wb ha hb
  have ea : wa = epsScalePt x a ≫ w := Over.OverMorphism.ext ha
  have eb : wb = epsScalePt x b ≫ w := Over.OverMorphism.ext hb
  rw [ea, eb, ← epsScalePt_add_comp x a b hw]
  rfl

end GlobalTheory.GrpTangentPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderTraceFormNondegenerate
section
open NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTOrderTrace

theorem trace_tmul_padic {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (z : ℤ_[p]) (a : R) :
    Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (z ⊗ₜ a) = (Algebra.trace ℤ R a : ℤ_[p]) * z := by
  have h1 : (z ⊗ₜ a : ℤ_[p] ⊗[ℤ] R) = z • (1 ⊗ₜ a) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (1 ⊗ₜ a) =
      (Algebra.lmul ℤ R a).baseChange ℤ_[p] := by
    ext c
    simp
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, smul_eq_mul, mul_comm]
  rfl

theorem trace_form_padic_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (u : ℤ_[p] ⊗[ℤ] 𝓞 E),
    (∀ w, Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) (u * w) = 0) → u = 0 := by
  intro E _ _ p _ u hu
  classical
  let b0 := RingOfIntegers.basis E
  let b1 := b0.baseChange ℤ_[p]
  have h1 : Algebra.discr ℤ_[p] b1 = (NumberField.discr E : ℤ_[p]) := by
    rw [NumberField.discr, Algebra.discr_def, Algebra.discr_def]
    rw [show ((Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det : ℤ_[p]) =
      Int.castRingHom ℤ_[p] (Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [b1, b0, Algebra.traceForm_apply, trace_tmul_padic]
  have h0 : (NumberField.discr E : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hnd : (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b1]
    have : LinearMap.BilinForm.toMatrix b1 (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        Algebra.traceMatrix ℤ_[p] b1 := by
      ext i j; simp [Algebra.traceMatrix_apply]
    rw [this, ← Algebra.discr_def, h1]; exact h0
  exact hnd.1 u (fun w => by simpa [Algebra.traceForm_apply] using hu w)

theorem ringHom_padic_eq_algebraMap : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [Ring B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B]
    (f : ℤ_[p] →+* B), f = algebraMap ℤ_[p] B := by
  intro p _ B _ _ _ f
  ext c
  rw [← sub_eq_zero]
  set b := Module.Free.chooseBasis ℤ_[p] B
  have hdiv : ∀ n : ℕ, ∃ v : B, f c - algebraMap ℤ_[p] B c = (p : ℤ_[p]) ^ n • v := by
    intro n
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
    have hc : c = (c.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * μ := by rw [← hμ]; ring
    refine ⟨f μ - algebraMap ℤ_[p] B μ, ?_⟩
    conv_lhs => rw [hc]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
      map_natCast, map_natCast, map_natCast, map_natCast]
    noncomm_ring
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  obtain ⟨v, hv⟩ := hdiv ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)
  have hmem : b.repr (f c - algebraMap ℤ_[p] B c) i ∈
      Ideal.span {(p : ℤ_[p]) ^ ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)} := by
    rw [Ideal.mem_span_singleton]
    conv_rhs => rw [hv]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have := (PadicInt.mem_span_pow_iff_le_valuation _ hne _).1 hmem
  omega

theorem matrix_basis_repr {ι R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (m : ℕ) (b : Module.Basis ι R A)
    (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) (k : ι) :
    (b.matrix (Fin m) (Fin m)).repr M (i, j, k) = b.repr (M i j) k := by
  simp only [Module.Basis.matrix, Module.Basis.map_repr, Module.Basis.repr_reindex_apply, LinearEquiv.trans_apply]
  rfl

theorem trace_mulLeft_matrix_eq : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (m : ℕ) (Z : Matrix (Fin m) (Fin m) A),
    LinearMap.trace R (Matrix (Fin m) (Fin m) A) (LinearMap.mulLeft R Z) = (m : R) * Algebra.trace R A Z.trace := by
  intro R A _ _ _ _ _ m Z
  classical
  let b := Module.Free.chooseBasis R A
  rw [LinearMap.trace_eq_matrix_trace R (b.matrix (Fin m) (Fin m)), Matrix.trace, Matrix.trace, map_sum,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have key : ∀ j : Fin m, ∑ k, ((LinearMap.toMatrix (b.matrix (Fin m) (Fin m)) (b.matrix (Fin m) (Fin m)))
      (LinearMap.mulLeft R Z)).diag (i, j, k) = ∑ k, ((Algebra.leftMulMatrix b) (Z.diag i)).diag k := by
    intro j
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply, matrix_basis_repr, Algebra.leftMulMatrix_eq_repr_mul, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem trace_mulLeft_baseChange_eq_zero : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (R : Type) [CommRing R] (x : O),
    (∀ y, LinearMap.trace ℤ O (LinearMap.mulLeft ℤ (x * y)) = 0) →
    ∀ Y : R ⊗[ℤ] O, LinearMap.trace R (R ⊗[ℤ] O) (LinearMap.mulLeft R ((1 ⊗ₜ x) * Y)) = 0 := by
  intro O _ _ _ R _ x hx Y
  have hb : ∀ z : O, LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] z) = (LinearMap.mulLeft ℤ z).baseChange R := by
    intro z; ext c w; simp
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb' =>
    rw [mul_add, show LinearMap.mulLeft R ((1 ⊗ₜ x) * a + (1 ⊗ₜ x) * b) =
      LinearMap.mulLeft R ((1 ⊗ₜ x) * a) + LinearMap.mulLeft R ((1 ⊗ₜ x) * b) from
      map_add (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_add, ha, hb', add_zero]
  | tmul r y =>
    have h1 : ((1 : R) ⊗ₜ[ℤ] x) * (r ⊗ₜ y) = r • ((1 : R) ⊗ₜ[ℤ] (x * y)) := by
      simp [TensorProduct.smul_tmul']
    rw [h1, show LinearMap.mulLeft R (r • ((1 : R) ⊗ₜ[ℤ] (x * y))) =
      r • LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] (x * y)) from
      map_smul (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_smul, hb, LinearMap.trace_baseChange, hx, map_zero, smul_zero]

theorem inj_tmul (p : ℕ) [Fact p.Prime] (O : Type) [Ring O] [Module.Free ℤ O] (x : O)
    (h : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0) : x = 0 := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ ℤ_[p]) (RingHom.injective_int (algebraMap ℤ ℤ_[p]))
  have h1 : (Algebra.linearMap ℤ ℤ_[p]).rTensor O ((1 : ℤ) ⊗ₜ x) = 0 := by simpa using h
  have h2 := hinj (h1.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid ℤ O) h2

theorem trace_order_nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O),
    (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro p _ D x hx
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨φ⟩ := D.splitP
  set A' := ℤ_[p] ⊗[ℤ] 𝓞 D.F
  let Φ : (ℤ_[p] ⊗[ℤ] D.O) ≃+* Matrix (Fin D.m) (Fin D.m) A' :=
    (Algebra.TensorProduct.comm ℤ ℤ_[p] D.O).toRingEquiv.trans
      (φ.toRingEquiv.trans (Algebra.TensorProduct.comm ℤ (𝓞 D.F) ℤ_[p]).toRingEquiv.mapMatrix)
  have hψ : Φ.toRingHom.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] D.O)) =
      algebraMap ℤ_[p] (Matrix (Fin D.m) (Fin D.m) A') := ringHom_padic_eq_algebraMap p _ _
  have hΦs : ∀ (c : ℤ_[p]) (X : ℤ_[p] ⊗[ℤ] D.O), Φ (c • X) = c • Φ X := by
    intro c X
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    exact congrArg (fun f => f c) hψ
  let e : (ℤ_[p] ⊗[ℤ] D.O) ≃ₗ[ℤ_[p]] Matrix (Fin D.m) (Fin D.m) A' :=
    { Φ.toAddEquiv with map_smul' := hΦs }
  have hconj : ∀ W : ℤ_[p] ⊗[ℤ] D.O, LinearMap.mulLeft ℤ_[p] (Φ W) = e.conj (LinearMap.mulLeft ℤ_[p] W) := by
    intro W
    ext V
    simp [LinearEquiv.conj_apply, e]
  set Z := Φ (1 ⊗ₜ x)
  have hZ : ∀ Y, Algebra.trace ℤ_[p] A' (Z * Y).trace = 0 := by
    intro Y
    have h1 := trace_mulLeft_baseChange_eq_zero D.O ℤ_[p] x hx (Φ.symm Y)
    rw [← LinearMap.trace_conj' _ e, ← hconj, map_mul, RingEquiv.apply_symm_apply, trace_mulLeft_matrix_eq] at h1
    have hm : (D.m : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 D.m_pos.ne'
    exact (mul_eq_zero.1 h1).resolve_left hm
  have hZ0 : Z = 0 := by
    ext i j
    apply trace_form_padic_eq_zero D.F p
    intro a
    have := hZ (Matrix.single j i a)
    rwa [Matrix.trace_mul_single, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at this
  have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0 := by
    rw [← map_eq_zero_iff Φ Φ.injective]; exact hZ0
  exact inj_tmul p D.O x h1

end GlobalTheory.HTOrderTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafRetractOfCoinducedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_etaleSheaf_retract_of_coinduced : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I], ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  first | exact @GlobalTheory.EtC.CoindRetract.coind_retract | exact GlobalTheory.EtC.CoindRetract.coind_retract | (intros; apply GlobalTheory.EtC.CoindRetract.coind_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationAStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_ramification_of_height_one : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  first | (exact @GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (exact GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (intros; apply GlobalTheory.integralClosure_height_one_uniformizer_ramification  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace <;> assumption)
end

