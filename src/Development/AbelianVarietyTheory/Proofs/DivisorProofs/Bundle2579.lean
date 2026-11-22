import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.LieRel

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [QuasiSeparated G.hom]

theorem exists_prod (l : List (LieG G)) :
    ∃ z : LieG G, z.1 = (l.map fun x => x.1).prod ∧ tangent z = (l.map tangent).sum := by
  induction l with
  | nil =>
    have h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1 := MonObj.comp_one _
    refine ⟨⟨1, h1⟩, rfl, ?_⟩
    have h2 := tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)
    have h3 : (⟨_, OmegaGlobal.fst_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ :=
      Subtype.ext (_root_.mul_one _)
    rw [h3] at h2
    simpa using h2
  | cons x l ih =>
    obtain ⟨z, hz, hz'⟩ := ih
    refine ⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hz]
    · rw [tangent_mul, hz', List.map_cons, List.sum_cons]

theorem isLieComb_of_tangent {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G)
    (h : tangent w = ∑ m, cst R (a m) • tangent (v m)) : IsLieComb a (fun m => (v m).1) w.1 := by
  let u : Fin n → LieG G := fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩
  obtain ⟨z, hz, hz'⟩ := exists_prod (List.ofFn u)
  have e : w = z := tangent_injective R G (by
    rw [h, hz', List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)
  refine ⟨fun m => (u m).1, fun m => ?_, ?_⟩
  · have ha : (dualScale (a m)).toRingHom = epsScaleR (a m) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v m).1.left) ha
  · rw [e, hz, List.map_ofFn]
    rfl

theorem exists_matrix {g : ℕ} {e e' : Fin g → Γ(omega G, ⊤)} (he : IsFrame e) (he' : IsFrame e') (v v' : Fin g → LieG G)
    (hv : ∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0)
    (hv' : ∀ j k, dualApp (tangent (v' j)) le_top (e' k) = if j = k then 1 else 0) :
    ∃ M : Matrix (Fin g) (Fin g) R, (∀ j, IsLieComb (M j) (fun m => (v' m).1) (v j).1) ∧
      M.det = (Scheme.ΓSpecIso (.of R)).hom (he.detUnit he' le_rfl le_rfl : Γ(Sp R, ⊤)) := by
  refine ⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩
  · refine isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)
    rw [resM_self, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]
    simp
  · have hc (j : Fin g) : tangent (v j) = he.coord j := he.dual_ext le_rfl fun k => by
      rw [he.dualApp_coord_frame, resM_self]
      exact (hv j k).trans (by simp only [eq_comm])
    rw [IsFrame.val_detUnit, Module.Basis.det_apply]
    refine Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm
    congr 1
    ext j m
    rw [hc, RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]
    rfl

end Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {g : ℕ}

theorem pfr_eq (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) :
    pfr c ξ hc = fun k => (omegaBase (isGrpPullback_pullback G ξ)).app ⊤
      (resM _ hc (QCoh.pullbackSections ξ (omega G) (le_refl (ξ ⁻¹ᵁ c.U)) (c.e k))) :=
  funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm

theorem isFrame_pfr (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) : IsFrame (pfr c ξ hc) := by
  rw [pfr_eq]
  exact ((c.isFrame.pullback ξ).res hc).map_iso _

theorem val_detUnit_pfr (c c' : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (hc' : ⊤ ≤ ξ ⁻¹ᵁ c'.U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ((isFrame_pfr c ξ hc).detUnit (isFrame_pfr c' ξ hc') le_rfl le_rfl : Γ(Sp R, ⊤)) =
      (ξ.appLE (c.U ⊓ c'.U) ⊤ h).hom (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right : Γ(S, c.U ⊓ c'.U)) := by
  have key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f)
      (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') :
      he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl := by
    subst h₁ h₂; rfl
  rw [key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ)))
    (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'),
    IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame.pullback ξ).res hc'),
    IsFrame.detUnit_res (c.isFrame.pullback ξ) (c'.isFrame.pullback ξ)]
  exact c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h

theorem genPt_appLE [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    (Scheme.ΓSpecIso (.of (FF S))).hom (((genPt S).appLE U ⊤ (genPt_le U hU)).hom a) =
      S.presheaf.germ U (genericPoint S) hU a := by
  have k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := genPt_le U hU
  have e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k =
      S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE k).op :
      Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  have e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫
      (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($e' a)

theorem lieRel : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  intro S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩
  choose v hv hv₁ using hy
  choose v' hv' hv₁' using hy'
  have : QuasiSeparated (bG G (genPt S)).hom :=
    MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance
  obtain ⟨M, hM, hd⟩ := exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'
  obtain rfl : (fun j => (v j).1) = y := funext hv
  obtain rfl : (fun j => (v' j).1) = y' := funext hv'
  refine ⟨M, hM, hd.trans ?_⟩
  rw [val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]
  exact genPt_appLE _ h1 _

end GlobalTheory.KeyVals.LieRel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.PrimPic

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

def pt (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x : T ⟶ B) : GlobalTheory.CechPic.Pic T.left := GlobalTheory.CechPic.pull x.left c

def lam (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x y : T ⟶ B) : GlobalTheory.CechPic.Pic T.left :=
  pt c (x * y) - pt c x - pt c y + pt c 1

theorem lam_mul_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (x x' y : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) (x * x') y =
      lam (GlobalTheory.CechPic.cls M.L M.isLB) x y + lam (GlobalTheory.CechPic.cls M.L M.isLB) x' y := by
  have ht := DVR.pullGen_isGen _ _ _ _ cub.isGen (lift x (lift x' y)).left
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb M.isLB _ _)).2 ⟨_, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb M.isLB] at h0
  have e := prod_cub x x' y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ B.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have e' := congrArg (fun u => FreeAbelianGroup.lift (fun ψ => GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls M.L M.isLB))
    (Multiplicative.toAdd u)) e
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv, map_sum, map_zsmul, map_add, map_neg,
    FreeAbelianGroup.lift_apply_of] at e'
  have e'' := e'.symm.trans h0
  simp only [lam, pt]
  linear_combination (norm := abel) e''

theorem lam_comm (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (x y : T ⟶ B) : lam c x y = lam c y x := by
  simp only [lam]; rw [_root_.mul_comm x y]; abel

theorem lam_one_left (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (y : T ⟶ B) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

def lamHom (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (y : T ⟶ B) :
    Additive (T ⟶ B) →+ GlobalTheory.CechPic.Pic T.left :=
  AddMonoidHom.mk' (fun x => lam (GlobalTheory.CechPic.cls M.L M.isLB) (Additive.toMul x) y)
    (fun a b => lam_mul_left M cub (Additive.toMul a) (Additive.toMul b) y)

theorem lam_prod_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} {Ix : Type} [Fintype Ix]
    (s : Ix → (T ⟶ B)) (m : Ix → ℤ) (y : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) (∏ i, s i ^ m i) y = ∑ i, m i • lam (GlobalTheory.CechPic.cls M.L M.isLB) (s i) y := by
  have e := map_sum (lamHom M cub y) (fun i => m i • Additive.ofMul (s i)) Finset.univ
  simp only [map_zsmul] at e
  refine Eq.trans ?_ e
  show _ = lam _ (Additive.toMul (∑ i, m i • Additive.ofMul (s i))) y
  congr 1

theorem lam_prod_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} {Ix : Type} [Fintype Ix]
    (x : T ⟶ B) (s : Ix → (T ⟶ B)) (m : Ix → ℤ) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) x (∏ i, s i ^ m i) = ∑ i, m i • lam (GlobalTheory.CechPic.cls M.L M.isLB) x (s i) := by
  rw [lam_comm, lam_prod_left M cub]
  simp only [lam_comm _ (s _) x]

theorem lam_mul_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (x y y' : T ⟶ B) :
    lam (GlobalTheory.CechPic.cls M.L M.isLB) x (y * y') =
      lam (GlobalTheory.CechPic.cls M.L M.isLB) x y + lam (GlobalTheory.CechPic.cls M.L M.isLB) x y' := by
  rw [lam_comm, lam_mul_left M cub, lam_comm _ y, lam_comm _ y']

def bil (c : GlobalTheory.CechPic.Pic B.left) {T : Over S} (N : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → (T ⟶ B)) :
    GlobalTheory.CechPic.Pic T.left :=
  ∑ a, ∑ b, N a b • lam c (s a) (t b)

theorem bil_left (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (N m : Matrix (Fin 8) (Fin 8) ℤ)
    (s t : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) N (fun a => ∏ k, s k ^ m a k) t =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (m.transpose * N) s t := by
  simp only [bil, lam_prod_left M cub, Matrix.mul_apply, Matrix.transpose_apply, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [_root_.mul_comm]

theorem bil_right (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (N m : Matrix (Fin 8) (Fin 8) ℤ)
    (s t : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) N s (fun b => ∏ k, t k ^ m b k) =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (N * m) s t := by
  simp only [bil, lam_prod_right M cub, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem bil_mul (M : RigLB B) (cub : CubicalStr B M) {T : Over S} (W : Matrix (Fin 8) (Fin 8) ℤ)
    (x y : Fin 8 → (T ⟶ B)) :
    bil (GlobalTheory.CechPic.cls M.L M.isLB) W (x * y) (x * y) - bil (GlobalTheory.CechPic.cls M.L M.isLB) W x x -
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W y y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W 1 1 =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (W + W.transpose) x y := by
  have h1 : bil (T := T) (GlobalTheory.CechPic.cls M.L M.isLB) W 1 1 = 0 := by
    simp [bil, lam_one_left]
  have h2 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x = bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y := by
    simp only [bil, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [lam_comm _ (y _)]
  have h3 : bil (GlobalTheory.CechPic.cls M.L M.isLB) W (x * y) (x * y) = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x x +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y + bil (GlobalTheory.CechPic.cls M.L M.isLB) W y x +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W y y := by
    simp only [bil, Pi.mul_apply, lam_mul_left M cub, lam_mul_right M cub, smul_add, Finset.sum_add_distrib]
    abel
  have h4 : bil (GlobalTheory.CechPic.cls M.L M.isLB) (W + W.transpose) x y = bil (GlobalTheory.CechPic.cls M.L M.isLB) W x y +
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W.transpose x y := by
    simp only [bil, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  rw [h1, h3, h4, ← h2]; abel

def preH {G T T' : Over S} [GrpObj G] (ρ : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one ρ
  map_mul' x y := MonObj.comp_mul ρ x y

theorem cechPicard_pullback_e8Bundle_class (W : Matrix (Fin 8) (Fin 8) ℤ) {A : Over S} [GrpObj A] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (hL : L.IsLB) (M : RigLB B) (h : IsE8WeightedBundle W pr L M.L) {T : Over S} (s : T ⟶ A) :
    GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.cls L hL) =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) W (fun a => s ≫ pr a) (fun b => s ≫ pr b) := by
  rw [(GlobalTheory.CechPic.cls_eq_iff hL (LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2)))).2 h,
    GlobalTheory.CechPic.cls_linComb M.isLB, map_sum]
  have hm : ∀ x y : A ⟶ B, s.left ≫ (x * y).left = ((s ≫ x) * (s ≫ y)).left := fun x y => by
    rw [← Over.comp_left, MonObj.comp_mul]
  have h1 : s.left ≫ (1 : A ⟶ B).left = (1 : T ⟶ B).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have hx : ∀ x : A ⟶ B, s.left ≫ x.left = (s ≫ x).left := fun x => (Over.comp_left _ _ _ s x).symm
  have v0 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 0 = p := fun _ _ _ _ => rfl
  have v1 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 1 = q := fun _ _ _ _ => rfl
  have v2 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 2 = r := fun _ _ _ _ => rfl
  have v3 : ∀ {α : Type} (p q r t : α), ![p, q, r, t] 3 = t := fun _ _ _ _ => rfl
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, Fintype.sum_prod_type, Fin.sum_univ_four, bil, lam, pt, lamPts,
    negε, v0, v1, v2, v3, hm, h1, hx]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_add, smul_sub, mul_neg, _root_.mul_one, neg_neg, neg_smul]
  abel

theorem cls_cube2 {A : Over S} [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) {T : Over S}
    (u v : T ⟶ A) (hc : (cubeLB A ![u, v] L).IsLB) :
    GlobalTheory.CechPic.cls (cubeLB A ![u, v] L) hc =
      GlobalTheory.CechPic.pull (u * v).left (GlobalTheory.CechPic.cls L hL) - GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls L hL) -
        GlobalTheory.CechPic.pull v.left (GlobalTheory.CechPic.cls L hL) + GlobalTheory.CechPic.pull (1 : T ⟶ A).left (GlobalTheory.CechPic.cls L hL) := by
  refine (GlobalTheory.CechPic.cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum A ![u, v] I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) hc).trans ?_
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I => ((-1 : ℤ) ^ (2 - I.card)) •
    GlobalTheory.CechPic.pull (psum A ![u, v] I).left (GlobalTheory.CechPic.cls L hL)) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum A ![u, v] ∅ = 1 := rfl
  have p₁ : psum A ![u, v] {0} = u := _root_.mul_one u
  have p₂ : psum A ![u, v] {1} = v := _root_.mul_one v
  have p₃ : psum A ![u, v] {0, 1} = u * v := congrArg (u * ·) (_root_.mul_one v)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [one_smul, neg_smul]
  abel

theorem cube_class_e8Bundle_eighth_power (W : Matrix (Fin 8) (Fin 8) ℤ) {A : Over S} [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (A ⟶ B))
    (hpr : ∀ a, IsMonHom (pr a)) (L : LB A.left) (hL : L.IsLB) (M : RigLB B) (cub : CubicalStr B M)
    (h : IsE8WeightedBundle W pr L M.L) {T : Over S} (u v : T ⟶ A) (hc : (cubeLB A ![u, v] L).IsLB) :
    GlobalTheory.CechPic.cls (cubeLB A ![u, v] L) hc =
      bil (GlobalTheory.CechPic.cls M.L M.isLB) (e8 W) (fun a => u ≫ pr a) (fun b => v ≫ pr b) := by
  rw [cls_cube2 L hL u v hc, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h, cechPicard_pullback_e8Bundle_class W pr L hL M h,
    cechPicard_pullback_e8Bundle_class W pr L hL M h]
  have hm : (fun a => (u * v) ≫ pr a) = (fun a => u ≫ pr a) * (fun a => v ≫ pr a) := funext fun a => by
    haveI := hpr a; exact MonObj.mul_comp u v (pr a)
  have h1 : (fun a => (1 : T ⟶ A) ≫ pr a) = 1 := funext fun a => by
    haveI := hpr a; exact MonObj.one_comp (pr a)
  rw [hm, h1]
  exact bil_mul M cub W _ _

theorem e8_transpose' (W : Matrix (Fin 8) (Fin 8) ℤ) : (e8 W).transpose = e8 W := by
  simp only [e8, Matrix.transpose_add, Matrix.transpose_transpose]; exact add_comm _ _

theorem actMat_zero (W : Matrix (Fin 8) (Fin 8) ℤ) : actMat W 0 = (e8 W).adjugate * W := rfl
theorem actMat_one (W : Matrix (Fin 8) (Fin 8) ℤ) : actMat W 1 = (e8 W).adjugate * W.transpose := rfl

theorem mat_adj (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    (actMat W 0).transpose * e8 W = e8 W * actMat W 1 := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, actMat_one, Matrix.transpose_mul, Matrix.adjugate_transpose, e8_transpose', Matrix.mul_assoc,
    Matrix.adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one, Matrix.one_mul]

theorem mat_prim (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) : e8 W * actMat W 0 = W := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, ← Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.one_mul]

theorem mat_sum (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) : actMat W 0 + actMat W 1 = 1 := by
  have hd : (e8 W).det = 1 := hW.2
  rw [actMat_zero, actMat_one, ← Matrix.mul_add]
  show (e8 W).adjugate * e8 W = 1
  rw [Matrix.adjugate_mul, hd, one_smul]

theorem e8_act_endomorphism_prod_eq_id : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  intro W hW gQ K _ P' B _ _ M pr hF hP hE act hact hacts
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  have hmon : ∀ a, IsMonHom (pr a) := hP.1
  have hpre : ∀ {T : Over (Sp K)} (s : T ⟶ P'.A) (i : Fin 2),
      (fun a => (s ≫ act i) ≫ pr a) = fun a => ∏ k, (s ≫ pr k) ^ actMat W i a k := fun s i => funext fun a => by
    rw [Category.assoc, hacts i a]
    exact (map_prod (preH (G := B) s) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (preH (G := B) s) _ _)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := hP.2 P'.A pr
    have h1 : ∀ a, (act 0 * act 1) ≫ pr a = pr a := by
      intro a
      haveI := hmon a
      rw [MonObj.mul_comp, hacts 0 a, hacts 1 a, ← Finset.prod_mul_distrib]
      have hs := mat_sum W hW
      rw [Finset.prod_eq_single a]
      · rw [← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_eq, zpow_one]
      · intro b _ hb
        rw [← zpow_add, ← Matrix.add_apply, hs, Matrix.one_apply_ne (Ne.symm hb), zpow_zero]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    exact (hx _ h1).trans (hx _ fun a => Category.id_comp _).symm
  · have hc1 : (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    have hc2 : (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hc1 hc2).1 ?_
    rw [cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE, cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE,
      hpre (fst P'.A P'.A) 0, hpre (snd P'.A P'.A) 1, bil_left M cub, bil_right M cub, mat_adj W hW]
  · have hc3 : (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff P'.isLB hc3).1 ?_
    rw [cube_class_e8Bundle_eighth_power W pr hmon P'.L P'.isLB M cub hE]
    have e1 := cechPicard_pullback_e8Bundle_class W pr P'.L P'.isLB M hE (𝟙 P'.A)
    rw [Over.id_left, GlobalTheory.CechPic.pull_id] at e1
    rw [e1]
    have h2 : (fun b => act 0 ≫ pr b) = fun b => ∏ k, pr k ^ actMat W 0 b k := funext fun b => hacts 0 b
    simp only [Category.id_comp]
    rw [h2, bil_right M cub, mat_prim W hW]

end GlobalTheory.Poinc.Sep.E8Fibration.PrimPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.EighthPowerBundle

open GlobalTheory.CechPic

def pre0 {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left)
    (hP : IsSymmetricPair h A P) : SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hP.1
  P := P
  isLB := hP.2.2.1
  rig₁ := hP.2.2.2.1
  rig₂ := hP.2.2.2.2.1
  symm := hP.2.2.2.2.2
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem powLB_props : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left),
    IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧
      Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧
      Out.Sym (Out.powObj A 8) (powLB A P) := by
  intro S h A _ _ P hP hA
  let c := pre0 h A P hP
  have hA' : Out.RelAmple c.A c.diag := hA
  obtain ⟨hpos, -⟩ := isE8_W8
  let pr : Fin 8 → (Out.powObj A 8 ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP.2.2.1 _ _
  have hLW : cls (powLB A P) hL = PrincipalIntegral.quad (cls c.P c.isLB) W8 pr := cls_linComb hP.2.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨AbelianSchemeGerms.isAbelianScheme_powObj A hP.1 7, hL,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 8 ℤ 0 S _ c (Out.powObj A 8) pr W8 hmon huniv hA'
      hpos,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PrincipalIntegral.sym hadd (PrincipalIntegral.pair_comm c) hmon hL hLW⟩

end GlobalTheory.EighthPowerBundle
end
end

