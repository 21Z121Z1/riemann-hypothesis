import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ringKrullDim_le_of_isEtaleCompletion : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  intro O A _ _ _ _ _ _ ψ _ h
  letI : Algebra O A := ψ.toAlgebra
  have hmap : (maximalIdeal O).map (algebraMap O A) = maximalIdeal A := h.2.1
  have hlo : (maximalIdeal A).LiesOver (maximalIdeal O) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap ψ).symm
  have key := Ideal.height_le_height_add_of_liesOver (maximalIdeal O) (maximalIdeal A)
  rw [hmap, Ideal.map_quotient_self] at key
  have h0 : (⊥ : Ideal (A ⧸ maximalIdeal A)).height = 0 := by
    simp
  rw [h0, add_zero] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

abbrev Vec (r : ℕ) := Fin r ⊕ Fin r → ℤ

section Formal

variable {r : ℕ}

def lam (u v : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (u + v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 0 1

def theta (a b c : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (a + b + c) 1 - Finsupp.single (a + b) 1 - Finsupp.single (a + c) 1 - Finsupp.single (b + c) 1 +
    Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 - Finsupp.single 0 1

def xv (i : Fin r) : Vec r := Sum.elim (Pi.single i 1) 0

def zv (i : Fin r) : Vec r := Sum.elim 0 (Pi.single i 1)

def axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim (fun l => A i l) 0

def azv (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim 0 (fun l => A' i l)

def rosVec (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i : Fin r) : Vec r :=
  ![axv A i + zv i, axv A i, zv i, xv i + azv A' i, xv i, azv A' i] a

def sig (W A A' : Matrix (Fin r) (Fin r) ℤ) : Vec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • lam (rosVec A A' a i) (rosVec A A' a j)

end Formal

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def vecHom (T : Tens D D' W) (v : Vec r) : D'.P.A ⊗ D'.P.A ⟶ D.P.A :=
  (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k)

def vecLat (T : Tens D D' W) (v : Vec r) (y y' : D'.X) : D.X :=
  ∑ k, v (Sum.inl k) • T.xe y k + ∑ k, v (Sum.inr k) • T.xe y' k

def isoV {X X' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}
    (w : LB.Iso M' (LB.LinComb M ψ δ)) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι) (χ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ :=
  gm χ z _ (w.s (fun k => J (χ ≫ ψ k), J' χ))

def qv (T : Tens D D' W) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (χ : D'.X) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  ∏ i, ∏ j, val (D.tau (T.xe χ i) (T.xe χ j)) (𝟙 _) z J ^ W i j

def rosLat (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) : Fin 6 → D'.X :=
  ![GlobalTheory.TensAct.latAct T A y + y', GlobalTheory.TensAct.latAct T A y, y', y + GlobalTheory.TensAct.latAct T A' y', y,
    GlobalTheory.TensAct.latAct T A' y']

def Triv (T : Tens D D' W) (c : Vec r →₀ ℤ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb D.P.L (fun v : c.support => (vecHom T v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good D.P.L z J → ∀ y y' : D'.X,
      val Ξ (D'.pt2 y y') z J = ∏ v ∈ c.support, val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-(c v))

end GlobalTheory.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjGenericOfCube
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem linEnd_of_actsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b : D.toPre.P.A ⟶ D.toPre.P.A} {h : D.toPre.X →+ D.toPre.X} {g : G ⟶ G} [IsMonHom g]
    (hg : ActsAs U b h g) : LinEnd U b h g :=
  ⟨inferInstance, fun _ => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map g e, fun e => (hg e).1,
    fun e => (hg e).2⟩

theorem rosatiAdj_generic_of_cube (hcube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o a g g' hg hg' ag ag'
  have hE := GlobalTheory.Mum.EndModel.endData_of_oAct O D.toPre o a
  have l1 : LinEnd U.toUnifPre (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) g :=
    linEnd_of_actsAs U.toUnifPre ag
  have l2 : LinEnd U.toUnifPre (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) g' := by
    have := linEnd_of_actsAs (h := DistribSMul.toAddMonoidHom D.toPre.X (star (star a))) U.toUnifPre ag'
    simpa only [star_star] using this
  have H := hcube R hR D A G hG U _ _ _ _ hE g g' l1 l2
  obtain ⟨u, hu⟩ := (GlobalTheory.NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB g g' H).1
  have := U.gen_hom
  exact GlobalTheory.EndRosati.rosatiAdj_generic U.toUnifPre (by simp) (by simp) u hu.1

end GlobalTheory.Mum.RosGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Over S}
variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

def lamLeft (z : X ⟶ G) : (X ⟶ G) →* Multiplicative (Pic X.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_prod_left {κ : Type} [Fintype κ] (x : κ → (X ⟶ G)) (n : κ → ℤ) (z : X ⟶ G) :
    lam (cls L hL) (∏ i, x i ^ n i) z = ∑ i, n i • lam (cls L hL) (x i) z := by
  have h := congrArg Multiplicative.toAdd (map_prod (lamLeft hL hΘ z) (fun i => x i ^ n i) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  exact h

theorem lam_prod_right {κ : Type} [Fintype κ] (x : X ⟶ G) (z : κ → (X ⟶ G)) (n : κ → ℤ) :
    lam (cls L hL) x (∏ i, z i ^ n i) = ∑ i, n i • lam (cls L hL) x (z i) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ (z _) x]

theorem lam_mul_right (x y z : X ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

end Bilinear

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def pairP (T : Tens D D' W) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j)

theorem cls_tens (T : Tens D D' W) :
    cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (T.pr i) (T.pr j) := by
  have hC := LB.isLB_linComb D.P.isLB (tensφ T.pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨T.w, T.w_gen⟩).trans ?_
  rw [cls_linComb D.P.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_tens (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairP T W h h := by
  rw [cls_tens T, pairP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

end Tensor

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

section Tensor2

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pairP_mul (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairP T W (u * v) (u * v) = pairP T W u u + pairP T W v v + pairP T (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ T.pr i = u ≫ T.pr i * v ≫ T.pr i := fun i => by
    haveI := T.pr_hom i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls D.P.L D.P.isLB) (v ≫ T.pr i) (u ≫ T.pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls D.P.L D.P.isLB) (u ≫ T.pr i) (v ≫ T.pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairP, hm, lam_mul_left D.P.isLB hΘ, lam_mul_right D.P.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

def pre {X Y Z : Over (Spec (CommRingCat.of R))} [GrpObj Z] (u : X ⟶ Y) : (Y ⟶ Z) →* (X ⟶ Z) where
  toFun f := u ≫ f
  map_one' := by simp [Hom.one_def]
  map_mul' f g := MonObj.comp_mul u f g

theorem comp_act_pr (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ T.act m) ≫ T.pr i = ∏ k, (u ≫ T.pr k) ^ m i k := by
  rw [Category.assoc, Tens.act_pr]
  exact (map_prod (pre (Z := D.P.A) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := D.P.A) u) _ _)

theorem pairP_act_left (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M (u ≫ T.act m) v = pairP T (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_left D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairP_act_right (T : Tens D D' W) (M m : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : pairP T M u (v ≫ T.act m) = pairP T (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta D.P.A D.P.L), t.IsGen := ⟨D.cub.t, D.cub.isGen⟩
  simp only [pairP, comp_act_pr, lam_prod_right D.P.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end Tensor2

end GlobalTheory.Mum.RosatiTens

namespace GlobalTheory.Mum.RosatiTens

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem symUnit_mul_star (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    (W + W.transpose) * TensO.mat _ (star a) = (TensO.mat _ a).transpose * (W + W.transpose) := by
  have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show (W + W.transpose) * ((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)) = _
  rw [← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem rosatiAdj_core (T : Tens D D' W) (h : IsUnit (W + W.transpose).det) (a : TensO (symUnitOf W h)) :
    RosatiAdj D'.P.A D'.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := T.act (TensO.mat _ a)
  let g := T.act (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_tens T]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairP_mul, pairP_mul]
    rw [pairP_act_left T (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairP_act_right T (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.RosatiTens

open GlobalTheory.Mum.RosatiTens in

theorem GlobalTheory.Mum.rosatiAdj_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact rosatiAdj_core T h a
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdjoint_unique_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  first | exact @GlobalTheory.Mum.rosatiAdj_unique | exact GlobalTheory.Mum.rosatiAdj_unique | (intros; apply GlobalTheory.Mum.rosatiAdj_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  first | exact @GlobalTheory.Mum.kill_of_lam_triv | exact GlobalTheory.Mum.kill_of_lam_triv | (intros; apply GlobalTheory.Mum.kill_of_lam_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEHasTie
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.TieOfLink

theorem tie_of_rpk {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) {x : TwIn O.ex} (y : RealIn x b.R b.S) (r : RecIn y)
    (e : rpkB b = rpkX y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : RealPins3 (realTOf y)) (hp : ∃ pins : RealPins (realTOf y), RealRecPins pins (realRecOf r)) :
    Nonempty b.Comparison₂ := by
  have key : ∀ z : RPk b.R b.S, z = rpkX y → ∃ Rr : RealRec z.B.Q, PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      RealPins3 z.B.Q ∧ ∃ pins : RealPins z.B.Q, RealRecPins pins Rr := by
    rintro z rfl
    exact ⟨realRecOf r, hpsi, h3, hp⟩
  obtain ⟨Rr, h⟩ := key _ e
  exact ⟨⟨Rr, h⟩⟩

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

theorem tie_of_wit (q : WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : RealPins (realTOf w.y.y))
    (hloc : Formalism.IndefR.principalLevelFrame.RowLocPin b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := GlobalTheory.T.recursion_local_row_condition _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : RealPins3 (realTOf w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact realPins3_realTOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact tie_of_rpk b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩

theorem rowE_hasTie {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Q : V4.Slot) :
    RowE Q (IsLinked p) fun _ => HasTie := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((GlobalTheory.T.bundle_witness_zero_section_eq_local hL p).and (GlobalTheory.T.bundle_witness_constant_eq hL p)).and (GlobalTheory.T.bundle_witness_places_eq_image hL p)).and (GlobalTheory.T.theta_level_conjugate_character hL p)).and (GlobalTheory.T.row_local_level_character hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : RealPins (realTOf w.y.y) :=
    realPins_realTOf _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : HasTie _ _ c b' := tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), Bundle D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → HasTie s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e

end GlobalTheory.Fc.TieOfLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def SecCarried {X : Scheme.{0}} (L : LB X) (θ : L.Sec) (f : X ⟶ X) (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι) (hk : z ∈ L.U k) (hj : f z ∈ L.U j),
    (X.presheaf.germ (f ⁻¹ᵁ L.U j) z hj).hom ((f.app (L.U j)).hom (θ.f j)) =
      (gw w (𝟙 X) z j k).val * (X.presheaf.germ (L.U k) z hk).hom (θ.f k)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_map_gs {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (f.stalkMap y).hom (gs (𝟙 X) (f y) U a) := by
  rw [gs_eq f y U h, gs_eq (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

def IsSecOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) : Prop :=
  ∀ (z : X) (k k' : L.ι), z ∈ W → z ∈ L.U k → z ∈ L.U k' →
    gs (𝟙 X) z (W ⊓ L.U k) (s k) =
      (gm (𝟙 X) z (L.U k ⊓ L.U k') (L.g k k') : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k') (s k')

def SecCarriedOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gs f z (W ⊓ L.U j) (s j) = (gw w (𝟙 X) z j k : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k) (s k)

example {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (hT : IsFrameOver L W T) :
    IsSecOver L W (fun k => (T k).val) := by
  intro z k k' hz hk hk'
  have hm : z ∈ W ⊓ L.U k ⊓ (W ⊓ L.U k') := ⟨⟨hz, hk⟩, hz, hk'⟩
  have e := congrArg (fun u => (gm (𝟙 X) z _ u : X.presheaf.stalk z)) (hT k k')
  simp only [map_mul, Units.val_mul] at e
  rw [gm_res _ z _ hm, gm_res _ z _ hm, gm_res _ z _ hm] at e
  have h1 : (𝟙 X) z ∈ W ⊓ L.U k := ⟨hz, hk⟩
  have h2 : (𝟙 X) z ∈ W ⊓ L.U k' := ⟨hz, hk'⟩
  show gs (𝟙 X) z _ (T k).val = _ * gs (𝟙 X) z _ (T k').val
  rw [gs_unit _ z _ h1, gs_unit _ z _ h2]
  exact e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_direct_factor_of_idempotent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  first | exact @GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | exact GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | (intros; apply GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image <;> assumption)
end

