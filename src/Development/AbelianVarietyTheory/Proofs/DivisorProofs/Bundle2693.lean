import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
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

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionProductEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_act_prod_eq_one : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  letI := P'.isAb.comm
  act 0 * act 1 = 𝟙 P'.A ∧
  LBIso (cubeLB P'.A ![fst P'.A P'.A ≫ act 0, snd P'.A P'.A] P'.L) (cubeLB P'.A ![fst P'.A P'.A, snd P'.A P'.A ≫ act 1] P'.L) ∧
  LBIso P'.L (cubeLB P'.A ![𝟙 P'.A, act 0] P'.L) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | exact GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.PrimPic.e8_act_endomorphism_prod_eq_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8_act_linComb_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | exact GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound.exists_bound_relAmple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | exact GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | (intros; apply GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def postHom {S : Scheme.{0}} (T : Over S) {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := by simp
  map_mul' x y := by simp [MonObj.mul_comp]

def preHom {S : Scheme.{0}} {T A : Over S} (x : T ⟶ A) (B : Over S) [GrpObj B] :
    (A ⟶ B) →* (T ⟶ B) where
  toFun y := x ≫ y
  map_one' := by simp
  map_mul' y z := by simp [MonObj.comp_mul]

theorem zpow_finset_sum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (e : J → ℤ) :
    g ^ (∑ i ∈ s, e i) = ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_prod_zpow {G C J : Type} [CommGroup G] [Fintype C] [Fintype J] (b : C → G) (x : J → C → ℤ) (k : J → ℤ) :
    ∏ i, (∏ c, b c ^ x i c) ^ k i = ∏ c, b c ^ (∑ i, k i * x i c) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finset_sum]
  rw [Finset.prod_comm]
  simp only [mul_comm]

theorem pow_val_intCast {G : Type} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) (k : ℤ) :
    g ^ ((k : ZMod N)).val = g ^ k := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' k hg).symm

theorem prod_zpow_pow_eq_one {G C : Type} [CommGroup G] [Fintype C] {N : ℕ} {b : C → G} (hb : ∀ c, b c ^ N = 1)
    (x : C → ℤ) : (∏ c, b c ^ x c) ^ N = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem sum_labMat_mul (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2)
    (i : Fin (2 * (8 * h))) (u : Fin 8) (c : Fin h ⊕ Fin h) :
    ∑ i', labMat W hW h a i' i * sharpBasis W hW h (Pi.single i' 1) u c =
      ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c := by
  have key : ∀ y : Fin (2 * (8 * h)) → ℤ,
      ∑ i', y i' * sharpBasis W hW h (Pi.single i' 1) u c = sharpBasis W hW h y u c := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ' y]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (key _).trans (congrFun (congrFun ((sharpBasis W hW h).apply_symm_apply _) u) c)

theorem ptOf_torsion_and_act : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → 0 < N →
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  intro W hW gQ S A B _ _ _ _ pr hP N T b hb hN
  have ext : ∀ x y : T ⟶ A, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun x y h =>
    (hP.2 T fun u => y ≫ pr u).unique h fun _ => rfl
  refine ⟨fun i => ext _ _ fun u => ?_, fun act hact a i => ext _ _ fun u => ?_⟩
  · haveI := hP.1 u
    have := map_pow (postHom T (pr u)) (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) N
    refine this.trans ?_
    change (ptOf hP b _ ≫ pr u) ^ N = _
    rw [ptOf_pr, prod_zpow_pow_eq_one hb]
    exact (map_one (postHom T (pr u))).symm
  · haveI := hP.1 u
    have h1 : (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a) ≫ pr u =
        ∏ c, b c ^ (∑ v, actMat W a u v * sharpBasis W hW.2 gQ (Pi.single i 1) v c) := by
      rw [Category.assoc, hact a u, ← prod_prod_zpow]
      refine (map_prod (preHom (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) B) _ _).trans ?_
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow, ← ptOf_pr hP]
      rfl
    rw [h1, Out.linComb, List.prod_ofFn]
    refine Eq.trans ?_ (map_prod (postHom T (pr u)) _ _).symm
    simp only [← sum_labMat_mul W hW.2 gQ a i u]
    rw [← prod_prod_zpow]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [map_pow, ← pow_val_intCast hN (prod_zpow_pow_eq_one hb _), ← ptOf_pr hP]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

noncomputable section

namespace GlobalTheory.EigDiff

theorem eigSt_holds : EigSt := by
  intro E _ _ _ _ H p _
  have hv : (Valued.v : Valuation ℂ_[p] ℝ≥0).Integers 𝓞_ℂ_[p] := Valuation.valuationSubring.integers _
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.idempotent_trace_separating_element E ℂ_[p] Valued.v 𝓞_ℂ_[p] hv
  refine ⟨δ, hδ0, ?_⟩
  intro l c _ _ Q τ w hw
  rw [htLat_psi]
  obtain ⟨⟨n, r, a, hsum⟩, hb⟩ := hδ (embAt c ℂ_[p] τ.1)
  constructor
  · intro h
    exact GlobalTheory.HTLat.Point.smul_latTQuot_le_latT Q _ δ r a hsum h
  · intro h
    obtain ⟨m, u, ℓ, e, h1, h2, h3⟩ := GlobalTheory.T.p_adic_point_linear_functional_cm Q (embAt c ℂ_[p] τ.1)
    exact GlobalTheory.T.p_adic_point_trace_dual Q _ δ hδ0 hb m u ℓ e h1 h2 h3 w hw h

end GlobalTheory.EigDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G']

def lamC (x y : T ⟶ G) : Pic G.left →+ Pic T.left where
  toFun c := lam c x y
  map_zero' := by simp only [lam, map_zero]; abel
  map_add' c d := by simp only [lam, map_add]; abel

theorem lamC_apply (c : Pic G.left) (x y : T ⟶ G) : lamC x y c = lam c x y := rfl

theorem lam_pull_of (g : G' ⟶ G) (c : Pic G.left) (u v : T ⟶ G')
    (hm : (u * v) ≫ g = (u ≫ g) * (v ≫ g)) (h1 : (1 : T ⟶ G') ≫ g = 1) :
    lam (pull g.left c) u v = lam c (u ≫ g) (v ≫ g) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end Pairing

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right' (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

def lamHom (z : T ⟶ G) : (T ⟶ G) →* Multiplicative (Pic T.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_zpow_left (x z : T ⟶ G) (k : ℤ) :
    lam (cls L hL) (x ^ k) z = k • lam (cls L hL) x z := by
  have h := map_zpow (lamHom hL hΘ z) x k
  exact congrArg Multiplicative.toAdd h

theorem lam_prod_left : ∀ (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G),
    lam (cls L hL) (List.ofFn fun v => x v ^ e v).prod z = ∑ v, e v • lam (cls L hL) (x v) z
  | 0, x, e, z => by simp [lam_one_left]
  | n + 1, x, e, z => by
    rw [List.ofFn_succ, List.prod_cons, lam_mul_left hL hΘ, lam_zpow_left hL hΘ,
      lam_prod_left n (fun v => x v.succ) (fun v => e v.succ) z, Fin.sum_univ_succ]

theorem lam_prod_right (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G) :
    lam (cls L hL) z (List.ofFn fun v => x v ^ e v).prod = ∑ v, e v • lam (cls L hL) z (x v) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ z]

theorem lam_lam (p q : G' ⟶ G) [IsMonHom p] [IsMonHom q] (u v : T ⟶ G') :
    lam (lam (cls L hL) p q) u v = lam (cls L hL) (u ≫ p) (v ≫ q) + lam (cls L hL) (u ≫ q) (v ≫ p) := by
  have e : lam (lam (cls L hL) p q) u v = lamC u v (lam (cls L hL) p q) := rfl
  rw [e, show lam (cls L hL) p q = pull (p * q).left (cls L hL) - pull p.left (cls L hL) - pull q.left (cls L hL)
      + pull (1 : G' ⟶ G).left (cls L hL) from rfl, map_add, map_sub, map_sub]
  simp only [lamC_apply]
  rw [lam_pull_of (p * q) _ u v (by rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
      MonObj.comp_mul, _root_.mul_mul_mul_comm]) (by rw [MonObj.comp_mul, MonObj.one_comp, MonObj.one_comp, _root_.mul_one]),
    lam_pull_of p _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of q _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of (1 : G' ⟶ G) _ u v (by rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one])
      (MonObj.comp_one _)]
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, lam_one_left,
    lam_mul_left hL hΘ, lam_mul_right' hL hΘ, lam_mul_right' hL hΘ]
  abel

end Bilinear

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

theorem alg_left {M : Type*} [AddCommGroup M] (S a : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a i v • B v j = ∑ v, ∑ j, (a.transpose * S) v j • B v j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  simp_rw [smul_comm (S _ _) (a _ _)]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem alg_right {M : Type*} [AddCommGroup M] (S a' : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a' j v • B i v = ∑ i, ∑ v, (S * a') i v • B i v := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm

def precomp {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') : (T' ⟶ G) →* (T ⟶ G) where
  toFun y := h ≫ y
  map_one' := MonObj.comp_one h
  map_mul' := MonObj.comp_mul h

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') :
    ∀ (n : ℕ) (x : Fin n → (T' ⟶ G)) (e : Fin n → ℤ),
      h ≫ (List.ofFn fun v => x v ^ e v).prod = (List.ofFn fun v => (h ≫ x v) ^ e v).prod
  | 0, x, e => by simp [MonObj.comp_one]
  | n + 1, x, e => by
    rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h n, List.ofFn_succ, List.prod_cons]
    congr 1
    exact map_zpow (precomp (G := G) h) (x 0) (e 0)

theorem lbIso_cubeLB_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  intro K _ A A' W pr hpr hiso a a' hS f f' hf hf'
  haveI := A.isAb.comm
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨cs⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp K) A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta A.A A.L), t.IsGen := ⟨cs.t, cs.isGen⟩
  have hL := A.isLB
  have hL' := A'.isLB
  have hLam : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hL _ _
  have hLC := LB.isLB_linComb hLam (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hcA : cls A'.L hL' = ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • lam (cls A.L hL) (pr ab.1) (pr ab.2) := by
    rw [(cls_eq_iff hL' hLC).2 hiso, cls_linComb hLam]
    refine Finset.sum_congr rfl fun ab _ => ?_
    congr 1
    rw [show cls (abelian₂ A.A A.L) hLam = lam (cls A.L hL) (fst A.A A.A) (snd A.A A.A) from cls_cube_two hL _ _ _,
      pull_lam, lift_fst, lift_snd]
  have key : ∀ {T : Over (Sp K)} (u v : T ⟶ A'.A), lam (cls A'.L hL') u v =
      ∑ i, ∑ j, (W + W.transpose) i j • lam (cls A.L hL) (u ≫ pr i) (v ≫ pr j) := by
    intro T u v
    rw [← lamC_apply, hcA, map_sum]
    simp only [map_zsmul, lamC_apply, lam_lam hL hΘ, smul_add, Finset.sum_add_distrib, Matrix.add_apply,
      Matrix.transpose_apply, add_smul]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_comm
  have h₁ : (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L).IsLB := LB.isLB_linComb hL' _ _
  have h₂ : (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L).IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hL', cls_cube_two hL', key, key]
  simp only [Category.assoc, hf, hf', comp_prod, lam_prod_left hL hΘ, lam_prod_right hL hΘ]
  refine (alg_left (W + W.transpose) a
    (fun v j => lam (cls A.L hL) (fst A'.A A'.A ≫ pr v) (snd A'.A A'.A ≫ pr j))).trans ?_
  rw [← hS]
  exact (alg_right (W + W.transpose) a'
    (fun i v => lam (cls A.L hL) (fst A'.A A'.A ≫ pr i) (snd A'.A A'.A ≫ pr v))).symm

end GlobalTheory.E8AdjointPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerLiftCompProjection
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

def inc8 : G ⟶ G8 G := mk8 G fun i => if i = 0 then 𝟙 G else 1

def L8 (PP : LB (G2 G).left) : LB (G8 G).left :=
  LB.LinComb PP (K := Fin 8 × Fin 8) (fun ij => (lift (pr8 G ij.1) (pr8 G ij.2) : G8 G ⟶ G2 G).left)
    (fun ij => GlobalTheory.W8 ij.1 ij.2)

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

theorem zpow_sum8 {M : Type} [CommGroup M] (x : M) (f : Fin 8 → ℤ) : x ^ (∑ j, f j) = ∏ j, x ^ f j := by
  simp only [Fin.sum_univ_eight, Fin.prod_univ_eight, zpow_add]

theorem matAct_add (a b : Matrix (Fin 8) (Fin 8) ℤ) :
    matAct G (a + b) = padd (G8 G) (matAct G a) (matAct G b) := eighthPowerGroupObj_hom_ext G fun k => by
  have e : padd (G8 G) (matAct G a) (matAct G b) = matAct G a * matAct G b := rfl
  rw [e, MonObj.mul_comp _ _ (pr8 G k), matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, zpow_add]

theorem matAct_mul (a b : Matrix (Fin 8) (Fin 8) ℤ) :
    matAct G (a * b) = matAct G b ≫ matAct G a := eighthPowerGroupObj_hom_ext G fun k => by
  rw [Category.assoc, matAct_pr, matAct_pr, PowQuotient.comp_prod]
  simp only [GrpObj.comp_zpow, matAct_pr, Matrix.mul_apply]
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [zpow_sum8]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

def ringAct8 : RingAct (G8 G) GlobalTheory.Mum.E8Ring.O8 where
  act a := matAct G a
  hom a := matAct_hom G a
  map_one := matAct_one G
  map_mul a b := matAct_mul G a b
  map_add a b := matAct_add G a b

end GlobalTheory.Mum.Pow8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerProjections_baseChange_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso | exact GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.isProd_pullback_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_symmetric_ample : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧ Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧ Out.Sym (Out.powObj A 8) (powLB A P) := by
  first | exact @GlobalTheory.EighthPowerBundle.powLB_props | exact GlobalTheory.EighthPowerBundle.powLB_props | (intros; apply GlobalTheory.EighthPowerBundle.powLB_props <;> assumption)
end

