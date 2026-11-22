import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem degenerationPointOfLattice_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (b : D.X) : cP D T (n • b) = cP D T b ^ n := by
  let f : Multiplicative D.X →* (T ⟶ D.P.A) :=
    { toFun := fun x => cP D T x.toAdd
      map_one' := by simpa using cPoint_nsmul D T 0 0
      map_mul' := fun x y => cPoint_add D T _ _ }
  have := map_zpow f (Multiplicative.ofAdd b) n
  simpa [f] using this

theorem overSpec_comp_zpow_grpObj {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (y : T ⟶ D.P.A) (n : ℤ) :
    ρ ≫ y ^ n = (ρ ≫ y) ^ n := by
  let f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A) :=
    { toFun := fun x => ρ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  exact map_zpow f y n

theorem value_tau_add_nsmul_mul_iteratedCube (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (a₀ m v : D.X) (k : ℕ) :
    val (D.tau (a₀ + k • m) v) (𝟙 (TK R).left) z J *
        cubN (th D z J) k (cP D (TK R) a₀) (cP D (TK R) m) (cP D (TK R) v) =
      val (D.tau a₀ v) (𝟙 (TK R).left) z J * val (D.tau m v) (𝟙 (TK R).left) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v
    rw [cPoint_add, cPoint_nsmul] at e
    simp only [Over.id_left] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]
    simp only [cubN] at ih
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e' ih' ⊢
    rw [succ_nsmul]
    linear_combination (norm := abel) e' + ih'

theorem exists_lamGen_zpow : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  intro R _ _ D hB n
  have hL := D.P.isLB
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left,
          (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        ![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)]
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (k : ℤ)))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(k : ℤ) * Oε l)) := by
      intro U _ h
      have e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ) := by rw [_root_.one_mul, zpow_natCast, mul_comm]
      have e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ) := by
        rw [_root_.one_mul, zpow_natCast]
      have e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A := _root_.one_mul _
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      rw [e1, e2, e3, e4, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF t ht
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]
    have e := val_tau_nsmul (𝟙 (TK R)) hJ hB k b a
    rw [val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a] at e
    simp only [Over.id_left] at e
    rw [natCast_zsmul, zpow_natCast]
    exact e
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left,
          (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        (fun i => -(![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ) i)
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (-(k : ℤ))))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(-(k : ℤ)) * Oε l)) := by
      intro U _ h
      have e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel]
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      have e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ)) := mul_comm _ _
      rw [e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]
    have c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b) := (degenerationPointOfLattice_zsmul _ _ _).symm
    rw [c1]
    have e := value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k
    have z0 := val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a
    rw [zero_nsmul] at z0
    simp only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0
    have s0 : (-(k : ℤ)) • b + k • b = 0 := by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]
    rw [s0, z0, _root_.one_mul] at e
    have s1 := val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)
    have s2 := val_tau_symm (𝟙 (TK R)) hJ a b
    simp only [Over.id_left] at s1 s2
    rw [s1, s2]
    rw [show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) =
      cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e,
      mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureGeometricFibrePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_structure_geometric_fibre_pullback : ∀ (T K : Type) [CommRing T] [IsNoetherianRing T] [Field K] [IsAlgClosed K] (χ : T →+* K) (P : PolAV (Sp T)) (Q : PolAV (Sp K)) (ψ : Q.A.left ⟶ P.A.left), IsGrpPullback Q.A P.A (spMap χ) ψ → LBIso Q.L (P.L.pull ψ) → ∀ (g M : ℕ) (hg : Q.g = g) (c : Tˣ) (ζK : Kˣ), (M : K) ≠ 0 → Units.map χ.toMonoidHom c = ζK → IsPrimitiveRoot ζK M → ∀ (y : Fin (2 * g) → (baseOver (Sp T) ⟶ P.A)), (∀ i, y i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (y i) (y j) (unitOn c ^ stdSymp g i j)) → ∃ lev : Level Q M (unitOn ζK), ∀ i, (GlobalTheory.levelBasis lev hg i).left ≫ ψ = spMap χ ≫ (y i).left := by
  first | exact @GlobalTheory.Mum.FibLevel.exists_level_of_pullback | exact GlobalTheory.Mum.FibLevel.exists_level_of_pullback | (intros; apply GlobalTheory.Mum.FibLevel.exists_level_of_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_structure_rational_thetaPoint_subfield : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  first | exact @GlobalTheory.ThetaDescentLevel.exists_level | exact GlobalTheory.ThetaDescentLevel.exists_level | (intros; apply GlobalTheory.ThetaDescentLevel.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisLiftModelVectors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLift

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n m : ℕ} (h : n = m)
    {w : Fin m → (epsR R ⟶ G)} (hw : IsLieBasis w) : IsLieBasis (fun j : Fin n => w (j.cast h)) := by
  subst h
  simpa using hw

theorem dual_eq_id {K : Type} [Field K] (F : DualNumber K →+* DualNumber K)
    (h₁ : ∀ a, F (algebraMap K _ a) = algebraMap K _ (RingHom.id K a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = RingHom.id _ := by
  let Fa : DualNumber K →ₐ[K] DualNumber K := { F with commutes' := h₁ }
  have : Fa = AlgHom.id K _ := DualNumber.algHom_ext h₂
  exact RingHom.ext fun z => congrArg (fun q : DualNumber K →ₐ[K] DualNumber K => q z) this

theorem main : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  intro K _ G _ _ L σ σ' x x' hg' y y' M hx hx' hM
  obtain ⟨φ, he, ψ, F, hφ, hψ, hmaps, hsec, hF₁, hF₂, hxv⟩ := hx
  obtain ⟨φ', -, -, F', hφ', -, -, -, hF₁', hF₂', hxv'⟩ := hx'
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  have e' : spMap (RingHom.id (DualNumber K)) = 𝟙 (Sp (DualNumber K)) := Spec.map_id _
  have hF := dual_eq_id F hF₁ hF₂
  have hF' := dual_eq_id F' hF₁' hF₂'
  subst hF hF'
  have eD : spMap (Formalism.L2.Pj.dualMap (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Formalism.L2.Pj.dualMap]
  have eR : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Chart.dualMapR]

  have hw : ∀ i, (y' i).left ≫ G.hom = (epsR K).hom ≫ spMap (RingHom.id K) := fun i => by
    rw [e, Category.comp_id]; exact Over.w (y' i)
  let v : Fin x.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (hφ.1.lift (y' i).left (epsR K).hom (hw i))
    (hφ.1.lift_snd _ _ _)
  have hvφ : ∀ i, (v i).left ≫ φ = (y' i).left := fun i => hφ.1.lift_fst _ _ _

  let χ : x.P.A.left ⟶ x'.P.A.left := hφ'.1.lift φ x.P.A.hom hφ.1.w
  have hχ : χ ≫ φ' = φ := hφ'.1.lift_fst _ _ _
  have hχ' : χ ≫ x'.P.A.hom = x.P.A.hom ≫ spMap (RingHom.id K) := by
    rw [hφ'.1.lift_snd, e, Category.comp_id]
  have hn : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ spMap (RingHom.id K)) (χ ≫ φ') := by
    rw [hχ, e, Category.comp_id, ← e]; exact hφ
  have hC : IsGrpPullback x.P.A x'.P.A (spMap (RingHom.id K)) χ := IsGrpPullback.cancel hφ' hn hχ'
  have := x'.P.isAb.smooth
  have hvχ : ∀ j, (v j).left ≫ χ = spMap (Chart.dualMapR (RingHom.id K)) ≫ (x'.v (j.cast hg'.symm)).left := by
    intro j
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hχ, hvφ, eR, Category.id_comp, hxv', e', Category.id_comp]
      simp
    · rw [Category.assoc, hχ', ← Category.assoc, Over.w (v j), eR, Category.id_comp, Over.w (x'.v _), e,
        Category.comp_id]
  have hv : IsLieBasis v := Chart.isLieBasis_baseChange (RingHom.id K) hC
    (isLieBasis_cast hg'.symm x'.basis) hvχ
  refine ⟨v, hv, fun i => ?_, φ, he, ψ, RingHom.id _, hφ, hψ, hmaps, hsec, hF₁, hF₂, fun i => ?_⟩
  · have h' : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ 𝟙 (Sp K)) φ := by rw [Category.comp_id]; exact hφ
    exact GlobalTheory.LamT.isLieComb_of_two_pullbacks (RingHom.id K) rfl (grpPullback_self G) h' rfl (hM i)
      (fun j => by rw [hxv, eD, e', Category.comp_id]; rfl)
      (by rw [hvφ, eD, Category.comp_id, Category.id_comp])
  · rw [hvφ, e', Category.id_comp]

end GlobalTheory.LieLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCorrOfPowEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_lieCorr_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R) (t : G.TorsionTower A) (x : G.Lie), ∃ v : epsR R ⟶ A, t.LieCorr x v := by
  intro p _ R _ N hN A _ G t x
  have hb := omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl
  let e := LinearEquiv.ofBijective (G.omegaLevel N) hb
  let D : G.A N →ₗ[R] R := x ∘ₗ e.symm.toLinearMap ∘ₗ AugCot.d (Bialgebra.counitAlgHom R (G.A N))
  have hD : ∀ a b : G.A N, D (a * b) = Coalgebra.counit (R := R) a * D b + Coalgebra.counit (R := R) b * D a := by
    intro a b
    simp only [D, LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, smul_eq_mul]
    rfl
  have hD1 : D 1 = 0 := by simp [D]
  let ψ₀ : G.A N →ₐ[R] DualNumber R :=
    AlgHom.ofLinearMap
      (Algebra.linearMap R (DualNumber R) ∘ₗ Coalgebra.counit + TrivSqZeroExt.inrHom R R ∘ₗ D)
      (by simp [hD1])
      (fun a b ↦ by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl, hD, mul_comm])
  have hfst : ∀ a, (ψ₀ a).fst = Coalgebra.counit (R := R) a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  have hsnd : ∀ a, (ψ₀ a).snd = D a := fun a ↦ by
    simp [ψ₀, TrivSqZeroExt.algebraMap_eq_inl]
  let v : epsR R ⟶ A := spOver ψ₀ ≫ t.y N
  have hv : IsTangent v := by
    have h := (t.eq_one_iff N ((TrivSqZeroExt.fstHom R R R).comp ψ₀)).2 hfst
    rw [← spOver_comp, Category.assoc] at h
    refine (congrArg Over.Hom.left h).trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ η[A].left) (Cris.spMap_id R)).trans (Category.id_comp _)
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R :=
    isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
  refine ⟨v, ?_⟩
  suffices hx : x' = x by rw [← hx]; exact hx'
  refine LinearMap.ext fun w ↦ ?_
  have k := (t.lieCorr_iff hv x').1 hx' N w
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 N)
  have ep : t.tanPt hv N = (epsTo R (ModPow p R N)).comp ψ₀ :=
    t.inj N _ _ _ (by rw [t.tanPt_y hv N, ← spOver_comp, Category.assoc])
  have ew : e.symm (w.1 N) = w := e.symm_apply_eq.2 rfl
  rw [← ha, TorsionTower.tanDer_d, ep, AlgHom.comp_apply, snd_epsTo, hsnd] at k
  have k2 : D a = x w := by
    simp only [D, LinearMap.comp_apply]
    change x (e.symm (AugCot.d (Bialgebra.counitAlgHom R (G.A N)) a)) = x w
    rw [ha, ew]
  rw [k2, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hN, Ideal.mem_span_singleton,
    zero_dvd_iff, sub_eq_zero] at k
  exact k

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section TransportLinComb

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]

theorem transChart_le (ψ : K → (X' ⟶ X)) (σ : I → (Y ⟶ X')) (jN : I × K → L.ι) (jM : I → L'.ι) (i : I) :
    LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) jN ⊓ LB.wchart L' σ jM ≤
      σ i ⁻¹ᵁ (LB.wchart L ψ (fun k => jN (i, k)) ⊓ L'.U (jM i)) :=
  fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k), Set.mem_iInter.1 hy.2 i⟩

def transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X')) (e : I → ℤ) :
    LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) where
  s P := ∏ i, res (transChart_le ψ σ P.1 P.2 i) (pullU (σ i) _ (w.s (fun k => P.1 (i, k), P.2 i))) ^ e i

theorem gm_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) (r : Z ⟶ Y) (z : Z) (P : (I × K → L.ι) × (I → L'.ι))
    (hP : r z ∈ LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) P.1 ⊓ LB.wchart L' σ P.2) :
    gm r z _ ((transIso ψ δ w σ e).s P) = ∏ i, gm (r ≫ σ i) z _ (w.s (fun k => P.1 (i, k), P.2 i)) ^ e i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ e i) ?_))
  exact (gm_res r z _ hP _).trans (gm_pull r (σ i) z _ (transChart_le ψ σ P.1 P.2 i hP) _)

theorem isGen_iff_gm' {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

theorem gm_of_isGen (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (r : Z ⟶ X') (z : Z) (P Q : (K → L.ι) × L'.ι)
    (hm : r z ∈ LB.wchart L ψ P.1 ⊓ L'.U P.2 ⊓ (LB.wchart L ψ Q.1 ⊓ L'.U Q.2)) :
    gm r z _ (w.s P) = ((∏ k, gm (r ≫ ψ k) z (L.U (P.1 k) ⊓ L.U (Q.1 k)) (L.g (P.1 k) (Q.1 k)) ^ δ k) *
      (gm r z _ (L'.g P.2 Q.2))⁻¹) * gm r z _ (w.s Q) := by
  have h := congrArg (gm r z _) (hw P Q)
  exact (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L' (LB.LinComb L ψ δ) r z P Q hm).trans (congrArg (· * _) (gm_linComb L ψ δ r z _ _ hm.1.1 hm.2.1)))
    (gm_res r z _ hm _))))

theorem isGen_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (σ : I → (Y ⟶ X')) (e : I → ℤ) : (transIso ψ δ w σ e).IsGen := by
  refine (isGen_iff_gm' _).2 fun P Q y hy => ?_
  have hd : gm (𝟙 Y) y ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U P ⊓ (LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U Q) ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).g P Q) = _ :=
    gm_div (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) (𝟙 Y) y P Q hy
  rw [gm_transIso ψ δ w σ e (𝟙 Y) y P hy.1, gm_transIso ψ δ w σ e (𝟙 Y) y Q hy.2,
    hd]
  erw [gm_linComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2) (𝟙 Y) y P.1 Q.1 hy.1.1 hy.2.1,
    gm_linComb L' σ e (𝟙 Y) y P.2 Q.2 hy.1.2 hy.2.2,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) (gm_of_isGen ψ δ hw (𝟙 Y ≫ σ i) y
      (fun k => P.1 (i, k), P.2 i) (fun k => Q.1 (i, k), Q.2 i)
      ⟨transChart_le ψ σ P.1 P.2 i hy.1, transChart_le ψ σ Q.1 Q.2 i hy.2⟩)]
  rw [Fintype.prod_prod_type]
  simp only [Category.assoc, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_zpow, ← zpow_mul, inv_zpow',
    Finset.prod_inv_distrib]
  simp only [mul_comm (δ _) (e _)]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rfl

end TransportLinComb

theorem exists_transIso_linComb : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]
    (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e)
      (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) =
          ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  intro X X' Y L L' K I _ _ ψ δ w hw _ _ σ e
  refine ⟨transIso ψ δ w σ e, isGen_transIso ψ δ hw σ e, fun Z q z J J' hJ hJ' => ?_⟩
  exact gm_transIso ψ δ w σ e q z _ ⟨hJ.mem (fun p : I × K => σ p.1 ≫ ψ p.2) q, hJ'.mem σ q⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveAppStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_descent_bijective_app : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) → ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  first | exact @GlobalTheory.Mum.lb_descend | exact GlobalTheory.Mum.lb_descend | (intros; apply GlobalTheory.Mum.lb_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstruction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.ObEx

theorem exists_isObL : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L hL
  obtain ⟨C, _, _, G, u, hB, hF⟩ := GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis X₀ L hL
  have hc := GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis X₀ C (opOf G) (opOf_le G) L u hL hF
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_unitCocycleLiftObstruction R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u
    ((ofSys_isFun S).restrict G) (fun T T' T'' a b ↦ congrArg Units.val (hc a b))
  obtain ⟨c, rfl⟩ := (GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X₀ s₀ C G hB.1 hB.2).2.2 d
  exact ⟨c, C, inferInstance, inferInstance, G, hB, u, hF, hd⟩

end GlobalTheory.LBObs.ObEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localFormOfTensorSection_in_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  first | exact @GlobalTheory.KeyValsSec.exists_locSec | exact GlobalTheory.KeyValsSec.exists_locSec | (intros; apply GlobalTheory.KeyValsSec.exists_locSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomCompleteDVRPrincipalMaximalIdealStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localHom_completeDVR_principal_maximalIdeal : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} → ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  first | exact @GlobalTheory.PrincDvr.exists_cDvr_localHom | exact GlobalTheory.PrincDvr.exists_cDvr_localHom | (intros; apply GlobalTheory.PrincDvr.exists_cDvr_localHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapIntegralSchemeToGradedProjModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  first | exact @GlobalTheory.Desc.ToModel.exists_map_to_model | exact GlobalTheory.Desc.ToModel.exists_map_to_model | (intros; apply GlobalTheory.Desc.ToModel.exists_map_to_model <;> assumption)
end

