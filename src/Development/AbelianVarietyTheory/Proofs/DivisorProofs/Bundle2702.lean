import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeStep

section Gens

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def zpowGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ) :
    LB.Gen (LB.LinComb L φ (fun k => n * ε k)) where
  s := fun j => t.s j ^ n

theorem zpowGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    (zpowGen L φ ε t n).IsGen := fun i j => by
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _)))

theorem val_zpowGen {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (zpowGen L φ ε t n) r z J = val t r z J ^ n :=
  map_zpow _ _ _

theorem finProdGen_isGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProdGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Gens

theorem prod_zpow_mul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℤ) :
    ∏ k, f k ^ (n * e k) = (∏ k, f k ^ e k) ^ n := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem prod_finset_fin_two_ulift_expand {U : Type} [CommMonoid U] (f : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, f I = f ⟨{0, 1}⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨∅⟩ := by
  refine (Fintype.prod_equiv Equiv.ulift f (fun I => f ⟨I⟩) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ac_rfl

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

theorem groupSchemePartialSum_pair_both : psum B' (x2 B') {0, 1} = fst B' B' * snd B' B' := congrArg (fst B' B' * ·) (_root_.mul_one _)
theorem psum0 : psum B' (x2 B') {0} = fst B' B' := _root_.mul_one _
theorem psum1 : psum B' (x2 B') {1} = snd B' B' := _root_.mul_one _
theorem psumE : psum B' (x2 B') ∅ = 1 := rfl

theorem pair_eq {r : ℕ} (pr : Fin r → (B' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : ℤ) (i j : Fin r) {U : Type}
    [CommGroup U] (h : ((G2 B').left ⟶ B.left) → U) :
    ∏ k : thK.{0} ⊕ (thK.{0} ⊕ thK.{0}), h (Sum.elim
      (fun k => (lift (fst B' B' ≫ pr i) (lift (snd B' B' ≫ pr i) ((fst B' B' ≫ pr j) * (snd B' B' ≫ pr j)))).left ≫
        thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (fst B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (snd B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)) k) ^
      (-w * Sum.elim thε (Sum.elim thε thε) k) =
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr i) (snd B' B' ≫ pr j) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr j) (snd B' B' ≫ pr i) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
      h ((psum B' (x2 B') I.down).left ≫ tensφ pr ((i, j), k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-w) := by
  haveI := hpr i
  haveI := hpr j
  refine (prod_zpow_mul (U := U) _ (Sum.elim thε (Sum.elim thε thε)) (-w)).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_cub, prod_cub, prod_cub]
  simp only [prod_finset_fin_two_ulift_expand, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, tensφ, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, groupSchemePartialSum_pair_both, psum0, psum1, psumE]
  have q2 : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  have q0 : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q1 : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have qe : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  simp only [q2, q0, q1, qe, ← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, MonObj.one_comp, MonObj.comp_one,
    _root_.mul_one, _root_.one_mul]
  generalize fst B' B' ≫ pr i = a
  generalize snd B' B' ≫ pr i = b
  generalize fst B' B' ≫ pr j = c
  generalize snd B' B' ≫ pr j = d
  rw [mul_comm (c * d) a, mul_comm c a, mul_comm d a, mul_comm (c * d) b, mul_comm d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) (u v : T ⟶ B) : U :=
  ∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts u v k) ^ Oε k

def pairGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B))
    (p : Fin r × Fin r) :=
  zpowGen L.L _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε cb.t
      (lift (fst B' B' ≫ pr p.1) (lift (snd B' B' ≫ pr p.1) ((fst B' B' ≫ pr p.2) * (snd B' B' ≫ pr p.2)))).left)
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (fst B' B' ≫ pr p.1))).left)
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1))).left)))
    (-W p.1 p.2)

theorem pairGen_isGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (pr : Fin r → (B' ⟶ B)) (p : Fin r × Fin r) : (pairGen cb W pr p).IsGen :=
  zpowGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _) (DVR.pullGen_isGen _ _ _ _ cb.isGen _))) _

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum

open CubeStep in

theorem cube_step : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  intro S B B' _ _ _ _ L cb r W pr hpr
  have hfe : FormEq (fun q : (Fin r × Fin r) × (thK.{0} ⊕ (thK.{0} ⊕ thK.{0})) => Sum.elim
      (fun k => (lift (fst B' B' ≫ pr q.1.1) (lift (snd B' B' ≫ pr q.1.1)
        ((fst B' B' ≫ pr q.1.2) * (snd B' B' ≫ pr q.1.2)))).left ≫ thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (fst B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (snd B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)) q.2)
      (fun q => -W q.1.1 q.1.2 * Sum.elim thε (Sum.elim thε thε) q.2)
      (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2)
        (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2))
      (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)
        (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2))) := by
    intro U _ h
    have h1 : ∏ q : (Fin r × Fin r) × Fin 4,
        h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr q.1.1) (snd B' B' ≫ pr q.1.2) q.2) ^ ((W + W.transpose) q.1.1 q.1.2 * Oε q.2) =
        (∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ Oε k) ^
          W p.1 p.2) *
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1) k) ^ Oε k) ^
          W p.1 p.2 := by
      calc _ = ∏ p : Fin r × Fin r, ∏ k : Fin 4,
            h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ ((W + W.transpose) p.1 p.2 * Oε k) :=
          Fintype.prod_prod_type _
        _ = ∏ p : Fin r × Fin r, (lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.1 p.2 *
            lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.2 p.1) :=
          Finset.prod_congr rfl fun p _ => by
            rw [prod_zpow_mul, Matrix.add_apply, Matrix.transpose_apply, zpow_add]; rfl
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          exact congrArg _ (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
    have h2 : ∏ q : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4),
        h ((psum B' (x2 B') q.1.down).left ≫ tensφ pr q.2) ^ (-((-1) ^ (2 - q.1.down.card) * tensε W q.2)) =
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
          h ((psum B' (x2 B') I.down).left ≫ tensφ pr (p, k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-W p.1 p.2) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul]
      congr 1
      simp only [tensε]
      ring
    refine (Fintype.prod_prod_type _).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) h1 h2)).symm)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pair_eq pr hpr (W p.1 p.2) p.1 p.2 h
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB hfe (GeneratorPullback.finProdGen L.L _ _ (pairGen cb W pr))
    (finProdGen_isGen _ _ _ _ (pairGen_isGen cb W pr))
  refine ⟨t, ht, fun T ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_finProdGen _ _ _ (pairGen cb W pr) _ _ hJ).trans
    ((Fintype.prod_prod_type _).trans ?_))
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only [pairGen]
  refine (val_zpowGen _ _ _ _ _ _ _ _).trans (congrArg (· ^ (-W i j)) ?_)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) (val_cub cb ρ hJ _ _ _))))).trans ?_
  rw [MonObj.comp_mul, ← _root_.mul_assoc]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectio
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

section Transport

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {P B : LB Y}

def isoSec (w : LB.Iso P B) (hw : w.IsGen) : (LB.div B P).Sec := ⟨fun i => (w.s i : _), fun i j => by
  have := congrArg Units.val (hw i j)
  rw [Units.val_mul] at this
  exact this⟩

theorem val_congr_pt {O : Y.Opens} {R : Type} [CommRing R] {x x' : Sp R ⟶ Y} (h : x = x') (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst h; rfl

theorem val_restr_eq {O O' : Y.Opens} (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ Y) (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

end Transport

set_option maxHeartbeats 1000000 in

theorem exists_rule_of_cls_pull : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  intro D T j Y e o hG hE Z TF la L hL hc
  have hP : (L.pull (π₀ TF.X Z)).IsLB := LB.isLB_pull hL _
  have hB := isLB_L₀ TF.X Z la
  obtain ⟨w, hw⟩ := (cls_eq_iff hP hB).1 ((cls_pull hL _ hP).trans hc)
  let C := divChart hB hP
  let G : H0 (str₀ TF.X Z) (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))) ⊤ := H0.ofSec _ ⊤ (isoSec w hw)
  let sOf : H0 (s₀ TF.Y Z) L ⊤ → H0 (str₀ TF.X Z) (L₀ TF.X Z la) ⊤ := fun t =>
    C.mul (H0.pull (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) G
  choose f hf hf' using fun t => exists_suppOn_sec₀_eq _ _ _ _ _ _ _ _ _ (AllWt.exOf _ la 0) (H0.restr le_top (sOf t))
  refine ⟨fun t => (f t).1, fun t ht => ?_, fun yy v hv k hk => ?_⟩
  · have hs : sOf t ∈ vanBd TF.X Z la := (mem_vanBd _ _).2 fun y hy hn => by
      obtain ⟨τ, ha, hb, hcc⟩ := C.cover y
      have u1 : IsUnit (H0.germ (C.c τ) y (memTop y) hcc (sOf t)) := by
        rw [← ger_toSec]; exact (isUnit_ger_iff _ hcc).2 hn
      have e3 := C.germ_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G τ y (memTop y) ha hb hcc
      have u1' : IsUnit (H0.germ (C.a τ) y (memTop y) ha
          (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) *
          H0.germ (C.b τ) y (memTop y) hb G) := (congrArg IsUnit e3).mp u1
      have u2 := (congrArg IsUnit (H0.germ_pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top (C.a τ) y (memTop y) ha t)).mp
        (isUnit_of_mul_isUnit_left u1')
      have u3 := (isUnit_map_iff (Scheme.Hom.stalkMap (π₀ TF.X Z) y).hom _).1 u2
      rw [← ger_toSec] at u3
      obtain ⟨v', hv'⟩ := ht ((isUnit_ger_iff _ _).1 u3)
      refine hy (show TF.X.π (inc₀ TF.X Z y) ∈ LogKS.interior TF.Y from ⟨i₀ TF.Y Z v', ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply, hv', ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply]
    obtain ⟨g, hg⟩ := vanBd_le_space D T j Y e o hG hE Z TF la hs
    have e0 : f t = Submodule.inclusion (cusp_le_secZ Z Y.U la) g := by
      refine sub_eq_zero.1 (eq_zero_of_sec₀ TF.X Z (Submodule.sub_mem _ (hf t) g.2.2) ?_)
      rw [map_sub, hf' t, ← hg]
      exact sub_self _
    show (f t).1 ∈ _
    rw [e0]
    exact g.2
  · have e1 : TF.X.ptY yy ≫ TF.X.π = v ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
      rw [(TF.X.lies_ptY yy).1, j₀_ι, ← Category.assoc, hv]
      rfl
    have hr : Set.range (TF.X.ptY yy) ⊆ Set.range (inc₀ TF.X Z) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨⟨_, show TF.X.π (TF.X.ptY yy s) ∈ barComp TF.Y Z from ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
      exact ((v ≫ j₀ TF.Y Z) s).2
    let zz := IsOpenImmersion.lift (inc₀ TF.X Z) (TF.X.ptY yy) hr
    have hzz : zz ≫ inc₀ TF.X Z = TF.X.ptY yy := IsOpenImmersion.lift_fac _ _ _
    have e2 : zz ≫ π₀ TF.X Z = v ≫ j₀ TF.Y Z := by
      have h1 : (zz ≫ π₀ TF.X Z) ≫ (barComp TF.Y Z).ι = (v ≫ j₀ TF.Y Z) ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, Category.assoc, ← e1, ← hzz, Category.assoc]
        exact congrArg (zz ≫ ·) (morphismRestrict_ι TF.X.π (barComp TF.Y Z))
      exact (cancel_mono _).1 h1
    obtain ⟨k', hk'⟩ := exists_chart_of_field (TF.X.F.isLB_LL (AllWt.exOf (T.Q.Dw j) la 0)) (TF.X.pt yy ≫ TF.X.inc)
    obtain ⟨Q, tt, hQ, htt⟩ := FlagCover.exists_chartFr_frBor TF.X yy k' hk'
    have hO : ⊤ ≤ (TF.X.pt yy ≫ TF.X.inc) ⁻¹ᵁ flagOpen TF.X :=
      FlagMod.le_preimage_map TF.X.inc (top_le_inc TF.X) le_top
    have hzO : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by rw [hzz, ← FlagCover.pt_inc]; exact hO
    have hzk : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ (TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0)).U k' := by
      rw [hzz, ← FlagCover.pt_inc]; exact hk'
    have hTop : ⊤ ≤ zz ⁻¹ᵁ (⊤ : (Y₀ TF.X Z).Opens) := fun _ _ => trivial
    have hz1 : ⊤ ≤ zz ⁻¹ᵁ U₀ TF.X Z := hzO
    have hz2 : ⊤ ≤ zz ⁻¹ᵁ (L₀ TF.X Z la).U (pIdx _ (inc₀ TF.X Z) k') := fun s hs => mem_pIdx.2 (hzk hs)
    have hπ1 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ (⊤ : (X₀ TF.Y Z).Opens) := fun _ _ => trivial
    have hπ2 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ L.U k := by rw [e2]; exact hk
    have hz3 : ⊤ ≤ zz ⁻¹ᵁ (L.pull (π₀ TF.X Z)).U (pIdx L (π₀ TF.X Z) k) := fun s hs => mem_pIdx.2 (hπ2 hs)
    have hz4 : ⊤ ≤ zz ⁻¹ᵁ (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))).U
        (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) := fun s hs => ⟨hz2 hs, hz3 hs⟩
    have hu : IsUnit (H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G) := by
      rw [H0.val_ofSec]
      exact (w.s (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)).isUnit.map (GlobalTheory.TangentOrigin.evalPt zz _ hz4)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℂˣ, ∀ g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0),
        evR _ _ g.1 yy = c0.val * H0.val (TF.X.pt yy ≫ TF.X.inc) k' hO hk' (secOf TF.X _ g) :=
      ⟨_, fun g => evR_eq_val_secOf g hO hQ htt⟩
    refine ⟨c0 * hu.unit, fun t => ?_⟩
    show evR _ _ (f t).1 yy = _
    rw [hc0 (f t)]
    rw [val_congr_pt (p := flagStr TF.X) (B := TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0))
      ((FlagCover.pt_inc TF.X yy).trans hzz.symm) k' hO hk' hzO hzk]
    rw [show H0.val (zz ≫ inc₀ TF.X Z) k' hzO hzk (secOf TF.X _ (f t)) =
        H0.val zz (pIdx _ (inc₀ TF.X Z) k') hz1 hz2 (sec₀ TF.X Z _ (f t)) from
      (H0.val_pull (inc₀ TF.X Z) le_rfl zz (pIdx _ _ k') hz1 hz2 hzO hzk _).symm]
    rw [hf' t, val_restr_eq le_top zz _ hTop hz1 hz2]
    have e4 : H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) =
        H0.val (v ≫ j₀ TF.Y Z) k le_top hk t :=
      (H0.val_pull (π₀ TF.X Z) le_top zz (pIdx _ _ k) hTop hz3 hπ1 hπ2 t).trans (val_congr_pt e2 k hπ1 hπ2 le_top hk t)
    have e5 : H0.val zz (pIdx _ (inc₀ TF.X Z) k') hTop hz2 (sOf t) =
        H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) *
          H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G :=
      C.val_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) zz
        hTop hz3 hz4 hz2
    rw [e5, e4, Units.val_mul, IsUnit.unit_spec]
    ring

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClassStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degreeOneObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb1 | exact GlobalTheory.Obs.exists_isOb1 | (intros; apply GlobalTheory.Obs.exists_isOb1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClassStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degreeTwoObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb2 | exact GlobalTheory.Obs.exists_isOb2 | (intros; apply GlobalTheory.Obs.exists_isOb2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumAdditiveLineBundleIsogeny
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DescNorm

theorem twist_descCompat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f L φ → DescCompat f L (twist f L φ u) := by
  intro X Y f L φ u hφ z i i' j j' hi hi' hj hj'
  have m : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b → (𝟙 (pullback f f)) z ∈ chart f L a b :=
    fun a b ha hb => ⟨ha, hb⟩
  simp only [twist, map_mul]
  rw [gm_res (𝟙 _) z le_top (m i' j' hi' hj'), gm_res (𝟙 _) z le_top (m i j hi hj), hφ z i i' j j' hi hi' hj hj']
  ac_rfl

theorem descentDatum_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  intro K _ _ A A' B _ _ _ q P hA hA' hB hq _ _ _ hP hadd hzero hker
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso _ P hP (GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel K A A' B q P hA hA' hB hq hP hadd hker)
  obtain ⟨τ, hτ⟩ := hzero
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family K A A' B q P τ hP hτ φ₀ hφ₀
  have hc : DescCompat (q ▷ B).left P (twist (q ▷ B).left P φ₀ u) := twist_descCompat _ P φ₀ u hφ₀
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ P _ hP hc
  have h1 := GlobalTheory.T.descentCocycleDefect_normalised_eq_one K A A' B q P τ hP _ D hu hD
  have h2 := GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero K A A' B q hB D
  refine ⟨twist (q ▷ B).left P φ₀ u, hc, fun w i j k hi hj hk => ?_⟩
  have e := hD _ (𝟙 _) w i j k hi hj hk
  rw [← h2 w, h1 w, _root_.one_mul, Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.DescNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearFormStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_tuple_prescribed_member_linearForm : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a₀ : Fin m → X), IsCone bar φ γ → NoEquivRays O γ → (∀ x, x ≠ 0 → ∃ j, 0 < γ j x x) → Supports bar φ d γ a₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ μ : Fin (s + 1) → X, ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧ Dominant bar φ (D * d) N₁ W γ a ∧ ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  first | exact @GlobalTheory.Poinc.DomTuple.exists_dominant | exact GlobalTheory.Poinc.DomTuple.exists_dominant | (intros; apply GlobalTheory.Poinc.DomTuple.exists_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  first | exact @GlobalTheory.PtExt.exists_isEpsGen_of_isCob | exact GlobalTheory.PtExt.exists_isEpsGen_of_isCob | (intros; apply GlobalTheory.PtExt.exists_isEpsGen_of_isCob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  first | exact @GlobalTheory.KeyVals.DualBasis.exists_isDual | exact GlobalTheory.KeyVals.DualBasis.exists_isDual | (intros; apply GlobalTheory.KeyVals.DualBasis.exists_isDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  first | exact @GlobalTheory.Poinc.exists_sharpOver_domain | exact GlobalTheory.Poinc.exists_sharpOver_domain | (intros; apply GlobalTheory.Poinc.exists_sharpOver_domain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback : ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → ∀ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ → (∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) → ∀ (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsSquare f₁ f₂ → ∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ)) := by
  first | exact @GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | exact GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | (intros; apply GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_coordinates_through_immersion : ∀ (R : Type) [CommRing R] [IsLocalRing R] (N : ℕ) (Y : Over (Sp (ResidueField R))), Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N), IsImmersion j → j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → ∀ y : Y.left, ∃ (W0 : (PSpace R N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O ∧ (O : Set Y.left) ⊆ j ⁻¹' W0 ∧ τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R N ∧ Etale e ∧ e ≫ pullback.snd _ _ = O.ι ≫ Y.hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0 := by
  first | exact @GlobalTheory.Mum.exists_etale_coords_lift_immersion | exact GlobalTheory.Mum.exists_etale_coords_lift_immersion | (intros; apply GlobalTheory.Mum.exists_etale_coords_lift_immersion <;> assumption)
end

