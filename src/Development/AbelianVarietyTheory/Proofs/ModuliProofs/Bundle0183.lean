import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open AdjointOfPairing in

theorem lbIso_cubeLB_of_pairing_adjoint : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L) := by
  intro hl k _ _ _ P a a' ha ha' H
  have := P.isAb.comm
  have out : ∀ r : P.A ⟶ P.A ⊗ P.A, (∃ t : LB.Gen (LB.LinComb P.L (fun i => r.left ≫ Out.rosatiφ P.A a a' i)
      Out.rosatiε), t.IsGen) → ∃ t : ((LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε).pull r.left).Gen,
        t.IsGen := fun r ⟨t, ht⟩ => gen_chartPull (chartPullOut P.L _ _ _ _ fun _ => rfl) t ht
  obtain ⟨t, ht⟩ := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian hl.globalFns k P.A P.A (LB.LinComb P.L (Out.rosatiφ P.A a a') Out.rosatiε) P.L
    P.isAb P.isAb P.isLB P.ample
    (DVR.linComb_isLB P.L P.isLB _ _)
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.one_mul, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
    ((TorsionDense.dense_torsion P hl.irred hl.kerPow).mono (Set.biUnion_subset_biUnion_left
      fun x hx => hx.elim fun n hx => out _ (exists_gen_fibre hl P a a' n (Nat.cast_ne_zero.2 hx.1.ne') x hx.2
        fun y c hy => H n x y c hx.1 hx.2 hy)))
    (out _ (exists_gen_of_formEq_zero P.isLB fun U _ h => by
      rw [prod_ros, MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel))
  obtain ⟨u, hu, -⟩ := exists_gen P.isLB
    (φ' := Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A, snd P.A P.A ≫ a'] I.down).left)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst P.A P.A ≫ a, snd P.A P.A] I.down).left))
    (ε' := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -(-1) ^ (2 - I.down.card)))
    (fun V _ h => by
      have p := prod_ros a a' (fst P.A P.A) (snd P.A P.A) h
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_neg _ _ p).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2)))
        (K' := ULift.{0} (Finset (Fin 2))) (U := V) _ (NormRos.prod_square (fst P.A P.A) (snd P.A P.A ≫ a') h)
        (DVR.prod_neg _ _ (NormRos.prod_square (fst P.A P.A ≫ a) (snd P.A P.A) h))).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact lbIso_of_gen u hu

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

theorem lam_iso_of_weil_pairings : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)) := by
  intro hL k _ _ P P' α p d hα hp _ hW
  haveI : IsCommMonObj P.A := P.isAb.comm
  have fib : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ P.A) (n : ℕ), 0 < n → n.Coprime p → x ^ n = 1 →
      ∃ t : LB.Gen ((LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))).pull
        (lift (toUnit P.A ≫ x) (𝟙 P.A)).left), t.IsGen := by
    intro x n hn hnp hx
    obtain ⟨u, hu, v⟩ := exists_gen_lam hL.globalFns hL.cube P (𝟙 P.A) d n x hx
    obtain ⟨u', hu', v'⟩ := exists_gen_lam hL.globalFns hL.cube P' α 1 n x hx
    refine exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _ ?_
    refine lbIso_of_invariant P.isLB P'.isLB _ _ _ _ (Out.mulA P.A n).left
      (I := {y : 𝟙_ (Over (Sp k)) ⟶ P.A // y ^ n = 1}) (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
      (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
        obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
        exact ⟨a, b, c, e⟩) k P n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
      (fun y z J J' hJ hJ' => ?_)
    · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
        MonObj.comp_one, _root_.one_mul]
    · obtain ⟨c, hc, -⟩ := (hL.weil _ P n _).1 x y.1 hx y.2
      obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
        ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
          Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
      have e : unitOn (c ^ d) = unitOn c ^ d := map_pow (Units.map _) c d
      have h₁ := v y.1 (unitOn c) y.2 (by rw [Category.comp_id, Category.comp_id]; exact hc) z J hJ
      have h₂ := v' y.1 (unitOn (c ^ d)) y.2 (hW n x y.1 c hn hnp hx y.2 hc) z J' hJ'
      rw [pow_one, e] at h₂
      refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
      exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h
  refine T.seesaw_triviality_on_dense_fibres_product_abelian hL.globalFns k P.A P.A (LB.div (abelian₂ P.A (P'.L.pull α.left)) (abelian₂ P.A (lbPow P.L d))) P.L
    P.isAb P.isAb P.isLB P.ample
    (LB.isLB_div (DVR.linComb_isLB _ (pull_isLB P'.isLB _) _ _)
      (DVR.linComb_isLB _ (DVR.linComb_isLB _ P.isLB _ _) _ _)) ?_ ?_ ?_
  · have := fib 1 1 one_pos (Nat.coprime_one_left p) (one_pow _)
    rwa [MonObj.comp_one] at this
  · refine (CoprimeTorsion.dense_torsion hL.ample hL.kerPow hL.irred k P hp).mono ?_
    exact Set.biUnion_subset_biUnion_left fun x ⟨n, hn, hnp, hx⟩ => fib x n hn hnp hx
  · obtain ⟨u, hu⟩ := exists_gen_axis (A := P.A) P.isLB (𝟙 _) d
    obtain ⟨u', hu'⟩ := exists_gen_axis (A := P.A) P'.isLB α.left 1
    exact exists_gen_div_pull P.L P'.L (𝟙 _) α.left d 1 (lamφ P.A) lamε _
      (lbIso_of_gens P.isLB P'.isLB _ _ _ _ u hu u' hu')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolIsoSymmetrisedRoot
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.MulRoot

open CechPic

theorem pull_pow_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (n : ℕ) :
    pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls P.L P.isLB) = (n ^ 2) • cls P.L P.isLB := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (h S P n)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, neg_smul, one_smul] at e
  rw [← natCast_zsmul, Nat.cast_pow]
  exact (add_neg_eq_zero.1 e).symm

theorem pull_inv_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen) :
    pull ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  have := P.isAb.comm
  have h₀ := pull_pow_pol h P 0
  have h₂ := pull_pow_pol h P 2
  have e := lam_mul_left P.isLB hΘ (𝟙 P.A) (𝟙 P.A)⁻¹ (𝟙 P.A)
  rw [mul_inv_cancel, lam_one_left] at e
  rw [pow_zero] at h₀
  rw [pow_two (𝟙 P.A)] at h₂
  simp only [lam, inv_mul_cancel, h₀, h₂, Over.id_left, pull_id] at e
  linear_combination (norm := module) e

theorem lam_eq_zero (laws : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {D : LB P.A.left} (hD : D.IsLB) (hΘ : ∃ t : LB.Gen (Theta P.A D), t.IsGen) {m : ℕ} (hm : 0 < m)
    (h : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls D hD) = 0) {T : Over (Sp K)} (x y : T ⟶ P.A) :
    lam (cls D hD) x y = 0 := by
  have := P.isAb.comm
  have := P.isAb.smooth
  have kill : ∀ {T : Over (Sp K)} (x : T ⟶ P.A), pull (x ^ m).left (cls D hD) = 0 := fun x => by
    have e : x ^ m = x ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, h, map_zero]
  have two : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) (x ^ (m * m)) y = 0 := fun {T} x y => by
    rw [pow_mul, lam_pow_left hD hΘ, ← lam_pow_right hD hΘ]
    have k₁ := kill (1 : T ⟶ P.A)
    rw [one_pow] at k₁
    rw [lam, ← mul_pow, kill, kill, kill, k₁]
    simp
  have hN : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).IsLB := LB.isLB_linComb hD _ _
  have val : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A),
      cls _ (pull_isLB hN (lift x y).left) = lam (cls D hD) x y := fun x y => by
    rw [cls_pull hN, cls_cube_two hD, pull_lam, lift_fst, lift_snd]
  have gen : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) x y = 0 →
      ∃ s : ((cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).pull (lift x y).left).Gen, s.IsGen := fun x y e =>
    (cls_eq_zero_iff _).1 ((val x y).trans e)
  have main := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian laws.globalFns K P.A P.A _ P.L P.isAb P.isAb P.isLB P.ample hN
    (gen _ _ (lam_one_left _ _)) (by
      have hs : Surjective (𝟙 P.A ^ (m * m)).left := (laws.mulN _ P (m * m) (Nat.mul_pos hm hm)).2.2.1
      refine dense_image_points (𝟙 P.A ^ (m * m)) _ fun u => gen _ _ ?_
      rw [MonObj.comp_pow, MonObj.comp_pow]
      exact two _ _) (gen _ _ (lam_one_right _ _))
  rw [← val, cls_pull hN, (cls_eq_zero_iff hN).2 main, map_zero]

end GlobalTheory.MulRoot

namespace GlobalTheory

open CechPic MulRoot

theorem pol_iso_symmetrised_root : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (m : ℕ), Odd m → N.IsLB → LBIso (lbPow P.L (m ^ 2)) (N.pull ((𝟙 P.A) ^ m).left) → LBIso P.L (LB.LinComb N (K := Fin 2) ![𝟙 P.A.left, (GrpObj.inv : P.A ⟶ P.A).left] ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]) := by
  intro laws cube K _ _ P N m hm hN hiso
  have := P.isAb.comm
  have hL := P.isLB
  have hD : (LB.div N P.L).IsLB := LB.isLB_div hN hL
  have hd : cls _ hD = cls N hN - cls P.L hL := cls_div hN hL hD
  have h₁ : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hN _)).2 hiso
    rw [cls_lbPow hL, cls_pull hN] at e
    rw [hd, map_sub, ← e, pull_pow_pol laws.mulPull, sub_self]
  have hlam := fun x y : P.A ⟶ P.A => lam_eq_zero laws P hD (cube _ P _ hD) hm.pos h₁ x y
  have h₀ : pull (1 : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e : (1 : P.A ⟶ P.A) = 1 ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id, one_pow]
    rw [e, Over.comp_left, pull_comp, h₁, map_zero]
  have hadd : ∀ x y : P.A ⟶ P.A, pull (x * y).left (cls _ hD) = pull x.left (cls _ hD) + pull y.left (cls _ hD) :=
    fun x y => by
      have e := hlam x y
      rw [lam, h₀] at e
      linear_combination (norm := module) e
  have hpow : ∀ n : ℕ, pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls _ hD) = n • cls _ hD := fun n => by
    induction n with
    | zero => rw [pow_zero, h₀, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, Over.id_left, pull_id, succ_nsmul]
  have hmd : m • cls _ hD = 0 := (hpow m).symm.trans h₁
  have hinv := hadd (𝟙 P.A) (𝟙 P.A)⁻¹
  rw [mul_inv_cancel, h₀, Over.id_left, pull_id] at hinv
  have hsym := pull_inv_pol laws.mulPull P (cube _ P _ hL)
  have ei : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := Category.id_comp _
  rw [ei] at hinv hsym
  rw [hd, map_sub, hsym] at hinv
  rw [hd] at hmd
  obtain ⟨k, rfl⟩ := hm
  have a : (1 - ((2 * k + 1 : ℕ) : ℤ)) / 2 = -k := by push_cast; omega
  have b : (((2 * k + 1 : ℕ) : ℤ) + 1) / 2 = k + 1 := by push_cast; omega
  rw [← cls_eq_iff hL (LB.isLB_linComb hN _ _), cls_linComb hN, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, a, b]
  linear_combination (norm := module) ((k : ℤ) + 1) • hinv + hmd

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolume
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV Filter Topology

namespace GlobalTheory.VolEx

theorem tendsto_pow_div_pow {i k : ℕ} (h : i ≤ k) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ i / (e : ℝ) ^ k) atTop (𝓝 (if i = k then 1 else 0)) := by
  split_ifs with hik
  · subst hik
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    rw [div_self (by positivity)]
  · exact (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne h hik)).comp tendsto_natCast_atTop_atTop

theorem tendsto_eval_div_pow (Q : Polynomial ℚ) {k : ℕ} (h : Q.natDegree ≤ k) :
    Tendsto (fun e : ℕ => ((Q.eval (e : ℚ) : ℚ) : ℝ) / (e : ℝ) ^ k) atTop (𝓝 (Q.coeff k : ℝ)) := by
  have h1 : Tendsto (fun e : ℕ => ∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * ((e : ℝ) ^ i / (e : ℝ) ^ k)) atTop
      (𝓝 (∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * (if i = k then 1 else 0))) :=
    tendsto_finsetSum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h1
  refine h1.congr fun e => ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem vAmp_of_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {m : ℕ} {s : Fin (m + 1) → M.Sec}
    (h : AbLaw.VeryAmpleBy p M s) : VAmp p M s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem vol_of_eventually {p : X ⟶ Sp K} {M : LB X} (hex : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r) (φ : ℕ → ℝ)
    (hφ : ∀ᶠ e : ℕ in atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) {k : ℕ} {δ : ℝ}
    (hδ : Tendsto (fun e : ℕ => φ e / (e : ℝ) ^ k) atTop (𝓝 δ)) : Vol p M k δ := by
  have : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ ((∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) → (r : ℝ) = φ e) := by
    intro e
    by_cases h : ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e
    · obtain ⟨r, h1, h2⟩ := h
      exact ⟨r, h1, fun _ => h2⟩
    · obtain ⟨r, h1⟩ := hex e
      exact ⟨r, h1, fun h' => absurd h' h⟩
  choose h h1 h2 using this
  refine ⟨h, h1, hδ.congr' ?_⟩
  filter_upwards [hφ] with e he
  rw [h2 e he]

theorem vol_nonneg {p : X ⟶ Sp K} {M : LB X} {k : ℕ} {δ : ℝ} (h : Vol p M k δ) : 0 ≤ δ := by
  obtain ⟨h, -, hh⟩ := h
  exact ge_of_tendsto' hh fun e => by positivity

theorem exists_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  intro hL _ K _ _ P M hM hA
  have hex : ∀ (N : LB P.A.left), N.IsLB → ∀ e, ∃ r, SectionsHaveFiniteDimension P.A.hom (lbPow N e) r := fun N hN e =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow N e) 0 (LB.isLB_linComb hN _ _)).1
  have : IsProper P.A.hom := P.isAb.proper
  obtain ⟨d, hd, m, s, hs⟩ :=
    ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).1 hA).exists_veryAmpleBy (R := K) P.A.hom
  have hH : (lbPow M d).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem K (Fin (m + 1)) _ P.A.hom (lbPow M d) s hH (vAmp_of_veryAmpleBy hs)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have volM : ∀ k, Q.natDegree ≤ k → Vol P.A.hom M k ((Q.coeff k : ℝ) / (d : ℝ) ^ k) := by
    intro k hk
    refine (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M k hM).2.2.2.2.1 d _ hd hA ?_
    rw [mul_div_cancel₀ _ (by positivity)]
    refine vol_of_eventually (hex _ hH) _ ?_ (tendsto_eval_div_pow Q hk)
    filter_upwards [hQ] with e ⟨r, h1, h2, _⟩
    exact ⟨r, h1, by rw [← h2]; norm_cast⟩
  have volL : ∀ k, P.g ≤ k → Vol P.A.hom P.L k (if P.g = k then 1 else 0) := by
    intro k hk
    refine vol_of_eventually (hex _ P.isLB) (fun e => (e : ℝ) ^ P.g) ?_ (tendsto_pow_div_pow hk)
    filter_upwards [eventually_ge_atTop 1] with e he
    exact ⟨e ^ P.g, PowSec.exists_basis_sections hL.globalSectionsRank K P e he, by push_cast; rfl⟩
  have dom : ∀ (A B : LB P.A.left), A.IsLB → B.IsLB → Out.RelAmple P.A A → ∃ c : ℕ, ∀ k δ δ',
      Vol P.A.hom B k δ → Vol P.A.hom A k δ' → δ ≤ (c : ℝ) ^ k * δ' := by
    intro A B hA hB ha
    obtain ⟨c, ⟨⟨t, ht⟩, -⟩, hc⟩ := ((GlobalTheory.T.eventually_section_and_relAmple_pow_div K P A B hA hB ha).and (eventually_ge_atTop 1)).exists
    refine ⟨c, fun k δ δ' h1 h2 => ?_⟩
    exact ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P B k hB).2.2.2.2.2 (lbPow A c) t (LB.isLB_linComb hA _ _) ht).2 _ _ h1
      ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P A k hA).2.2.2.1 c δ' hc h2)
  have hdeg : Q.natDegree ≤ P.g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc⟩ := dom P.L M P.isLB hM P.ample
    have h1 := hc _ _ _ (volM _ le_rfl) (volL _ hlt.le)
    rw [if_neg hlt.ne, mul_zero] at h1
    have h2 := le_antisymm h1 (vol_nonneg (volM _ le_rfl))
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have h3 : Q.leadingCoeff = 0 := by exact_mod_cast h2
      rw [Polynomial.leadingCoeff_eq_zero] at h3
      rw [h3] at hlt
      simp at hlt
    · exact absurd h2 (by positivity)
  refine ⟨_, ?_, volM _ hdeg⟩
  obtain ⟨c, hc⟩ := dom M P.L hM P.isLB hA
  have h1 := hc _ _ _ (volL _ le_rfl) (volM _ hdeg)
  rw [if_pos rfl] at h1
  refine lt_of_le_of_ne (vol_nonneg (volM _ hdeg)) fun h => ?_
  rw [← h, mul_zero] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory.VolEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpleGlobal

theorem exists_lift_fieldExtension {S S' : Scheme.{0}} (f : S' ⟶ S) {K₀ : Type} [Field K₀] (x : Sp K₀ ⟶ S)
    (a : Sp K₀) (q : S') (h : f q = x a) :
    ∃ (K : Type) (_ : Field K) (i : K₀ →+* K) (u : Sp K ⟶ S'), u ≫ f = spMap i ≫ x := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback q a h
  refine ⟨(pullback f x).residueField z, inferInstance,
    (Spec.preimage ((pullback f x).fromSpecResidueField z ≫ pullback.snd f x)).hom,
    (pullback f x).fromSpecResidueField z ≫ pullback.fst f x, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom _) ≫ x
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]

theorem relAmple_of_pointwise {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [IsProper G.hom] [Flat G.hom]
    (M : LB G.left) (hM : M.IsLB)
    (hproj : ∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left),
      IsPullback φ B.hom G.hom y → IsProjOver B.hom)
    (hpt : ∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (φ : G'.left ⟶ G.left) (L' : LB G'.left),
      IsPullback φ G'.hom G.hom f ∧ L'.IsLB ∧ LBIso L' (M.pull φ) ∧ p ∈ Set.range f ∧ Out.RelAmple G' L') :
    Out.RelAmple G M := by
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S G M hM inferInstance inferInstance (fun s => ?_)
  obtain ⟨V, hV, hsV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (by first | exact AlgebraicGeometry.isBasis_affine_open S | exact S.isBasis_affineOpens | exact AlgebraicGeometry.Scheme.isBasis_affineOpens S | exact isBasis_affineOpens S)) (show s ∈ (⊤ : S.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV'⟩
  let y : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV'.fromSpec
  let q := hV'.primeIdealOf ⟨s, hsV⟩
  have hq : hV'.fromSpec q = s := hV'.fromSpec_primeIdealOf ⟨s, hsV⟩
  let g : Γ(S, V) →+* q.asIdeal.ResidueField := algebraMap _ _
  let B : Over (Spec (CommRingCat.of Γ(S, V))) := Over.mk (pullback.snd G.hom y)
  have hB : IsPullback (pullback.fst G.hom y) B.hom G.hom y := IsPullback.of_hasPullback _ _
  have hLB : (M.pull (pullback.fst G.hom y)).IsLB := pull_isLB hM _
  have hflat : Flat B.hom := by
    first | (show Flat (pullback.snd G.hom y); infer_instance) | exact MorphismProperty.pullback_snd _ _ inferInstance
  have hprojB := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver _).2 (hproj _ y B _ hB)
  have hfib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B)
      ((M.pull (pullback.fst G.hom y)).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) := by
    obtain ⟨S', f, G', φ, L', hφ, hL', e, ⟨s', hs'⟩, hA'⟩ := hpt s
    let x : Sp q.asIdeal.ResidueField ⟶ S := Spec.map (CommRingCat.ofHom g) ≫ y
    let a : Sp q.asIdeal.ResidueField := IsLocalRing.closedPoint _
    have ha : x a = s := by
      have hpt' : (Spec.map (CommRingCat.ofHom g)) a = q := by
        apply PrimeSpectrum.ext
        change Ideal.comap g (IsLocalRing.maximalIdeal _) = q.asIdeal
        rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
      first
        | (show y ((Spec.map (CommRingCat.ofHom g)) a) = s
           rw [hpt']
           exact hq)
        | exact (Scheme.comp_base_apply _ _ _).trans (by rw [hpt']; exact hq)
    obtain ⟨K, _, i, u, hu⟩ := exists_lift_fieldExtension f x a s' (hs'.trans ha.symm)
    have h₂ : IsPullback (pullback.fst G.hom (spMap i ≫ x)) (pullback.snd G.hom (spMap i ≫ x)) G.hom
        (spMap i ≫ x) := IsPullback.of_hasPullback _ _
    have hA₂ := GlobalTheory.FibreAmple.relAmple_of_factor hM hφ h₂ u hu hL' e hA'
    exact GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))).paste_horiz hB) h₂
      (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA₂
  obtain ⟨r, hr, hA⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre Γ(S, V) B (M.pull (pullback.fst G.hom y)) hflat hprojB hLB
    q.asIdeal.ResidueField g (GlobalTheory.FibreAmple.residueField_fraction q.asIdeal) hfib
  let U₀ : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  let j := U₀.ι
  have : IsOpenImmersion y := by dsimp only [y]; infer_instance
  have : IsOpenImmersion j := by dsimp only [j]; exact inferInstance
  have hqr : q ∈ PrimeSpectrum.basicOpen r :=
    (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hr ((Ideal.algebraMap_residueField_eq_zero).2 h)
  refine ⟨(j ≫ y).opensRange, ⟨⟨q, hqr⟩, ?_⟩, ?_⟩
  · rw [← hq]
    rfl
  · have hu : (j ≫ y).isoOpensRange.inv ≫ (j ≫ y) = (j ≫ y).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    exact GlobalTheory.FibreAmple.relAmple_of_factor hM ((IsPullback.of_hasPullback B.hom j).paste_horiz hB)
      (isPullback_morphismRestrict G.hom _).flip _ hu (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA

theorem relAmple_of_polarised_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  intro E _ _ _ H S _ t hP hproj hpt
  have hflat : Flat t.G.hom := by
    first
      | exact inferInstance
      | (haveI := t.semi.smooth; infer_instance)
  refine relAmple_of_pointwise t.G t.PP.L t.PP.isLB hproj (fun p => ?_)
  obtain ⟨S', f, t', m, hp, hA, -⟩ := hpt p
  refine ⟨S', f, t'.G, m.cm.F, t'.PP.L, m.cart.1, t'.PP.isLB, ?_, hp, hA⟩
  first
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw.1⟩)
    | (obtain ⟨w, -, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact (hw : False))

end GlobalTheory.AmpleGlobal
end
end

