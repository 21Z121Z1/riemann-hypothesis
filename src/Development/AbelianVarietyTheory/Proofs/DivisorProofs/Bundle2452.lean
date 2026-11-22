import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteOrder

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem two_smul_pow {G M : Type*} [Group G] [AddCommGroup M] (q : G → M) (q1 : q 1 = 0)
    (hq : ∀ x y : G, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹) (ψ : G) (n : ℕ) :
    (2 : ℤ) • q (ψ ^ n) = ((n : ℤ) * (n + 1)) • q ψ + ((n : ℤ) * (n - 1)) • q ψ⁻¹ := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q1]
  | one => simp [two_zsmul]
  | more n h0 h1 =>
    have h := hq (ψ ^ (n + 1)) ψ
    rw [← pow_succ, pow_succ ψ n, mul_inv_cancel_right, ← pow_succ] at h
    push_cast at h1 ⊢
    linear_combination (norm := module) (2 : ℤ) • h - h0 + (2 : ℤ) • h1

theorem pull_one_eq_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h0 : pull (η[A]).left c = 0 := GlobalTheory.cechPic_sp_field_eq_zero K _
  rw [Hom.one_def, Over.comp_left, pull_comp, h0, map_zero]

theorem pull_iter {S : Scheme.{0}} {A : Over S} (σ : A ≅ A) (c : Pic A.left)
    (h : pull σ.hom.left c = c) (m : ℕ) : pull (GlobalTheory.SerreField.iter σ m).hom.left c = c := by
  induction m with
  | zero => exact pull_id c
  | succ m ih =>
    change pull ((GlobalTheory.SerreField.iter σ m).hom.left ≫ σ.hom.left) c = c
    rw [pull_comp, h, ih]

theorem eff_add_nsmul {X : Scheme.{0}} [IsIntegral X] {a b : Pic X} (ha : Eff a) (hb : Eff b) (k : ℕ) :
    Eff (a + k • b) := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact eff_add _ _ ih hb

theorem exists_ge_cast_ne_zero (K : Type) [Field K] (t : ℕ) : ∃ n : ℕ, t ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : (t : K) = 0
  · exact ⟨t + 1, by omega, by simp [h]⟩
  · exact ⟨t, le_rfl, h⟩

theorem finiteOrder_of_const_of_cube :
    GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  intro hConst hCube K _ _ A _ _ hA L hL hAmp σ hσ hfix
  haveI : IsIntegral A.left := GlobalTheory.SS.isIntegral_of_abelian A hA
  let q : (A ⟶ A) → Pic A.left := fun u => pull u.left (cls L hL)
  have q1 : q 1 = 0 := pull_one_eq_zero A _
  have hq : ∀ x y : A ⟶ A, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹ := by
    intro x y
    have h : q (x * y * y⁻¹) + q x + q y + q y⁻¹ = q (x * y) + q (x * y⁻¹) + q (y * y⁻¹) + q 1 :=
      hCube K A hA L hL hAmp (cls L hL) x y y⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, q1, add_zero, add_zero] at h
    exact h.symm
  obtain ⟨d, hd, r, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hAmp
  have heff : ∀ u : A ⟶ A, Eff ((d : ℤ) • q u) := fun u => by
    have h := eff_pull_of_veryAmpleBy K A.hom _ r s (GlobalTheory.AbLaw.isLB_pw hL d) hs u.left inferInstance
    rwa [cls_pw hL, map_zsmul] at h
  obtain ⟨t₀, ht₀⟩ := hConst K A hA L hL hAmp
    ((2 * d : ℤ) • (q (𝟙 A) + q (𝟙 A) + q (𝟙 A) + q (𝟙 A)⁻¹))
  obtain ⟨n, hn, hnK⟩ := exists_ge_cast_ne_zero K t₀
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hnK)
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA (k + 1) hnK
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.SerreField.exists_iter_fix σ (𝟙_ (Over (Sp K))) (k + 1)
  refine ⟨m, hm0, ?_⟩
  have hx : q (GlobalTheory.SerreField.iter σ m).hom = q (𝟙 A) := (pull_iter σ _ hfix m).trans (pull_id _).symm
  have hxm : IsMonHom (GlobalTheory.SerreField.iter σ m).hom := inferInstance
  generalize (GlobalTheory.SerreField.iter σ m).hom = x at hm hx hxm ⊢
  have hu : IsMonHom (x * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, e⟩ := hdiv _ hu (fun y hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hm y hy, Category.comp_id, mul_inv_cancel])
  have h1 := hq x (𝟙 A)
  rw [hx, e] at h1
  have h2 := two_smul_pow q q1 hq ψ (k + 1)
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * ((k + 1) * (k + 2))) (hn.trans ?_) ψ hψ ?_
    · nlinarith [Nat.zero_le k, Nat.mul_le_mul_right ((k + 1) * (k + 2)) hd]
    · have h3 := eff_add_nsmul (eff_add _ _ (heff (x * 𝟙 A)) (heff (x * 𝟙 A))) (heff ψ⁻¹) ((k + 1) * k)
      convert h3 using 1
      change _ - _ • q ψ = _
      rw [← natCast_zsmul, ← natCast_zsmul]
      push_cast at h2 ⊢
      linear_combination (norm := module) (d : ℤ) • h2 - (2 * d : ℤ) • h1
  rw [hψ1, one_pow] at e
  exact mul_inv_eq_one.1 e

end GlobalTheory.AmpleFiniteOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_one_left_eq_zero {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0 := GlobalTheory.ThetaExtend.pic_local (R := K) _
  rw [Hom.one_def, Over.comp_left, pull_comp, h, map_zero]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem pull_pow_left (hcube : CubeSt) {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L)
    (c : Pic A.left) (ψ : A ⟶ A) (n : ℕ) :
    pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c := by
  have hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c =
      2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c := by
    intro n
    have h := hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹
    have e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1) := mul_inv_cancel_right _ _
    have e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2) := (pow_succ _ _).symm
    have e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n := by rw [pow_succ, mul_inv_cancel_right]
    have e4 : ψ * ψ⁻¹ = 1 := mul_inv_cancel _
    rw [e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero] at h
    rw [two_nsmul]
    exact h.symm
  have key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c +
      ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c =
      (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, pull_one_left_eq_zero]; simp
      · rw [pow_one]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := eq_sub_of_add_eq (hrec n)
      rw [show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]
      rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1),
        choose_two_succ n]
      push_cast
      module
  exact (key n).1

theorem separatedSt_of_const_cube : ConstSt → CubeSt → SeparatedSt := by
  intro hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu
  haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  obtain ⟨d, hd, n0, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
  have heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL)) := by
    intro φ
    rw [← cls_pw hL (d : ℤ)]
    exact eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance
  have heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL)) := by
    intro φ j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using heff φ
    | succ j hj ih =>
      push_cast
      rw [add_zsmul, one_zsmul]
      exact eff_add _ _ ih (heff φ)
  obtain ⟨t₀, ht₀⟩ := hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))
  have hN : t₀ + 2 < Q ^ (t₀ + 2) := Nat.lt_pow_self (by omega)
  obtain ⟨ψ, hψ, rfl⟩ := hu (t₀ + 2)
  have hpow := pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_
    · have h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2 := by
        rw [choose_two_succ]; omega
      have h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2 :=
        Nat.le_mul_of_pos_left _ hd
      omega
    · have hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2 := Nat.choose_pos (by omega)
      have e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) -
          (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) =
          (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL) := by
        rw [hpow, map_zsmul, ← natCast_zsmul]
        push_cast
        module
      rw [e]
      exact heffn _ _ hb
  rw [hψ1, one_pow]

end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank

open ReciprocityTheory.ChartRestriction.G.FD

theorem abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact abs_wtOf_le la _

theorem sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]; linarith
    · have hb := fun i => abs_le.1 (abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring

end GlobalTheory.BergRank

namespace GlobalTheory.BergRank

theorem berg_sup_rank : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := GlobalTheory.T.sup_constant_log_bound D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    GlobalTheory.T.level_geometry_weight_bound hP.p6 D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := GlobalTheory.T.cuspFormRank_le_bergmanBound_goodCover D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ

end GlobalTheory.BergRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem app_bijective_of_flat_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R)
    (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y →
    IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  intro R _ S Y Z π y p q hqc hqs hbij hy H V
  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hV : IsIso (p.app V) := GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens p (fun W ↦
    have : IsAffine W.1 := W.2
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
      ((isPullback_morphismRestrict p W.1).flip.paste_horiz H.flip)) V
  exact (ConcreteCategory.isIso_iff_bijective _).mp hV

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveAffineOpenFlatBaseChangeProper
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AffInj

theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

example : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom :=
  @app_injective_of_isPullback

end GlobalTheory.AffInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem appTop_injective_of_surjective_toSpec_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  intro R _ _ S π hπ hS
  rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : π ⁻¹ᵁ (Sp R).basicOpen r = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hr, Scheme.basicOpen_zero]
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ.surj x
  have hy : y ∈ π ⁻¹ᵁ (Sp R).basicOpen r := hx
  rw [h1] at hy
  exact hy.elim

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_injective_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  first | exact @GlobalTheory.Obs.sig_inj_of_flat | exact GlobalTheory.Obs.sig_inj_of_flat | (intros; apply GlobalTheory.Obs.sig_inj_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  first | exact @GlobalTheory.Obs.sig_natural | exact GlobalTheory.Obs.sig_natural | (intros; apply GlobalTheory.Obs.sig_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V → Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  first | exact @GlobalTheory.FormalAlg.baseChange_quotient | exact GlobalTheory.FormalAlg.baseChange_quotient | (intros; apply GlobalTheory.FormalAlg.baseChange_quotient <;> assumption)
end

