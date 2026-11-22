import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0089
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
section
noncomputable section
namespace GlobalTheory.CartanInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

variable {p q : ℕ}

def l1 {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

def Kc (p q : ℕ) : Set (UpqT p q) := {k | IsKC (UpqT.mat k)}

def eP (B : Fin p → Fin q → ℂ) : UpqT p q :=
  GlobalTheory.CompactDualExists.expU ⟨pY B, (pY_mem B).1⟩

theorem mat_eP (B : Fin p → Fin q → ℂ) : UpqT.mat (eP B) = NormedSpace.exp (pY B) := rfl

theorem continuous_eP : Continuous (eP : (Fin p → Fin q → ℂ) → UpqT p q) :=
  GlobalTheory.CompactDualExists.continuous_expU.comp (continuous_pY.subtype_mk _)

theorem mat_mul (x y : UpqT p q) : UpqT.mat (x * y) = UpqT.mat x * UpqT.mat y := rfl

theorem mat_one : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem isKC_fromBlocks (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    IsKC (Matrix.fromBlocks U 0 0 V : Mat p q) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

theorem mem_Kc_iff (k : UpqT p q) : k ∈ Kc p q ↔
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      UpqT.mat k = Matrix.fromBlocks U 0 0 V := by
  constructor
  · intro hk
    have hk' : IsKC (UpqT.mat k) := hk
    have h : UpqT.mat k = Matrix.fromBlocks (UpqT.mat k).toBlocks₁₁ 0 0 (UpqT.mat k).toBlocks₂₂ := by
      ext a b
      rcases a with i | i <;> rcases b with j | j
      · rfl
      · exact hk' _ _ (by simp [sameBlock])
      · exact hk' _ _ (by simp [sameBlock])
      · rfl
    have hJ := GlobalTheory.UpqTopology.mat_unitary k
    rw [h] at hJ
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at hJ
    refine ⟨_, ?_, _, ?_, h⟩
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.1
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.2.2.2
  · rintro ⟨U, -, V, -, h⟩
    show IsKC (UpqT.mat k)
    rw [h]; exact isKC_fromBlocks U V

theorem star_mul_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : (UpqT.mat k)ᴴ * UpqT.mat k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at hU hV
  rw [h]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU, hV]

theorem mat_inv_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : UpqT.mat k⁻¹ = (UpqT.mat k)ᴴ := by
  have h1 : UpqT.mat k * UpqT.mat k⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc UpqT.mat k⁻¹ = ((UpqT.mat k)ᴴ * UpqT.mat k) * UpqT.mat k⁻¹ := by
        rw [star_mul_of_mem_Kc hk, one_mul]
    _ = (UpqT.mat k)ᴴ := by rw [mul_assoc, h1, mul_one]

def Ksg (p q : ℕ) : Subgroup (UpqT p q) where
  carrier := Kc p q
  one_mem' := (mem_Kc_iff 1).2 ⟨1, one_mem _, 1, one_mem _, by rw [mat_one, Matrix.fromBlocks_one]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := (mem_Kc_iff x).1 hx
    obtain ⟨U', -, V', -, h'⟩ := (mem_Kc_iff y).1 hy
    show IsKC (UpqT.mat (x * y))
    rw [mat_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (UpqT.mat x⁻¹)
    rw [mat_inv_of_mem_Kc hx]
    have hx' : IsKC (UpqT.mat x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

theorem exists_cartan (g : UpqT p q) : ∃ k ∈ Kc p q, ∃ B, g = k * eP B := by
  obtain ⟨U, hU, V, hV, h⟩ := isCartan_cartanB g
  refine ⟨g * (eP fun i j => cartanB g i j)⁻¹, (mem_Kc_iff _).2 ⟨U, hU, V, hV, ?_⟩, _,
    (inv_mul_cancel_right _ _).symm⟩
  have h1 : UpqT.mat (eP fun i j => cartanB g i j) * UpqT.mat (eP fun i j => cartanB g i j)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, h, Matrix.mul_assoc]
  exact (congrArg _ h1).trans (Matrix.mul_one _)

theorem cartanB_mul_eP {k : UpqT p q} (hk : k ∈ Kc p q) (B : Fin p → Fin q → ℂ) :
    cartanB (k * eP B) = Matrix.of B := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  exact cartanB_eq ⟨U, hU, V, hV, by rw [mat_mul, h]; rfl⟩

theorem polJ_aOf (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (sinhcAd_mulVec_of_sq_eigen p q _ _ _ (adMat_sq_mulVec_eigP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (det_eigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem polJ_pOf (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) =
    (∏ i ∈ Finset.range (min p q), shc (2 * singVal B i) * shc (singVal B i) ^ (2 * (max p q - min p q))) *
    ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q),
      if i < j then (shc (singVal B i - singVal B j) * shc (singVal B i + singVal B j)) ^ 2 else 1 := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have e : pOf B = Matrix.fromBlocks U 0 0 V * aOf p q (singVal B) * Matrix.fromBlocks Uᴴ 0 0 Vᴴ := by
    conv_lhs => rw [hB]
    simp [aOf, pOf, singVal, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [e, Conj.polJ_conj p q _ _ _ (by simp [Matrix.fromBlocks_multiply, h1, h2]) (isKC_fromBlocks _ _)
    (isKC_fromBlocks _ _), polJ_aOf, RootProd.prod_shc_rootP]

theorem one_le_shc (x : ℝ) : 1 ≤ shc x := by
  unfold shc
  split_ifs with hx
  · exact le_rfl
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [le_div_iff_of_neg h, one_mul]; exact Real.sinh_le_self_iff.2 h.le
    · rw [le_div_iff₀ h, one_mul]; exact Real.self_le_sinh_iff.2 h.le

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl h

theorem one_le_polJ (B : Matrix (Fin p) (Fin q) ℂ) : 1 ≤ polJ (pOf B) := by
  rw [polJ_pOf]
  refine one_le_mul_of_one_le_of_one_le (one_le_prod_real fun i _ => ?_)
    (one_le_prod_real fun i _ => one_le_prod_real fun j _ => ?_)
  · exact one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_pow₀ (one_le_shc _))
  · split_ifs
    · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_shc _))
    · exact le_rfl

theorem shc_le_exp (x : ℝ) : shc x ≤ Real.exp |x| := by
  have key : ∀ y : ℝ, 0 < y → Real.sinh y / y ≤ Real.exp y := by
    intro y hy
    rw [div_le_iff₀ hy, Real.sinh_eq, div_le_iff₀ two_pos]
    have h1 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(2 * y))
    have h3 := Real.exp_pos y
    rw [h1]; nlinarith
  unfold shc
  split_ifs with hx
  · exact Real.one_le_exp (abs_nonneg x)
  · rcases lt_or_gt_of_ne hx with h | h
    · have := key (-x) (neg_pos.2 h)
      rwa [Real.sinh_neg, neg_div_neg_eq, ← abs_of_neg h] at this
    · rw [abs_of_pos h]; exact key x h

theorem singVal_nonneg (B : Matrix (Fin p) (Fin q) ℂ) (i : ℕ) : 0 ≤ singVal B i :=
  LinearMap.singularValues_nonneg _ _

theorem sum_sum_ite_lt (m : ℕ) (s : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then s i + s j else 0) =
      ((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (s := Finset.range (m + 1))
      (fun j hj => if_neg (by have := Finset.mem_range.1 hj; omega)), add_zero]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem polJ_le_exp (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) ≤
    Real.exp (2 * (((p + q : ℕ) : ℝ) - 1) * ∑ i ∈ Finset.range (min p q), singVal B i) := by
  have h0 := singVal_nonneg B
  have hs : ∀ x, 0 ≤ shc x := fun x => zero_le_one.trans (one_le_shc x)
  rw [polJ_pOf]
  set s := singVal B
  set m := min p q with hm
  set D := max p q - min p q with hD
  have hA : ∏ i ∈ Finset.range m, shc (2 * s i) * shc (s i) ^ (2 * D) ≤
      Real.exp ((2 + 2 * (D : ℝ)) * ∑ i ∈ Finset.range m, s i) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => mul_nonneg (hs _) (pow_nonneg (hs _) _)) fun i _ => ?_
    have a1 := shc_le_exp (2 * s i)
    have a2 := shc_le_exp (s i)
    rw [abs_of_nonneg (by linarith [h0 i])] at a1 a2
    calc _ ≤ Real.exp (2 * s i) * Real.exp (s i) ^ (2 * D) :=
          mul_le_mul a1 (pow_le_pow_left₀ (hs _) a2 _) (pow_nonneg (hs _) _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hB : (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
      if i < j then (shc (s i - s j) * shc (s i + s j)) ^ 2 else 1) ≤
      Real.exp (4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i)) := by
    rw [← sum_sum_ite_lt, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
      fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
    split_ifs
    · have a1 := (shc_le_exp (s i - s j)).trans (Real.exp_le_exp.2
        (show |s i - s j| ≤ s i + s j from abs_le.2 ⟨by linarith [h0 i], by linarith [h0 j]⟩))
      have a2 := shc_le_exp (s i + s j)
      rw [abs_of_nonneg (by linarith [h0 i, h0 j])] at a2
      calc _ ≤ (Real.exp (s i + s j) * Real.exp (s i + s j)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (hs _) (hs _)) (mul_le_mul a1 a2 (hs _) (Real.exp_pos _).le) 2
        _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    · simp
  refine (mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity) (Real.exp_pos _).le).trans (le_of_eq ?_)
  have e : ((p + q : ℕ) : ℝ) = D + 2 * m := by
    have : p + q = D + 2 * m := by omega
    exact_mod_cast this
  rw [← Real.exp_add, e]; ring_nf

end GlobalTheory.CartanInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WeilPairingGalois

theorem exists_top_agree (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable)
    (hM : ∀ x ∈ S, x ∈ M) :
    ∃ s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, cj ⊤ s x = cj M ρ x := by
  have hle : IntermediateField.adjoin ℚ S ≤ M := IntermediateField.adjoin_le_iff.2 hM
  haveI : Countable (IntermediateField.adjoin ℚ S) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ S).trans ?_
    have h1 : Cardinal.mk S ≤ Cardinal.aleph0 := Cardinal.le_aleph0_iff_set_countable.2 hS
    simp [h1]
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq (IntermediateField.adjoin ℚ S)
    (IntermediateField.adjoin ℚ S).val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨(τ.toRingHom.comp (⊤ : IntermediateField ℚ ℂ).val.toRingHom).toRatAlgHom, fun x hx => ?_⟩
  have h := hτ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos (hM x hx), dif_pos (IntermediateField.mem_top (F := ℚ) (x := x))]
  exact h

theorem cj_top_mul (s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (x y : ℂ) :
    cj ⊤ s (x * y) = cj ⊤ s x * cj ⊤ s y := by
  simp only [cj, TaylorLogMetric.liftM, dif_pos (IntermediateField.mem_top (F := ℚ))]
  rw [← map_mul]; rfl

theorem cj_one (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : cj M ρ 1 = 1 := by
  simp only [cj, TaylorLogMetric.liftM, dif_pos M.one_mem]
  exact map_one ρ

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  simp only [ee, ← Complex.exp_add]; congr 1; push_cast; ring

theorem latticeRiemannForm_add_left (Λ : AddSubgroup ℂ) (x y w : ℂ) : gl3FieldFirst Λ (x + y) w = gl3FieldFirst Λ x w + gl3FieldFirst Λ y w := by
  simp only [gl3FieldFirst, add_mul, Complex.add_im, add_div]

theorem latticeRiemannForm_add_right (Λ : AddSubgroup ℂ) (x y w : ℂ) : gl3FieldFirst Λ w (x + y) = gl3FieldFirst Λ w x + gl3FieldFirst Λ w y := by
  simp only [gl3FieldFirst, map_add, mul_add, Complex.add_im, add_div]

theorem latticeRiemannForm_natCast_mul_comm (Λ : AddSubgroup ℂ) (n : ℕ) (x w : ℂ) : gl3FieldFirst Λ x (n * w) = gl3FieldFirst Λ (n * x) w := by
  simp only [gl3FieldFirst, map_mul, map_natCast]; congr 2; ring

theorem expTwoPiI_latticeRiemannForm_of_mem (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {x w : ℂ} (hx : x ∈ Λ) (hw : w ∈ Λ) : ee (gl3FieldFirst Λ x w) = 1 := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 hx)
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 hw)
  have ha := (GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h).2.2.2.1
  have h1 : ((m * L.ω₁ + n * L.ω₂) * (starRingEnd ℂ) (p * L.ω₁ + q * L.ω₂)).im =
      ((m * q - n * p : ℤ) : ℝ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
    simp; ring
  have h2 : ∃ k : ℤ, gl3FieldFirst Λ (m * L.ω₁ + n * L.ω₂) (p * L.ω₁ + q * L.ω₂) = k := by
    rw [gl3FieldFirst, h1, ha]
    generalize (L.ω₁ * starRingEnd ℂ L.ω₂).im = c
    rcases lt_trichotomy c 0 with hc | hc | hc
    · refine ⟨-(m * q - n * p), ?_⟩
      rw [abs_of_neg hc]; have := hc.ne; push_cast; field_simp
    · exact ⟨0, by simp [hc]⟩
    · refine ⟨(m * q - n * p), ?_⟩
      rw [abs_of_pos hc]; have := hc.ne'; field_simp
  obtain ⟨k, hk⟩ := h2
  rw [hk, ee, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem value_shift (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (x l : ℂ)
    (hG : ∀ z, U1 Λ (2 * l) G z = G z) :
    U1 Λ (x + 2 * l) G 0 = ee (gl3FieldFirst Λ x l) * U1 Λ x G 0 := by
  have h := hG x
  simp only [U1, zero_add] at h ⊢
  rw [← h, ee, gl3FieldFirst, mul_assoc (G _), ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [Complex.ofReal_div, Complex.im_eq_sub_conj]
  simp only [map_add, map_mul, Complex.conj_conj, map_ofNat]
  by_cases hA : (area Λ : ℂ) = 0
  · simp [hA]
  · field_simp
    ring

theorem isLattice_of_periodPair (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  rw [h, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

theorem periodPair_of_isLattice (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨⟨w₁, w₂, hi⟩, fun z => ?_⟩
  rw [PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

theorem periodPair_conj (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) :
    ∃ L' : PeriodPair, ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice := by
  obtain ⟨-, -, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have hne : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 ≠ 0 := by
    have e : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 =
        ρ (TaylorLogMetric.liftM M (g2 Λ) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 Λ) ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, map_ne_zero]
    intro h0
    apply hd
    have := congrArg (fun y : M => (y : ℂ)) h0
    simp only [TaylorLogMetric.liftM, dif_pos h2, dif_pos h3] at this
    exact this
  obtain ⟨L', ha, hb⟩ := hex _ _ hne
  obtain ⟨e2, e3, -, -, -, hun, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨_, e2.trans ha, e3.trans hb⟩
  have : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    hun _ (hs.1.trans (e2.trans ha).symm) (hs.2.trans (e3.trans hb).symm)
  exact ⟨L', fun z => by rw [this]; rfl⟩

theorem value_shift_sg (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (x : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    coef1 (U1 Λ (x + 2 * l) (sgStar Λ)) 0 = ee (gl3FieldFirst Λ x l) * coef1 (U1 Λ x (sgStar Λ)) 0 := by
  simp only [coef1, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  refine value_shift Λ _ x l fun z => ?_
  have h2 : 2 * l ∈ Λ := by rw [two_mul]; exact Λ.add_mem hl hl
  rw [(GlobalTheory.OddTheta.sgStar_laws Λ (isLattice_of_periodPair L Λ h)).1.2.2.2 _ h2 z,
    if_pos (by simpa using hl), one_mul]

theorem value_ne_zero (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {x : ℂ} (hx : x ∉ Λ) : coef1 (U1 Λ x (sgStar Λ)) 0 ≠ 0 := by
  simp only [coef1, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, U1, zero_add]
  exact mul_ne_zero
    (fun h0 => hx (((GlobalTheory.OddTheta.sgStar_laws Λ (isLattice_of_periodPair L Λ h)).2.1 x).1 h0))
    (Complex.exp_ne_zero _)

theorem natMul_mem {Λ : AddSubgroup ℂ} (n : ℕ) {x : ℂ} (hx : x ∈ Λ) : (n : ℂ) * x ∈ Λ := by
  rw [← nsmul_eq_mul]; exact Λ.nsmul_mem hx n

theorem weil_top (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ)
    (s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ s) (a b a' b' : ℂ) (m : ℕ) (hm : 0 < m)
    (ha : (m : ℂ) * a ∈ lamOf D cc δ) (hb : (m : ℂ) * b ∈ lamOf D cc δ)
    (haa : Adp1 ⊤ s (lamOf D cc δ) m a a') (hbb : Adp1 ⊤ s (lamOf D cc δ) m b b') :
    cj ⊤ s (ee (gl3FieldFirst (lamOf D cc δ) a b)) = ee (gl3FieldFirst (lamConj ⊤ s (lamOf D cc δ)) a' b') := by
  obtain ⟨L, hL⟩ := periodPair_of_isLattice _
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1
  obtain ⟨L', hL'⟩ := periodPair_conj L _ hL ⊤ s IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨hex, hun, -, hadd, -, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ s hK IntermediateField.mem_top IntermediateField.mem_top
  have hgal := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ hc ⊤ s hK IntermediateField.mem_top IntermediateField.mem_top
  generalize lamOf D cc δ = Λ at *
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hmul : ∀ (n : ℕ) t t', StarPt ⊤ s Λ t t' → StarPt ⊤ s Λ (n * t) (n * t') := by
    intro n t t' h
    induction n with
    | zero => exact Or.inl ⟨by simp, by simp⟩
    | succ n ih => simpa [add_mul] using hadd _ _ _ _ ih h
  have ha' : (m : ℂ) * a' ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ haa).1 (by convert ha using 1; push_cast; field_simp)
    convert this using 1; push_cast; field_simp
  have hb' : (m : ℂ) * b' ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ hbb).1 (by convert hb using 1; push_cast; field_simp)
    convert this using 1; push_cast; field_simp
  have e1 : gl3FieldFirst Λ a b = gl3FieldFirst Λ (a / m) (m * b) := by
    rw [latticeRiemannForm_natCast_mul_comm]; congr 1; field_simp
  have e2 : gl3FieldFirst (lamConj ⊤ s Λ) a' b' = gl3FieldFirst (lamConj ⊤ s Λ) (a' / m) (m * b') := by
    rw [latticeRiemannForm_natCast_mul_comm]; congr 1; field_simp
  rw [e1, e2]
  rcases id haa with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [expTwoPiI_latticeRiemannForm_of_mem L Λ hL h1 hb, expTwoPiI_latticeRiemannForm_of_mem L' _ hL' h2 hb', cj_one]
  obtain ⟨t, ht⟩ := hex (a / m / ((2 * (2 * m ^ 2) : ℕ) : ℂ))
    ⟨2 * (2 * m ^ 2) * m ^ 2, by positivity, by convert ha using 1; push_cast; field_simp⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  obtain ⟨u, hu⟩ := hex (b / m / 2)
    ⟨2 * m ^ 2, by positivity, by convert hb using 1; push_cast; field_simp⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have hx : StarPt ⊤ s Λ (a / m) (4 * m ^ 2 * t) := by
    convert hmul (2 * (2 * m ^ 2)) _ _ ht using 1 <;> push_cast <;> field_simp <;> ring
  have hy : StarPt ⊤ s Λ (b / m) (2 * u) := by
    convert hmul 2 _ _ hu using 1 <;> push_cast <;> field_simp
  have hν := (hun _ _ _ hx).1 haa
  have hμ := (hun _ _ _ hy).1 hbb
  have hx' : 4 * m ^ 2 * t ∉ lamConj ⊤ s Λ := by
    rcases hx with h | h
    · exact absurd h.1 h1
    · exact h.2.1
  have hl' : 2 * m ^ 2 * u ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ hy).1 (by convert hb using 1; push_cast; field_simp)
    convert this using 1; push_cast; ring
  have g1 := hgal (a / m) (4 * m ^ 2 * t) (2 * m ^ 2) (by positivity)
    (by convert ha using 1; push_cast; field_simp)
    (by unfold Adp1; convert ht using 1; push_cast; field_simp; ring)
    (fun _ => IntermediateField.mem_top) 0
  have g2 := hgal (a / m + 2 * (m * b)) (4 * m ^ 2 * t + 2 * (2 * m ^ 2 * u)) (2 * m ^ 2) (by positivity)
    (by convert Λ.add_mem ha (natMul_mem (2 * m ^ 2) hb) using 1; push_cast; field_simp)
    (by unfold Adp1; convert hadd _ _ _ _ ht hu using 1 <;> push_cast <;> field_simp <;> ring)
    (fun _ => IntermediateField.mem_top) 0
  rw [value_shift_sg L Λ hL _ hb, value_shift_sg L' _ hL' _ hl', cj_top_mul, g1] at g2
  rw [mul_right_cancel₀ (value_ne_zero L' _ hL' hx') g2]
  have e3 : (4 * m ^ 2 * t : ℂ) = a' / m + (4 * m ^ 2 * t - a' / m) := by ring
  have e4 : (2 * m ^ 2 * u : ℂ) = m * b' + m * (m * (2 * u - b' / m)) := by field_simp; ring
  rw [e3, latticeRiemannForm_add_left, ee_add, expTwoPiI_latticeRiemannForm_of_mem L' _ hL' hν hl', mul_one, e4, latticeRiemannForm_add_right, ee_add,
    latticeRiemannForm_natCast_mul_comm _ m _ (m * _), latticeRiemannForm_natCast_mul_comm _ m _ (2 * u - _),
    expTwoPiI_latticeRiemannForm_of_mem L' _ hL' (by convert ha' using 1; field_simp) hμ, mul_one]

theorem weilPairingGalois_all : ∀ D : D7, WeilPairingGaloisAlt D := by
  intro D cc δ hc M ρ hK h2 h3 a b a' b' m hm ha hb haa hbb he
  set Λ := lamOf D cc δ with hΛ
  let S : Set ℂ := (Set.range (fun k : D.host.K => D.host.φ₀ (k : D.host.E)) ∪
    {g2 Λ, g3 Λ, ee (gl3FieldFirst Λ a b), wpF Λ (a / m), wpD Λ (a / m), wpF Λ (b / m), wpD Λ (b / m)}) ∩ M
  haveI : Countable D.host.K := by
    haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
    infer_instance
  have hS : S.Countable :=
    ((Set.countable_range _).union (Set.toFinite _).countable).mono Set.inter_subset_left
  obtain ⟨s, hs⟩ := exists_top_agree M ρ S hS fun x hx => hx.2
  have hlam : lamConj ⊤ s Λ = lamConj M ρ Λ := by
    have e2 := hs (g2 Λ) ⟨Or.inr (by simp), h2⟩
    have e3 := hs (g3 Λ) ⟨Or.inr (by simp), h3⟩
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hK' : FixK D ⊤ s := fun k =>
    ⟨IntermediateField.mem_top, (hs _ ⟨Or.inl ⟨k, rfl⟩, (hK k).1⟩).trans (hK k).2⟩
  have hst : ∀ t t', (t = a / m ∨ t = b / m) → StarPt M ρ Λ t t' → StarPt ⊤ s Λ t t' := by
    intro t t' ht h
    unfold StarPt
    rw [hlam]
    rcases h with h | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hs _ ⟨Or.inr (by rcases ht with rfl | rfl <;> simp), h3⟩]
      · rw [h6, hs _ ⟨Or.inr (by rcases ht with rfl | rfl <;> simp), h4⟩]
  rw [← hs _ ⟨Or.inr (by simp), he⟩, ← hlam]
  exact weil_top D cc δ hc s hK' a b a' b' m hm ha hb (hst _ _ (Or.inl rfl) haa)
    (hst _ _ (Or.inr rfl) hbb)

end GlobalTheory.WeilPairingGalois
end
end

