import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0100
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0092
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlipSimilar
section
noncomputable section

namespace GlobalTheory.HCComm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def flip {n : ℕ} (M : Mt g n) : Mt g n := (M.submatrix Fin.revPerm Fin.revPerm).transpose

theorem flip_apply {n : ℕ} (M : Mt g n) (i j : Fin n) : flip M i j = M j.rev i.rev := rfl

theorem flip_mul {n : ℕ} (M N : Mt g n) : flip (M * N) = flip N * flip M := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv M N Fin.revPerm Fin.revPerm Fin.revPerm, Matrix.transpose_mul]

theorem flip_one {n : ℕ} : flip (1 : Mt g n) = 1 := by
  unfold flip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem flip_flip {n : ℕ} (M : Mt g n) : flip (flip M) = M := by
  ext i j
  simp only [flip_apply, Fin.rev_rev]

private lemma one_submatrix_rev_mul_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    ((1 : Mt g n).submatrix Fin.rev id * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, Matrix.one_apply]

private lemma mul_one_submatrix_rev_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    (A * (1 : Mt g n).submatrix Fin.rev id) i j = A i j.rev := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp Fin.revPerm]
  simp [Matrix.one_apply]

theorem flip_similar {n : ℕ} (M : Mt g n) : ∃ P : Mt g n, IsUnit P ∧ P * M = flip M * P := by

  obtain ⟨Q, hQ, hQM⟩ := GlobalTheory.SimilarTranspose.main (ZMod g) (Fin n) M
  have hJJ : (1 : Mt g n).submatrix Fin.rev id * (1 : Mt g n).submatrix Fin.rev id = 1 := by
    ext i j
    rw [one_submatrix_rev_mul_apply]
    simp [Matrix.one_apply]
  have hflip : flip M = (1 : Mt g n).submatrix Fin.rev id * M.transpose *
      (1 : Mt g n).submatrix Fin.rev id := by
    ext i j
    rw [mul_one_submatrix_rev_apply, one_submatrix_rev_mul_apply, flip_apply, Matrix.transpose_apply]
  generalize (1 : Mt g n).submatrix Fin.rev id = J at hJJ hflip
  refine ⟨J * Q, IsUnit.mul ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩ hQ, ?_⟩
  have hJJQ : J * (J * Q) = Q := by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hflip]
  simp only [Matrix.mul_assoc, hJJQ, hQM]

def flipG {n : ℕ} (x : Gn g n) : Gn g n where
  val := flip (x : Mt g n)
  inv := flip ((x⁻¹ : Gn g n) : Mt g n)
  val_inv := by rw [← flip_mul, Units.inv_mul, flip_one]
  inv_val := by rw [← flip_mul, Units.mul_inv, flip_one]

theorem flipG_coe {n : ℕ} (x : Gn g n) : ((flipG x : Gn g n) : Mt g n) = flip (x : Mt g n) := rfl

theorem flipG_mul {n : ℕ} (x y : Gn g n) : flipG (x * y) = flipG y * flipG x := by
  apply Units.ext
  simp only [flipG_coe, Units.val_mul, flip_mul]

theorem flipG_inv {n : ℕ} (x : Gn g n) : flipG x⁻¹ = (flipG x)⁻¹ := by
  apply Units.ext
  rfl

theorem flipG_flipG {n : ℕ} (x : Gn g n) : flipG (flipG x) = x := by
  apply Units.ext
  simp only [flipG_coe, flip_flip]

def flipE (n : ℕ) : Gn g n ≃ Gn g n := ⟨flipG, flipG, flipG_flipG, flipG_flipG⟩

theorem flipG_conj {n : ℕ} (x : Gn g n) : ∃ p : Gn g n, flipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, hPx⟩ := flip_similar (x : Mt g n)
  refine ⟨hP.unit, Units.ext ?_⟩
  have h1 : ((hP.unit : Gn g n) : Mt g n) = P := hP.unit_spec
  have h2 : ((hP.unit : Gn g n) : Mt g n) * ((hP.unit⁻¹ : Gn g n) : Mt g n) = 1 := hP.unit.mul_inv
  rw [h1] at h2
  rw [flipG_coe, Units.val_mul, Units.val_mul, h1, hPx, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos (Units.isUnit x)]
  exact Units.ext rfl

theorem class_flip {n : ℕ} {α : Gn g n → ℂ} (hα : IsClass α) (M : Mt g n) :
    α (toG (flip M)) = α (toG M) := by
  by_cases hM : IsUnit M
  · have e1 : toG M = hM.unit := by
      unfold toG
      rw [dif_pos hM]
    have e2 : toG (flip M) = flipG hM.unit := by
      rw [← toG_coe (flipG hM.unit), flipG_coe, IsUnit.unit_spec]
    obtain ⟨p, hp⟩ := flipG_conj hM.unit
    rw [e1, e2, hp]
    exact hα _ _
  · have hF : ¬ IsUnit (flip M) := by
      intro h
      apply hM
      have e : flip (flip M) = ((flipG h.unit : Gn g n) : Mt g n) := by
        rw [flipG_coe, IsUnit.unit_spec]
      rw [flip_flip] at e
      rw [e]
      exact Units.isUnit _
    unfold toG
    rw [dif_neg hM, dif_neg hF]

theorem inPar_flip {a b : ℕ} (M : Mt g (a + b)) : InPar b (flip M) ↔ InPar a M := by
  constructor
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    have := h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)
    rwa [flip_apply, Fin.rev_rev, Fin.rev_rev] at this
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    rw [flip_apply]
    exact h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)

private lemma entN_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dif_pos ⟨hx, hy⟩]

theorem tl_flip {a b : ℕ} (M : Mt g (a + b)) : tl b (flip M) = flip (br a b M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_of_lt (flip M) i j (by omega) (by omega),
    entN_of_lt M (a + j.rev) (a + i.rev) (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma entN_eq_apply_of_lt_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dif_pos ⟨hx, hy⟩]

theorem br_flip {a b : ℕ} (M : Mt g (a + b)) : br b a (flip M) = flip (tl a M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_eq_apply_of_lt_of_lt (flip M) (b + i) (b + j) (by omega) (by omega),
    entN_eq_apply_of_lt_of_lt M j.rev i.rev (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma sum_flipG_conj_eq_sum_conj_flipG {n : ℕ} (F : Gn g n → ℂ) (w : Gn g n) :
    ∑ y : Gn g n, F (flipG (y⁻¹ * w * y)) = ∑ y : Gn g n, F (y⁻¹ * flipG w * y) := by
  refine Fintype.sum_bijective (fun y => (flipG y)⁻¹) ?_ _ _ ?_
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun v => flipG v⁻¹, ?_, ?_⟩
    · intro y
      simp only [inv_inv, flipG_flipG]
    · intro v
      simp only [flipG_flipG, inv_inv]
  · intro y
    simp only [flipG_mul, flipG_inv, inv_inv, mul_assoc]

private lemma sum_conj_conj_eq_sum_conj {n : ℕ} (F : Gn g n → ℂ) (w p : Gn g n) :
    ∑ y : Gn g n, F (y⁻¹ * (p * w * p⁻¹) * y) = ∑ y : Gn g n, F (y⁻¹ * w * y) := by
  refine Fintype.sum_bijective (fun y => p⁻¹ * y) (Group.mulLeft_bijective p⁻¹) _ _ ?_
  intro y
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ),
    IsClass α → IsClass β → n = a + b → hc a b α β n = hc b a β α n := by
  intro g _ a b n α β hα hβ hn
  subst hn
  funext x

  have key : ∀ z : Gn g (a + b),
      (if InPar b ((flipG z : Gn g (a + b)) : Mt g (a + b)) then
        β (toG (tl b ((flipG z : Gn g (a + b)) : Mt g (a + b)))) *
          α (toG (br b a ((flipG z : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      (if InPar a (z : Mt g (a + b)) then
        α (toG (tl a (z : Mt g (a + b)))) * β (toG (br a b (z : Mt g (a + b)))) else 0) := by
    intro z
    simp only [flipG_coe, inPar_flip, tl_flip, br_flip, class_flip hβ, class_flip hα]
    rw [mul_comm]
  have hcard : (Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card =
      (Finset.univ.filter fun p : Gn g (a + b) => InPar b (p : Mt g (a + b))).card := by
    refine Finset.card_nbij' flipG flipG ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe, inPar_flip]
      exact hq
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe]
      apply (inPar_flip (a := a) (b := b) (flip (q : Mt g (a + b)))).mp
      rwa [flip_flip]
    · intro q _
      exact flipG_flipG q
    · intro q _
      exact flipG_flipG q
  obtain ⟨p, hp⟩ := flipG_conj x
  let Fba : Gn g (a + b) → ℂ := fun z =>
    if InPar b (z : Mt g (a + b)) then
      β (toG (tl b (z : Mt g (a + b)))) * α (toG (br b a (z : Mt g (a + b)))) else 0
  have e1 : (∑ y : Gn g (a + b), if InPar a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)) then
      α (toG (tl a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) *
        β (toG (br a b ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
    calc _ = ∑ y : Gn g (a + b), Fba (flipG (y⁻¹ * x * y)) :=
          Finset.sum_congr rfl fun y _ => (key _).symm
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * flipG x * y) := sum_flipG_conj_eq_sum_conj_flipG Fba x
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
          rw [hp]
          exact sum_conj_conj_eq_sum_conj Fba x p
  simp only [hc, hcT]
  rw [hcard]
  congr 1

end GlobalTheory.HCComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
section
open Formalism.MainNotions.S NumberField GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.TensDer

theorem hasDerivAt_orbit_tens : ∀ (B : RowsAut) (E : gInf B) (u u' : ∀ v, B.H v), (∀ v, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v)) (u' v) 0) → (∀ v, B.σ v 1 = 1) → open Classical in HasDerivAt (orbit B E (B.tens u)) (∑ v, B.tens (Function.update u v (u' v))) 0 := by
  intro B E u u' hd h1
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hfun : orbit B E (B.tens u) =
      fun t => (m.restrictScalars ℝ) (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) := by
    funext t
    have := B.tens_spec.2.1
    rw [ContinuousMultilinearMap.coe_restrictScalars, hm]
    unfold orbit
    rw [this]
    congr 1
  have h0 : (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0) = u := by
    funext v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
  have hpi : HasDerivAt (fun t v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) u' 0 :=
    hasDerivAt_pi.2 hd
  have hF := (m.restrictScalars ℝ).hasFDerivAt (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0)
  have := hF.comp_hasDerivAt (0 : ℝ) hpi
  rw [hfun]
  rw [h0, ContinuousMultilinearMap.linearDeriv_apply] at this
  simp only [ContinuousMultilinearMap.coe_restrictScalars, Function.comp_def, hm] at this ⊢
  exact this

end GlobalTheory.TensDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcParamEqWeightStepZeroAddRho
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem hcParam_eq_weight_step_zero_add_rho : ∀ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), (((D.hcW u τ).u i : ℚ) : ℝ) = ((Formalism.L2.Forms.lamT u 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℝ) + ((rhoVec D.R.k i : ℚ) : ℝ) := by
  intro D u τ i
  rw [Formalism.L2.Forms.lamT_zero]
  have h0 := (D.fm u).lam_eq 0 (Nat.zero_le _) τ (Fin.cast D.R.N_zero.symm i)
  rw [dif_pos (show (Fin.cast D.R.N_zero.symm i : ℕ) < D.R.k from i.2)] at h0
  have hq : ((D.hcW u τ).u i : ℚ) =
      (((D.fm u).lam 0 τ).w (Fin.cast D.R.N_zero.symm i) : ℚ) + rhoVec D.R.k i := by
    rw [h0, hcToWeightQ]
    simp
  rw [hq]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelBoundByWeight
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernelWeight

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y

def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y

theorem exists_coord {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j) := by
    apply Subgroup.inv_mem
    exact Subgroup.mem_iInf.1 hn.1.2 j
  have h1 : n⁻¹ x ∈ S.spanTo g (j + 1) := (hu.1 x).2 hx
  have h2 : n⁻¹ x - x ∈ S.spanTo g j := hu.2 x hx
  have h3 : n⁻¹ x ∈ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _) h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h3
  have h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    have : i ≠ j.castSucc := by
      rintro rfl
      simp at hi'
    show hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg this]
  have h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x := by
    have := h4 h2
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  refine ⟨c, ?_, ?_⟩
  · have : x = n (n⁻¹ x) := (n.apply_symm_apply x).symm
    rw [this, ← hc, map_sum]
    simp
  · show _ = hfLin L S.Hm (gs j) x
    rw [← h5, ← hc, map_sum]
    have : ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0 := by
      intro i
      rw [map_smul]
      show c i * hf L S.Hm (g i) (gs j) = _
      rw [hd]; split_ifs <;> simp
    simp [this]

end

theorem kernel_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  have hW := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).2.1
  have hom : ‖S.om d Λ‖ = 1 := (GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ _ _ hW).2.2.2.2
  have hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1 := fun b u =>
    (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _

  have hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧
      S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1 := by
    intro w hw
    obtain ⟨Λ₁, h1, h2, -, -, h5⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF _ _ _ _ hw
    refine ⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩
    obtain ⟨al, hal, hal1⟩ := exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1
    obtain ⟨al', hal', hal1'⟩ := exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1
    rw [h5 al al' hal hal', hal1, hal1']
    rfl
  have huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂ :=
    fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)
  let P : Submodule L.O S.V → Prop := fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y
  let G : S.MW → ℂ := fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then
    S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0
  obtain ⟨hGn, hGs⟩ := (GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G
    (by
      intro w Λ₁ hw
      by_cases hP : P Λ₁
      · obtain ⟨Λ₂, h1, -, h3⟩ := hmove w hw.1
        rw [if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]
        exact if_pos ⟨Λ₁, hw, hP⟩
      · rw [if_neg hP]
        refine if_neg ?_
        rintro ⟨Λ₂, h1, h2⟩
        exact hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))
    (by
      intro w hw
      refine if_neg ?_
      rintro ⟨Λ₂, h1, -⟩
      exact hw h1.1)
  obtain ⟨-, hLn, hHn, -, hLb, hHb⟩ := GlobalTheory.T.hermitianMoves_total_measure_estimates L r k S hk j β βJ d Λ hT hF
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)
  set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH
  obtain ⟨hn2, hc2⟩ := hsm (-S.om d Λ) H hHn
  obtain ⟨hn3, hc3, -⟩ := hadd G _ hGn hn2
  have hb := (hadd _ _ hn3 hLn).2.2 (by
    intro w
    simp only [Pi.add_apply, hH, ind, G]
    by_cases hw : S.Mv (j + 1) d Λ w
    · by_cases hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁
      · rw [if_pos hex, if_pos hw]
        split_ifs <;> simp
      · have hl : ¬ S.NoLeak Λ w.2.1 := by
          intro hl
          obtain ⟨Λ₁, h1, h2, -⟩ := hmove w hw
          exact hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩
        rw [if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]
        simp [hom, hchi]
    · have hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ := by
        rintro ⟨Λ₂, h1, -⟩
        exact hw h1.1
      rw [if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]
      simp)
  rw [hc3, hc2] at hb
  have hcK : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  have hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤
      (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re +
        ‖cint (S.refA (j + 1) Λ) H‖ := by
    have e : cint (S.refA (j + 1) Λ) G =
        (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) +
          S.om d Λ * cint (S.refA (j + 1) Λ) H := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hb ?_)
    rw [norm_mul, hom, one_mul]
  have := mul_le_mul_of_nonneg_left hG hcK
  show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _
  rw [hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]
  linarith

end GlobalTheory.HL.KernelWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumnsStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ), inUJ ε h → hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  first | exact @GlobalTheory.hs_le_of_cols | exact GlobalTheory.hs_le_of_cols | (intros; apply GlobalTheory.hs_le_of_cols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspaceStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_unitriangular_move_frame_mem_flagSubspace : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  first | exact @GlobalTheory.FlagInv.inv_moves | exact GlobalTheory.FlagInv.inv_moves | (intros; apply GlobalTheory.FlagInv.inv_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactNormBoundedBesselClosedSubgroupStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S → ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  first | exact @GlobalTheory.SgInf.isCompact_normBounded | exact GlobalTheory.SgInf.isCompact_normBounded | (intros; apply GlobalTheory.SgInf.isCompact_normBounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBoundsStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → Submodule.span K (A : Set (Fin a → K)) = ⊤ → Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ size (Pi.basisFun K (Fin a)) X N) → largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ, ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧ Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤ (a : ℝ) * b * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  first | exact @GlobalTheory.HomCover.exists_hom_near | exact GlobalTheory.HomCover.exists_hom_near | (intros; apply GlobalTheory.HomCover.exists_hom_near <;> assumption)
end

