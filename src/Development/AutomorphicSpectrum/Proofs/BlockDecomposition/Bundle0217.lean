import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianUnitaryFlow
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve

section RingNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • Y)) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt

theorem hasDerivAt_exp_smul_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) Y 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

end RingNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_smul_mem_unitaryGroup {n : ℕ} (Y : Mat n) (hY : Yᴴ = -Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hc : (t • Y)ᴴ = -(t • Y) := by
    rw [conjTranspose_smul, hY]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_right]
  simp

theorem exists_unitary_curve : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y →
    ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧
      (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  intro n Y hY
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), exp_smul_mem_unitaryGroup Y hY t⟩,
    (continuous_exp_smul Y).subtype_mk _, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left s).smul_right t)
  · exact hasDerivAt_exp_smul_zero Y

end GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactor
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar.Chol

variable {n m k : ℕ}

def invRoot (P : Mat (n + 1)) : ℝ := (Real.sqrt (P 0 0).re)⁻¹

def col (P : Mat (n + 1)) (i : Fin n) : ℂ := P i.succ 0 * (invRoot P : ℂ)

def schur (P : Mat (n + 1)) : Mat n :=
  Matrix.of fun i j => P i.succ j.succ - col P i * star (col P j)

def step (σ : Mat n → Mat n) (P : Mat (n + 1)) : Mat (n + 1) :=
  Matrix.of fun i j =>
    Fin.cases (motive := fun _ => ℂ)
      (Fin.cases (motive := fun _ => ℂ) ((Real.sqrt (P 0 0).re : ℝ) : ℂ) (fun _ => 0) j)
      (fun i' => Fin.cases (motive := fun _ => ℂ) (col P i') (fun j' => σ (schur P) i' j') j) i

lemma step_zero_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) :
    step σ P 0 0 = ((Real.sqrt (P 0 0).re : ℝ) : ℂ) := rfl

lemma step_zero_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (j : Fin n) :
    step σ P 0 j.succ = 0 := rfl

lemma step_succ_zero (σ : Mat n → Mat n) (P : Mat (n + 1)) (i : Fin n) :
    step σ P i.succ 0 = col P i := rfl

lemma step_succ_succ (σ : Mat n → Mat n) (P : Mat (n + 1)) (i j : Fin n) :
    step σ P i.succ j.succ = σ (schur P) i j := rfl

lemma lead_pos {P : Mat (n + 1)} (hP : P.PosDef) : 0 < (P 0 0).re :=
  (Complex.pos_iff.1 (hP.diag_pos (i := 0))).1

lemma lead_eq {P : Mat (n + 1)} (hP : P.PosDef) : (((P 0 0).re : ℝ) : ℂ) = P 0 0 := by
  apply Complex.ext
  · simp
  · simpa using (Complex.pos_iff.1 (hP.diag_pos (i := 0))).2

lemma root_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    Real.sqrt (P 0 0).re * invRoot P = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.2 (lead_pos hP)).ne'

lemma lead_mul_invRoot {P : Mat (n + 1)} (hP : P.PosDef) :
    P 0 0 * ((invRoot P : ℂ) * (invRoot P : ℂ)) = 1 := by
  have h : (P 0 0).re * (invRoot P * invRoot P) = 1 := by
    have h1 := root_mul_invRoot hP
    have h2 := Real.mul_self_sqrt (lead_pos hP).le
    calc (P 0 0).re * (invRoot P * invRoot P)
        = (Real.sqrt (P 0 0).re * Real.sqrt (P 0 0).re) * (invRoot P * invRoot P) := by rw [h2]
      _ = (Real.sqrt (P 0 0).re * invRoot P) * (Real.sqrt (P 0 0).re * invRoot P) := by ring
      _ = 1 := by rw [h1]; ring
  rw [← lead_eq hP]
  exact_mod_cast h

lemma schur_posDef {P : Mat (n + 1)} (hP : P.PosDef) : (schur P).PosDef := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hcs : star ((invRoot P : ℝ) : ℂ) = (invRoot P : ℂ) := by simp
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, schur, of_apply, star_sub, star_mul', star_star, hH]
    ring
  · intro x hx
    set c : ℂ := (invRoot P : ℂ) with hc
    set w : ℂ := ∑ j, P 0 j.succ * x j with hw
    set u : ℂ := ∑ i, star (x i) * P i.succ 0 with hu
    set q : ℂ := ∑ i, star (x i) * ∑ j, P i.succ j.succ * x j with hq
    set t : ℂ := -(w * (c * c)) with ht
    let y : Fin (n + 1) → ℂ := Fin.cons t x
    have y0 : y 0 = t := rfl
    have ys : ∀ i : Fin n, y i.succ = x i := fun i => rfl
    have hy : y ≠ 0 := fun h => hx (funext fun i => by simpa [ys] using congrFun h i.succ)
    have hpos := hP.dotProduct_mulVec_pos hy
    have hW : ∑ j, star (col P j) * x j = w * c := by
      rw [hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, star_mul', hH, hcs, ← hc]
      ring
    have hrow : ∀ i, (schur P *ᵥ x) i = (∑ j, P i.succ j.succ * x j) - col P i * (w * c) := by
      intro i
      rw [← hW]
      simp only [mulVec, dotProduct, schur, of_apply, sub_mul, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    have hU : ∑ i, star (x i) * col P i = u * c := by
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [col, ← hc]
      ring
    have hL : star x ⬝ᵥ (schur P *ᵥ x) = q - (u * c) * (w * c) := by
      simp only [dotProduct, hrow, Pi.star_apply, mul_sub, Finset.sum_sub_distrib]
      congr 1
      generalize w * c = v
      rw [← hU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h0 : (P *ᵥ y) 0 = P 0 0 * t + w := by
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys, hw]
    have hs : ∀ i : Fin n, (P *ᵥ y) i.succ = P i.succ 0 * t + ∑ j, P i.succ j.succ * x j := by
      intro i
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, y0, ys]
    have hz : P 0 0 * t + w = 0 := by
      have := lead_mul_invRoot hP
      rw [← hc] at this
      rw [ht]
      linear_combination (-w) * this
    have hR : star y ⬝ᵥ (P *ᵥ y) = u * t + q := by
      rw [dotProduct, Fin.sum_univ_succ]
      simp only [Pi.star_apply, h0, hs, y0, ys, hz, mul_zero, zero_add, mul_add,
        Finset.sum_add_distrib]
      congr 1
      rw [hu, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hk : star x ⬝ᵥ (schur P *ᵥ x) = star y ⬝ᵥ (P *ᵥ y) := by
      rw [hL, hR, ht]
      ring
    rw [hk]
    exact hpos

lemma step_mul {σ : Mat n → Mat n} {P : Mat (n + 1)} (hP : P.PosDef)
    (hσ : σ (schur P) * (σ (schur P))ᴴ = schur P) : step σ P * (step σ P)ᴴ = P := by
  have hH : ∀ i j, star (P j i) = P i j := fun i j => hP.isHermitian.apply i j
  have hr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * (invRoot P : ℂ) = 1 := by
    exact_mod_cast root_mul_invRoot hP
  have hrr : ((Real.sqrt (P 0 0).re : ℝ) : ℂ) * ((Real.sqrt (P 0 0).re : ℝ) : ℂ) = P 0 0 := by
    rw [← lead_eq hP]
    exact_mod_cast Real.mul_self_sqrt (lead_pos hP).le
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ]
    simp [hrr]
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero]
    simp only [col, star_mul', hH]
    simp
    linear_combination (P 0 j.succ) * hr
  · simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_zero_zero, step_zero_succ,
      step_succ_zero, step_succ_succ]
    simp [col]
    linear_combination (P i.succ 0) * hr
  · have h := congrFun (congrFun hσ i) j
    simp only [mul_apply, conjTranspose_apply] at h
    simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_succ, step_succ_zero, step_succ_succ, h]
    simp [schur]

lemma contDiff_entry (i j : Fin m) : ContDiff ℝ ∞ (fun P : Mat m => P i j) :=
  contDiff_apply_apply ℝ ℂ i j

lemma contDiffOn_mat {s : Set (Mat k)} {f : Mat k → Mat m}
    (h : ∀ i j, ContDiffOn ℝ ∞ (fun P => f P i j) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => h i j

lemma contDiffOn_entry {s : Set (Mat k)} {f : Mat k → Mat m} (h : ContDiffOn ℝ ∞ f s)
    (i j : Fin m) : ContDiffOn ℝ ∞ (fun P => f P i j) s :=
  (contDiff_entry i j).comp_contDiffOn h

lemma contDiffOn_root :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => Real.sqrt (P 0 0).re) {P | P.PosDef} :=
  ContDiffOn.sqrt (Complex.reCLM.contDiff.comp (contDiff_entry 0 0)).contDiffOn
    fun _ hP => (lead_pos hP).ne'

lemma contDiffOn_invRoot :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => ((invRoot P : ℝ) : ℂ)) {P | P.PosDef} :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_root.inv fun _ hP => (Real.sqrt_pos.2 (lead_pos hP)).ne')

lemma contDiffOn_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => col P i) {P | P.PosDef} :=
  (contDiff_entry i.succ 0).contDiffOn.mul contDiffOn_invRoot

lemma contDiffOn_star_col (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Mat (n + 1) => star (col P i)) {P | P.PosDef} :=
  Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_col i)

lemma contDiffOn_schur : ContDiffOn ℝ ∞ (schur (n := n)) {P | P.PosDef} :=
  contDiffOn_mat fun i j =>
    (contDiff_entry i.succ j.succ).contDiffOn.sub ((contDiffOn_col i).mul (contDiffOn_star_col j))

lemma contDiffOn_step {σ : Mat n → Mat n} (hσ : ContDiffOn ℝ ∞ σ {P | P.PosDef}) :
    ContDiffOn ℝ ∞ (step σ) {P | P.PosDef} := by
  refine contDiffOn_mat fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_root
  · exact contDiffOn_const
  · exact contDiffOn_col i
  · exact contDiffOn_entry (hσ.comp contDiffOn_schur fun _ hP => schur_posDef hP) i j

theorem exists_smooth_section :
    ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧
      ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  intro n
  induction n with
  | zero => exact ⟨id, contDiffOn_id, fun P _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨σ, hσ, hf⟩ := ih
    exact ⟨step σ, contDiffOn_step hσ, fun P hP => step_mul hP (hf _ (schur_posDef hP))⟩

end GlobalTheory.CompanionTheory.ConeHaar.Chol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SmCalc

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {u : ℝ → E → W} {O : Set E}

theorem hasFDerivAt_unc (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((hu.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasDerivAt_line (s : ℝ) (y : E) :
    HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem deriv_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    deriv (fun r => u r y) s = fderiv ℝ (Function.uncurry u) (s, y) ((1 : ℝ), (0 : E)) := by
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s
    (hasFDerivAt_unc hO hu s hy) (hasDerivAt_line s y)
  exact h2.deriv

theorem fderiv_slice_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O)
    (v : E) : fderiv ℝ (u s) y v = fderiv ℝ (Function.uncurry u) (s, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 := HasFDerivAt.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) y
    (hasFDerivAt_unc hO hu s hy) h1
  have h3 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := h2
  simp [h3.fderiv]

theorem fd_smooth (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ O) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)

theorem smooth_deriv (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => deriv (fun r => u r y) s) (Set.univ ×ˢ O) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((1 : ℝ), (0 : E))) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply contDiffOn_const
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact deriv_eq hO hu s hy

theorem smooth_field (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => fderiv ℝ (u s) y (V y)) (Set.univ ×ˢ O) := by
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), V p.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((0 : ℝ), V p.2)) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply h0.contDiffOn
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact fderiv_slice_eq hO hu s hy _

theorem smooth_slice (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) :
    ContDiffOn ℝ ∞ (u s) O := by
  have h1 : ContDiff ℝ ∞ (fun z : E => (s, z)) := contDiff_const.prodMk contDiff_id
  exact ContDiffOn.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) hu
    h1.contDiffOn (fun z hz => ⟨Set.mem_univ _, hz⟩)

theorem smooth_line (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {y : E} (hy : y ∈ O) : ContDiff ℝ ∞ fun s => u s y := by
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => (r, y)) := contDiff_id.prodMk contDiff_const
  have h2 := ContDiffOn.comp (s := Set.univ) (g := Function.uncurry u)
    (f := fun r : ℝ => (r, y)) hu h1.contDiffOn (fun _ _ => ⟨Set.mem_univ _, hy⟩)
  exact contDiffOn_univ.1 h2

theorem deriv_fderiv_comm (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (v : E) (s : ℝ) {y : E}
    (hy : y ∈ O) :
    deriv (fun r => fderiv ℝ (u r) y v) s =
      fderiv ℝ (fun z => deriv (fun r => u r z) s) y v := by
  have hm : (s, y) ∈ (Set.univ : Set ℝ) ×ˢ O := ⟨Set.mem_univ _, hy⟩
  have hn := (isOpen_univ.prod hO).mem_nhds hm
  have hF : ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) := hu.contDiffAt hn
  have hG : HasFDerivAt (fderiv ℝ (Function.uncurry u))
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)) (s, y) :=
    (((fd_smooth hO hu).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ (Function.uncurry u) (s, y) :=
    hF.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hL : HasDerivAt (fun r => fderiv ℝ (u r) y v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), v)) s := by
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s hG (hasDerivAt_line s y)
    have h3 := ((ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)).hasFDerivAt).comp_hasDerivAt s h2
    have he : (fun r => fderiv ℝ (u r) y v) = (⇑(ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)) ∘
        (fderiv ℝ (Function.uncurry u)) ∘ fun r : ℝ => (r, y)) := by
      funext r
      simpa using fderiv_slice_eq hO hu r hy v
    rw [he]
    simpa using h3
  have hR : HasFDerivAt (fun z => deriv (fun r => u r z) s)
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        ((fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E))) y := by
    have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right s y
    have h2 := HasFDerivAt.comp (f := fun z : E => (s, z)) y hG h1
    have h3 := ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt).comp y h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz
    simpa using deriv_eq hO hu s hz
  rw [hL.deriv, hR.fderiv]
  simpa using hsym.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), v)

end Generic

theorem contDiff_mulRight {n : ℕ} (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

end SmCalc

theorem sm_calculus : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧
      (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧
      ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y :=
  fun _ hu => ⟨SmCalc.smooth_deriv isOpen_GLs hu,
    fun X => SmCalc.smooth_field isOpen_GLs hu (SmCalc.contDiff_mulRight X),
    SmCalc.smooth_slice hu, fun _ hy => SmCalc.smooth_line hu hy,
    fun _ s _ hy => SmCalc.deriv_fderiv_comm isOpen_GLs hu _ s hy⟩

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
end
end

