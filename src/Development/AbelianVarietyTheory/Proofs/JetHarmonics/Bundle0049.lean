import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensAdj

section
variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_left (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (y : ι → R.H) :
    hh Γ R (fun c => ∑ I, f I c) y = ∑ I, hh Γ R (f I) y := by
  simp only [hh, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (x : ι → R.H) :
    hh Γ R x (fun c => ∑ I, f I c) = ∑ I, hh Γ R x (f I) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem sum_sm (R : Rep k r) (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) : ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (t := univ) (f := x) fun c _ => hx c

omit [DecidableEq ι] in
theorem hh_tm (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) (v : R.H) :
    hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ := by
  simp only [hh, tm, ev, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem norm_sq_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Matrix ι ι ℂ}
    (h : Γᴴ * Γ = 1) (x : ι → H) : ∑ i, ‖∑ j, Γ i j • x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have key : ∑ i, ⟪∑ j, Γ i j • x j, ∑ j, Γ i j • x j⟫_ℂ = ∑ i, ⟪x i, x i⟫_ℂ := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ i, Γ i l * ((starRingEnd ℂ) (Γ i j) * ⟪x j, x l⟫_ℂ)
        = (if j = l then 1 else 0) * ⟪x j, x l⟫_ℂ := by
      intro j
      have := congrFun (congrFun h j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [conjTranspose_apply, RCLike.star_def]
      ring
    simp only [h2]
    simp
  simp only [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

theorem norm_hh_le {Γ : Matrix ι ι ℂ} (h : Γᴴ * Γ = 1) (R : Rep k r) (x : ι → R.H) :
    ‖hh Γ R x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  have e : hh Γ R x x = ∑ i, ⟪x i, ∑ j, Γ i j • x j⟫_ℂ := by
    simp only [hh, inner_sum, inner_smul_right]
  have h1 := norm_sq_mul h x
  have h2 : ‖hh Γ R x x‖ ≤ ∑ i, (‖x i‖ ^ 2 + ‖∑ j, Γ i j • x j‖ ^ 2) / 2 := by
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖x i‖ - ‖∑ j, Γ i j • x j‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1] at h2
  linarith

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
  {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} {ep : κ → ℝ}

theorem proj_sm (hT : TensH ρ Γ R RI io pr ep) (I : κ) {x : ι → R.H} (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, pr I c (x c) ∈ (RI I).sm :=
  sum_sm (RI I) _ fun c => (hT.raw.pr_sm I c).mem _ (hx c)

theorem adj (hT : TensH ρ Γ R RI io pr ep) (I : κ) (y : (RI I).H) (hy : y ∈ (RI I).sm) (x : ι → R.H)
    (hx : ∀ c, x c ∈ R.sm) :
    hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_right Γ R (fun J c => io J c (∑ d, pr J d (x d))), Finset.sum_eq_single I]
  · exact hT.iso I y hy _ (proj_sm hT I hx)
  · intro J _ hJ
    exact hT.orth I J hJ.symm y hy _ (proj_sm hT J hx)
  · simp

theorem parseval (hT : TensH ρ Γ R RI io pr ep) (x x' : ι → R.H) (hx : ∀ c, x c ∈ R.sm)
    (hx' : ∀ c, x' c ∈ R.sm) :
    hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_left Γ R (fun J c => io J c (∑ d, pr J d (x d)))]
  exact Finset.sum_congr rfl fun I _ => adj hT I _ (proj_sm hT I hx) x' hx'

end

theorem tens_adj : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI hR _ hF hT
  refine ⟨fun I y hy x hx => adj hT I y hy x hx, fun x x' hx hx' => parseval hT x x' hx hx',
    fun a x v => hh_tm Γ R a x v, ?_, ?_⟩
  · intro I y hy
    have h1 := norm_hh_le (Γ := Γ) (by rw [hF.1, hF.2.1]) R (fun c => io I c y)
    rw [hT.iso I y hy y hy, norm_mul, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖(ep I : ℂ)‖ = 1 := by rcases hT.ep_sq I with h | h <;> simp [h]
    rw [h2] at h1
    simpa using h1
  · intro a a' v hv v' hv' g hg
    have ht : ∀ (b : ι → ℂ) (w : R.H), w ∈ R.sm → ∀ c, tm R b w c ∈ R.sm := fun b w hw c =>
      R.smSub.smul_mem (b c) hw
    have hact : ∀ c, act ρ R g (tm R a' v') c ∈ R.sm := fun c =>
      sum_sm R _ fun j => R.smSub.smul_mem _
        (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 _ (ht a' v' hv' j) g hg)
    have hp := parseval hT _ _ hact (ht a v hv)
    simp only [hT.raw.pr_eq _ g hg _ (ht a' v' hv')] at hp
    rw [← hp]
    simp only [hh, act, tm, Formalism.QuantumDeterminants.herm, inner_sum, inner_smul_left, inner_smul_right, map_smul, smul_smul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply, RCLike.star_def]
    ring

end GlobalTheory.TensAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopMinorWedge

theorem det_mul_sub {n l : ℕ} (A : Matrix (Fin l) (Fin n) ℂ) (B : Matrix (Fin n) (Fin l) ℂ) :
    (A * B).det = ∑ I : BranchingSupport.Sub n l, (A.submatrix id (I.1.orderEmbOfFin I.2)).det *
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det := by
  rw [GlobalTheory.det_mul_eq_sum_minors]
  exact Fintype.sum_equiv
    (⟨fun S => ⟨S.1, S.2⟩, fun S => ⟨S.1, S.2⟩, fun _ => rfl, fun _ => rfl⟩ :
      Set.powersetCard (Fin n) l ≃ BranchingSupport.Sub n l) _ _ (fun _ => rfl)

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := det_mul_sub (g.submatrix (I.1.orderEmbOfFin I.2) id) (Matrix.of fun c b => f b c)
  have h2 : BranchingSupport.wedge (fun b => g *ᵥ f b) I =
      (g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun c b => f b c)).det := rfl
  rw [h2, h]
  rfl

theorem star_wedge_dot {n l : ℕ} (f f' : Fin l → Fin n → ℂ) :
    star (BranchingSupport.wedge f) ⬝ᵥ BranchingSupport.wedge f' = (Matrix.of fun a b => star (f a) ⬝ᵥ f' b).det := by
  have h := det_mul_sub (Matrix.of fun a c => star (f a c)) (Matrix.of fun c b => f' b c)
  have h2 : (Matrix.of fun a b => star (f a) ⬝ᵥ f' b) =
      (Matrix.of fun a c => star (f a c)) * (Matrix.of fun c b => f' b c) := rfl
  rw [h2, h]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [Pi.star_apply, BranchingSupport.wedge, ← Matrix.det_conjTranspose]
  rfl

theorem herm_cmp_wedge_eq_det : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (cmp (r + 1) g *ᵥ wedge (Formalism.QuantumDeterminants.fvec k r z'))
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (Formalism.QuantumDeterminants.Zhat k r z z' g).det := by
  intro k r z z' g
  rw [Formalism.QuantumDeterminants.herm, cmp_mulVec_wedge, cmp_mulVec_wedge, star_wedge_dot]
  rfl

end GlobalTheory.TopMinorWedge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace DualFRep

theorem gram_transpose (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᵀ = Formalism.QuantumDeterminants.Hpk k r := by
  have h := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [conjTranspose_apply] at h1
  rw [transpose_apply, ← h1]
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> simp

variable {n : ℕ}

theorem left_inv {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, h2]

theorem inv_eq {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H :=
  Matrix.inv_eq_left_inv (left_inv h2 hg)

theorem entry_le {k r : ℕ} (g : Mx k r) (a b : Fin (2 * r + k + 1)) : ‖g a b‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g a b) ≤ ∑ j, Complex.normSq (g a j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (g a j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end DualFRep

open DualFRep in

theorem isFRep_dualM (k r : ℕ) : IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  have h1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 := gram_transpose k r
  have hmem : ∀ g ∈ GG k r, gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := fun g hg => hg
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 h3 hmem ⊢
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dualM]
  · intro g hg h hh
    simp only [dualM]
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  · intro g hg
    have key : g⁻¹ * H * (g⁻¹)ᴴ = H := by
      rw [inv_eq h2 (hmem g hg)]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1]
      calc H * gᴴ * H * H * (H * (g * H)) = H * (gᴴ * (H * H) * H * g) * H := by
            simp only [Matrix.mul_assoc]
        _ = H := by rw [h2, Matrix.mul_one, hmem g hg, h2, Matrix.one_mul]
    have e : ((g⁻¹)ᵀ)ᴴ = ((g⁻¹)ᴴ)ᵀ := rfl
    have := congrArg Matrix.transpose key
    rw [transpose_mul, transpose_mul, h3] at this
    simp only [dualM]
    rw [e, Matrix.mul_assoc, this]
  · intro i j
    have hc : Continuous (fun g : Mx k r => (H * gᴴ * H) j i) := by
      have : Continuous (fun g : Mx k r => H * gᴴ * H) :=
        (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
      exact this.matrix_elem j i
    refine hc.continuousOn.congr ?_
    intro g hg
    simp only [dualM, transpose_apply]
    rw [inv_eq h2 (hmem g hg)]
  · refine ⟨∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖, ?_⟩
    intro g hg i j
    simp only [dualM, transpose_apply, pow_one]
    rw [inv_eq h2 (hmem g hg)]
    have hN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc ‖(H * gᴴ * H) j i‖ = ‖∑ b, ∑ a, H j a * star (g b a) * H b i‖ := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
      _ ≤ ∑ b, ∑ a, ‖H j a * star (g b a) * H b i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
      _ ≤ ∑ b, ∑ a, ‖H j a‖ * ‖H b i‖ * B.gN g := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul, norm_star, mul_right_comm]
          exact mul_le_mul_of_nonneg_left (entry_le g b a) (by positivity)
      _ = (∑ b, ∑ a, ‖H j a‖ * ‖H b i‖) * B.gN g := by simp only [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact Finset.single_le_sum
            (f := fun p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖)
            (fun p _ => by positivity) (Finset.mem_univ (i, j))
  · intro g hg hu
    have hl : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
    have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv hl
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [dualM]
    rw [hinv]
    have e : star ((star g)ᵀ) = gᵀ := by
      ext a b
      simp [Matrix.star_apply]
    rw [e, ← transpose_mul, (Matrix.mem_unitaryGroup_iff).1 hu, transpose_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarNotions

open Formalism.FourierDecayAlt.P.B2x1 in

theorem finite_compact_of_sigmaFinite {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [SigmaFinite μ] (hc : μ Uᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) (K : Set (Formalism.QuantumDeterminants.Mt k r)) (hK : IsCompact K) : μ K < ∞ := by
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have : SigmaFinite (pull hU μ) := by
    have h : SigmaFinite ((pull hU μ).map inc) := by rw [map_pull μ hc]; infer_instance
    exact SigmaFinite.of_map _ inc_memb.measurable.aemeasurable h
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Gp U hU)) := inferInstance
  have huniq := Measure.haarMeasure_unique (pull hU μ) K₀
  have hfin : pull hU μ K₀ ≠ ∞ := by
    intro hinf
    rw [hinf] at huniq
    have hzero : ∀ n, Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) = 0 := by
      intro n
      by_contra hne
      have h1 := measure_spanningSets_lt_top (pull hU μ) n
      have h2 : pull hU μ (spanningSets (pull hU μ) n) =
          ∞ * Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) :=
        congrArg (fun m : Measure (Gp U hU) => m (spanningSets (pull hU μ) n)) huniq
      rw [h2, ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have huniv : Measure.haarMeasure K₀ Set.univ = 0 := by
      rw [← iUnion_spanningSets (pull hU μ)]
      exact measure_iUnion_null hzero
    have h1 : Measure.haarMeasure K₀ K₀ = 0 := measure_mono_null (Set.subset_univ _) huniv
    rw [Measure.haarMeasure_self] at h1
    exact one_ne_zero h1
  have hK' : IsCompact ((inc : Gp U hU → Formalism.QuantumDeterminants.Mt k r) ⁻¹' K) := inc_closedEmb.isCompact_preimage hK
  have h3 : pull hU μ (inc ⁻¹' K) = pull hU μ K₀ * Measure.haarMeasure K₀ (inc ⁻¹' K) :=
    congrArg (fun m : Measure (Gp U hU) => m (inc ⁻¹' K)) huniq
  rw [← map_pull (hU := hU) μ hc, inc_memb.map_apply, h3]
  exact ENNReal.mul_lt_top hfin.lt_top hK'.measure_lt_top

theorem isHaarOn_iff {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (hex : ∃ ν : Measure (Formalism.QuantumDeterminants.Mt k r), B.IsHaarOn U ν) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ B.IsHaarOn U μ := by
  constructor
  · rintro ⟨hσ, h0, hc, hl⟩
    obtain ⟨ν, hν⟩ := hex
    have hfin := finite_compact_of_sigmaFinite hU μ hc hl
    obtain ⟨c, hcν⟩ := P.haar_measure_unique_up_to_scalar k r U ν μ hU hν hc hl hfin
    refine { ne_zero := h0, conc := hc, left := hl, right := ?_, finite_compact := hfin }
    intro a ha
    rw [hcν, Measure.map_smul, hν.right a ha]
  · intro h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem isHaarOn_iff_groups : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) :=
  fun k r μ =>
    ⟨isHaarOn_iff (P.unitary_group_closed k r) (P.unitary_group_haar_exists k r) μ,
      isHaarOn_iff (P.unipotent_radical_closed k r) (P.unipotent_haar_exists k r) μ,
      fun z hz hT _ => isHaarOn_iff (P.weyl_subgroup_closed k r z) (P.weyl_haar_exists k r z hz hT) μ⟩

end GlobalTheory.HaarNotions
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsIsoGmOfMap
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOneInt

theorem mulN_eq_nMul {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    JetMomFound.mulN F n = nMul F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [JetMomFound.mulN, nMul_succ, ih]

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem isIsoGm_of_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (F : FormalGroup R) (f : PowerSeries R)
    (h0 : PowerSeries.constantCoeff f = 0) (h1 : IsUnit (PowerSeries.coeff 1 f))
    (h : (f.map φ).subst (F.map φ).toPowerSeries =
      (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) *
          (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S)) :
    JetMomFound.IsIsoGm F f := by
  refine ⟨h0, h1, ?_⟩
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f h0
  have hs : MvPowerSeries.HasSubst
      ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro s; fin_cases s <;> simp [hc])
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2) φ) := by
    intro a b hab
    ext ν
    apply hφ
    rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hab]
  apply hinj
  rw [map_add, map_add, map_mul, PowerSeries.map_subst hF, PowerSeries.map_subst (hX 0),
    PowerSeries.map_subst (hX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]
  exact h

theorem htOneIsGm : JetMomFound.HtOneIsGm := by
  intro p _ F _ hH
  let φ : 𝓞_ℂ_[p] →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hI : Intg (F.map φ).toPowerSeries := by
    intro ν
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
    exact (mem_int_iff _).1 (MvPowerSeries.coeff ν F.toPowerSeries).2
  have hn : ∀ k, PowerSeries.coeff k (nMul (F.map φ) p) =
      ((PowerSeries.coeff k (JetMomFound.mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    intro k
    rw [← (nMul_props _ F).2.2.2.2 _ φ p, PowerSeries.coeff_map, mulN_eq_nMul]
    rfl
  obtain ⟨f, hfI, hf0, hf1, hf⟩ := HeightOne.exists_iso_multiplicative ℂ_[p] p (F.map φ) hI
    (by rw [hn]; exact hH.1) (fun k hk => by rw [hn]; exact hH.2 k hk)
  let f₀ : PowerSeries 𝓞_ℂ_[p] := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n f, (mem_int_iff _).2 (hfI (Finsupp.single () n))⟩
  have hc : ∀ n, φ (PowerSeries.coeff n f₀) = PowerSeries.coeff n f := by
    intro n
    simp only [f₀, PowerSeries.coeff_mk]
    rfl
  have hm : f₀.map φ = f := by
    ext n
    rw [PowerSeries.coeff_map, hc]
  refine ⟨f₀, isIsoGm_of_map φ hφ F f₀ ?_ ?_ (by rw [hm]; exact hf)⟩
  · apply hφ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  · have hne : PowerSeries.coeff 1 f ≠ 0 := by
      intro h
      rw [h, norm_zero] at hf1
      exact zero_ne_one hf1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, (mem_int_iff _).2 ?_⟩ ?_
    · rw [norm_inv, hf1, inv_one]
    · apply hφ
      rw [map_mul, hc, map_one]
      exact mul_inv_cancel₀ hne

end GlobalTheory.ConvSer.HeightOneInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLe
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem norm_sq_integral_inner_smul_le (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ)
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hp : AEStronglyMeasurable ph ν) :
    ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤
      (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF
  set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG
  have hFm : AEMeasurable F ν := hp.enorm.mul hf.enorm
  have hGm : AEMeasurable G ν := hg.enorm
  have h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    have h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖ := by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_smul]; ring
    have := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm,
      ofReal_norm_eq_enorm] at this
    exact this
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm
  have e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ENNReal.rpow_two]
  have e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm, ENNReal.rpow_two]
  rw [e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm]
  refine (pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)
  have k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, k, k]

end GlobalTheory
end

