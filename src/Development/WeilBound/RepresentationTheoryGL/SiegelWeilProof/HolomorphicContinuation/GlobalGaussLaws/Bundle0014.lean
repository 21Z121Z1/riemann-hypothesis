import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInC
section
noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

theorem diag_eq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (Mᴴ * A * M) j j = star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

theorem tr_re_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (trace (Mᴴ * A * M)).re ∧ (M ≠ 0 → 0 < (trace (Mᴴ * A * M)).re) := by
  have hsum : (trace (Mᴴ * A * M)).re = ∑ j, (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, diag_eq]
  have hnn : ∀ j, 0 ≤ (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    intro j
    by_cases hv : (fun a => M a j) = 0
    · rw [hv]
      simp
    · exact (hA.re_dotProduct_pos hv).le
  refine ⟨hsum ▸ Finset.sum_nonneg (fun j _ => hnn j), fun hM => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (fun a => M a j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hM
    ext a j
    exact congrFun (hc j) a
  rw [hsum]
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j, Finset.mem_univ _, hA.re_dotProduct_pos hj⟩

theorem tr_re_symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M N : Matrix (Fin m) (Fin n) ℂ) :
    (trace (Mᴴ * A * N)).re = (trace (Nᴴ * A * M)).re := by
  have h : (Mᴴ * A * N)ᴴ = Nᴴ * A * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  rw [← h, Matrix.trace_conjTranspose]
  simp

theorem tr_im_zero {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M : Matrix (Fin m) (Fin n) ℂ) :
    trace (Mᴴ * A * M) = ((trace (Mᴴ * A * M)).re : ℂ) := by
  have h : star (trace (Mᴴ * A * M)) = trace (Mᴴ * A * M) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have him : (trace (Mᴴ * A * M)).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext <;> simp [him]

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

def qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) : ℝ :=
  ∑ t : {τ' : T // τ' ≠ τ}, w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b' t))).re

def Qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) : LinearMap.BilinForm ℝ (Bsp τ m n) :=
  LinearMap.mk₂ ℝ (fun b b' => 2 * qf τ A w b b')
    (fun b₁ b₂ b' => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.conjTranspose_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (of ((r • b) t))ᴴ = (r : ℂ) • (of (b t))ᴴ := by
        rw [show of ((r • b) t) = (r : ℂ) • of (b t) from by ext i j; simp [Complex.real_smul]]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)
    (fun b b₁ b₂ => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : of ((r • b') t) = (r : ℂ) • of (b' t) := by ext i j; simp [Complex.real_smul]
      rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)

theorem Qf_apply (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) :
    Qf τ A w b b' = 2 * qf τ A w b b' := rfl

theorem Qf_symm (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).IsHermitian) (w : T → ℝ)
    (b b' : Bsp τ m n) : Qf τ A w b b' = Qf τ A w b' b := by
  rw [Qf_apply, Qf_apply]
  congr 1
  unfold qf
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tr_re_symm (hA t.1 t.2)]

theorem Qf_pos (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) (b : Bsp τ m n) (hb : b ≠ 0) : 0 < Qf τ A w b b := by
  rw [Qf_apply]
  have hnn : ∀ t : {τ' : T // τ' ≠ τ}, 0 ≤ w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b t))).re :=
    fun t => mul_nonneg (hw t.1 t.2).le (tr_re_nonneg (hA t.1 t.2) _).1
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (funext hc)
  have hof : of (b t) ≠ 0 := by
    intro h0
    apply ht
    funext i j
    exact congrFun (congrFun h0 i) j
  have hpos : 0 < qf τ A w b b :=
    Finset.sum_pos' (fun t _ => hnn t)
      ⟨t, Finset.mem_univ _, mul_pos (hw t.1 t.2) ((tr_re_nonneg (hA t.1 t.2) _).2 hof)⟩
  linarith

theorem exists_gauss (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) :
    ∃ G : 𝓢(Bsp τ m n, ℂ), ∀ b, G b = Complex.exp (-(Real.pi : ℂ) * ((2 * qf τ A w b b : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := GlobalTheory.ThK.EvAt0.GaussForm.exists_schwartz_gauss_form (Qf τ A w)
    (Qf_symm τ A (fun t ht => (hA t ht).isHermitian) w) (fun b hb => Qf_pos τ A hA w hw b hb)
  refine ⟨G, fun b => ?_⟩
  rw [(hG b).1, Qf_apply]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBound
section
noncomputable section

open Matrix Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def famPQ {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ)
    (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e p q y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

namespace DBoundH

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def EntD (S : Set ℂ) (f : ℂ → Matrix ι ι ℂ) : Prop := ∀ i j, DifferentiableOn ℂ (fun z => f z i j) S

theorem entD_const (S : Set ℂ) (A : Matrix ι ι ℂ) : EntD S (fun _ => A) := fun _ _ => differentiableOn_const _

theorem entD_add {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).fun_add (hg i j)

theorem entD_mul {S : Set ℂ} {f g : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (hg : EntD S g) :
    EntD S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hf i k).mul (hg k j)

theorem det_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableOn_const _).mul (DifferentiableOn.fun_finsetProd fun i _ => hf _ _)

theorem entD_adjugate {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    EntD S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_diff (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact differentiableOn_const _
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entD_inv {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntD S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_diff hf).inv h0).mul (entD_adjugate hf i j)

theorem trace_diff {S : Set ℂ} {f : ℂ → Matrix ι ι ℂ} (hf : EntD S f) :
    DifferentiableOn ℂ (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact DifferentiableOn.fun_sum fun i _ => hf i i

theorem entD_aC (X : Fin n → ℝ) (S : Set ℂ) : EntD S (aC X) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (X i : ℂ)))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · simpa [aC] using differentiableOn_const (c := (0 : ℂ))
  · by_cases h : i = j
    · subst h
      simpa [aC] using (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-(z * (X i : ℂ))))).differentiableOn
    · simpa [aC, h] using differentiableOn_const (c := (0 : ℂ))

theorem entD_toBlocks₁₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₁) :=
  fun i j => hf (Sum.inl i) (Sum.inl j)

theorem entD_toBlocks₁₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₁₂) :=
  fun i j => hf (Sum.inl i) (Sum.inr j)

theorem entD_toBlocks₂₁ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₁) :=
  fun i j => hf (Sum.inr i) (Sum.inl j)

theorem entD_toBlocks₂₂ {S : Set ℂ} {f : ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    (hf : EntD S f) : EntD S (fun z => (f z).toBlocks₂₂) :=
  fun i j => hf (Sum.inr i) (Sum.inr j)

theorem bigM_diff (y : GR n) (X : Fin n → ℝ) (S : Set ℂ) : EntD S (fun z => mR y * aC X z) :=
  entD_mul (entD_const _ _) (entD_aC X S)

theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [Matrix.det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => by rw [← Complex.exp_add]; simp

theorem det_bigM_ne (y : GR n) (X : Fin n → ℝ) (z : ℂ) : (mR y * aC X z).det ≠ 0 := by
  rw [det_mul, det_aC, mul_one]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.1.isUnit).ne_zero

end DBoundH

namespace DBoundH

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem famPQ_holo {m n : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (y : GR n)
    (u : Fin m → Fin n → ℂ) : DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X) := by
  set S := stripS X
  have hM := bigM_diff y X S
  have hQ : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₂₁ hM) (entD_const _ _)) (entD_toBlocks₂₂ hM)
  have hP : ∀ s : ℂ, EntD S (fun z => (mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) :=
    fun s => entD_add (entD_mul (entD_toBlocks₁₁ hM) (entD_const _ _)) (entD_toBlocks₁₂ hM)
  have hd1 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.1
  have hd2 : ∀ z ∈ S, ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 :=
    fun z hz => (dSieg n y X z hz).2.2.2
  have hZ1 : EntD S (fun z => ptZ y X z Complex.I) := entD_mul (hP _) (entD_inv (hQ _) hd1)
  have hZ2 : EntD S (fun z => ptZ y X z (-Complex.I)) := entD_mul (hP _) (entD_inv (hQ _) hd2)
  have hj : DifferentiableOn ℂ (fun z => jC e p q y X z) S := by
    unfold jC
    refine (((det_diff hM).zpow (Or.inl fun z _ => det_bigM_ne y X z)).mul
      ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd1 z hz))).mul ((det_diff (hQ _)).zpow (Or.inl fun z hz => hd2 z hz))
  have hg : DifferentiableOn ℂ (fun z => gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u) S := by
    unfold gC
    refine DifferentiableOn.cexp ?_
    exact ((trace_diff (entD_mul hZ1 (entD_const _ _))).const_mul _).sub
      ((trace_diff (entD_mul hZ2 (entD_const _ _))).const_mul _)
  exact hj.mul hg

variable {n : ℕ} {T : Type} [TopologicalSpace T]

def EntC (S : Set T) (f : T → Matrix ι ι ℂ) : Prop := ∀ i j, ContinuousOn (fun x => f x i j) S

omit [Fintype ι] [DecidableEq ι] in
theorem entC_const (S : Set T) (A : Matrix ι ι ℂ) : EntC S (fun _ => A) := fun _ _ => continuousOn_const

omit [Fintype ι] [DecidableEq ι] in
theorem entC_add {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z + g z) := fun i j => by
  simp only [Matrix.add_apply]
  exact (hf i j).add (hg i j)

omit [DecidableEq ι] in
theorem entC_mul {S : Set T} {f g : T → Matrix ι ι ℂ} (hf : EntC S f) (hg : EntC S g) :
    EntC S (fun z => f z * g z) := fun i j => by
  simp only [Matrix.mul_apply]
  exact continuousOn_finset_sum _ fun k _ => (hf i k).mul (hg k j)

theorem det_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).det) S := by
  simp only [Matrix.det_apply]
  refine continuousOn_finset_sum _ fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact continuousOn_const.mul (continuousOn_finset_prod _ fun i _ => hf _ _)

theorem entC_adjugate {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    EntC S (fun z => (f z).adjugate) := fun i j => by
  simp only [Matrix.adjugate_apply]
  refine det_cont (f := fun z => (f z).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact continuousOn_const
  · simp only [Matrix.updateRow_ne hab]; exact hf a b

theorem entC_inv {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) (h0 : ∀ z ∈ S, (f z).det ≠ 0) :
    EntC S (fun z => (f z)⁻¹) := fun i j => by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((det_cont hf).inv₀ h0).mul (entC_adjugate hf i j)

omit [DecidableEq ι] in
theorem trace_cont {S : Set T} {f : T → Matrix ι ι ℂ} (hf : EntC S f) :
    ContinuousOn (fun z => (f z).trace) S := by
  simp only [Matrix.trace, Matrix.diag]
  exact continuousOn_finset_sum _ fun i _ => hf i i

theorem mR_cont : Continuous fun y : GR n => mR y :=
  Units.continuous_val.comp continuous_subtype_val

theorem gramB_cont {m : ℕ} (ε : Fin m → Bool) (b : Bool) (i j : Fin n) :
    Continuous fun u : Fin m → Fin n → ℂ => gramB ε b u i j := by
  unfold gramB evX
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun k => by
    split_ifs
    · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · exact (continuous_apply _).comp (continuous_apply _))

theorem famPQ_cont {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) :
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) := by
  set S : Set (GR n × ℂ × (Fin m → Fin n → ℂ)) := Set.univ ×ˢ (stripS X ×ˢ Set.univ) with hS
  have hzS : ∀ p' ∈ S, p'.2.1 ∈ stripS X := fun p' hp => hp.2.1
  have hY : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1) := fun i j =>
    (((continuous_apply j).comp ((continuous_apply i).comp mR_cont)).comp continuous_fst).continuousOn
  have hA : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => aC X p'.2.1) := by
    intro i j
    have := (entD_aC X Set.univ i j).continuousOn
    exact (this.comp_continuous (continuous_fst.comp continuous_snd) (fun _ => Set.mem_univ _)).continuousOn
  have hM : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => mR p'.1 * aC X p'.2.1) := entC_mul hY hA
  have hM' : ∀ i j, ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1) i j) S := hM
  have projected_block_lower_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₁) :=
    fun i j => hM' (Sum.inr i) (Sum.inl j)
  have lowerDiagonalBlockAsGL : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun i j => hM' (Sum.inr i) (Sum.inr j)
  have upper_block_rank_one_update : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₁) :=
    fun i j => hM' (Sum.inl i) (Sum.inl j)
  have projected_block_upper_sum : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun i j => hM' (Sum.inl i) (Sum.inr j)
  have hQ : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂) :=
    fun s => entC_add (entC_mul projected_block_lower_sum (entC_const _ _)) lowerDiagonalBlockAsGL
  have hP : ∀ s : ℂ, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      (mR p'.1 * aC X p'.2.1).toBlocks₁₁ * (s • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₁₂) :=
    fun s => entC_add (entC_mul upper_block_rank_one_update (entC_const _ _)) projected_block_upper_sum
  have hd1 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * (Complex.I • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.1
  have hd2 : ∀ p' ∈ S, ((mR p'.1 * aC X p'.2.1).toBlocks₂₁ * ((-Complex.I) • 1) + (mR p'.1 * aC X p'.2.1).toBlocks₂₂).det ≠ 0 :=
    fun p' hp => (dSieg n p'.1 X p'.2.1 (hzS p' hp)).2.2.2
  have hZ1 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 Complex.I) :=
    entC_mul (hP _) (entC_inv (hQ _) hd1)
  have hZ2 : EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => ptZ p'.1 X p'.2.1 (-Complex.I)) :=
    entC_mul (hP _) (entC_inv (hQ _) hd2)
  have hG : ∀ b : Bool, EntC S (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => gramB (epsT t ε) b p'.2.2) := fun b i j =>
    ((gramB_cont (epsT t ε) b i j).comp (continuous_snd.comp continuous_snd)).continuousOn
  have hj : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => jC e p q p'.1 X p'.2.1) S := by
    unfold jC
    exact (((det_cont hM).zpow₀ _ fun p' _ => Or.inl (det_bigM_ne p'.1 X p'.2.1)).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd1 p' hp))).mul
      ((det_cont (hQ _)).zpow₀ _ fun p' hp => Or.inl (hd2 p' hp))
  have hg : ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) =>
      gC ε t c (ptZ p'.1 X p'.2.1 Complex.I) (ptZ p'.1 X p'.2.1 (-Complex.I)) p'.2.2) S := by
    unfold gC
    refine ContinuousOn.cexp ?_
    exact (continuousOn_const.mul (trace_cont (entC_mul hZ1 (hG true)))).sub
      (continuousOn_const.mul (trace_cont (entC_mul hZ2 (hG false))))
  exact hj.mul hg

end DBoundH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB

variable {n : ℕ}

def dR (β : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (β j : ℂ)

theorem dR_conjTranspose (β : Fin n → ℝ) : (dR β)ᴴ = dR β := by
  simp [dR, Matrix.diagonal_conjTranspose]

theorem dR_mul (β β' : Fin n → ℝ) : dR β * dR β' = dR (fun j => β j * β' j) := by
  simp [dR, Matrix.diagonal_mul_diagonal]

theorem dR_add (β β' : Fin n → ℝ) : dR β + dR β' = dR (fun j => β j + β' j) := by
  simp [dR, Matrix.diagonal_add]

theorem dR_neg (β : Fin n → ℝ) : -dR β = dR (fun j => -β j) := by
  simp [dR, Matrix.diagonal_neg]

theorem dR_one : dR (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [dR]

theorem dR_inv (β : Fin n → ℝ) (hβ : ∀ j, β j ≠ 0) : (dR β)⁻¹ = dR (fun j => (β j)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [dR_mul]
  rw [← dR_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (hβ j)

theorem kth_eq (θ : Fin n → ℝ) : kth θ = fromBlocks (dR fun j => Real.cos (θ j)) (dR fun j => Real.sin (θ j))
    (-dR fun j => Real.sin (θ j)) (dR fun j => Real.cos (θ j)) := rfl

theorem kth_decomp (θ : Fin n → ℝ) (hc : ∀ j, Real.cos (θ j) ≠ 0) :
    kth θ = nU (dR fun j => Real.tan (θ j)) * nbar (dR fun j => -(Real.sin (θ j) * Real.cos (θ j))) *
      mM (dR fun j => (Real.cos (θ j))⁻¹) := by
  have hinv : ((dR fun j => (Real.cos (θ j))⁻¹)ᴴ)⁻¹ = dR fun j => Real.cos (θ j) := by
    rw [dR_conjTranspose, dR_inv _ (fun j => inv_ne_zero (hc j))]
    simp only [inv_inv]
  rw [kth_eq]
  simp only [nU, nbar, mM, hinv, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, dR_mul]
  rw [dR_add, dR_neg]
  congr 1
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq (θ j))
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  · congr 1
    funext j
    have h1 := hc j
    field_simp

theorem kth_half (θ : Fin n → ℝ) : kth θ = kth (fun j => θ j / 2) * kth (fun j => θ j / 2) := by
  have hc : ∀ j, Real.cos (θ j) = Real.cos (θ j / 2) * Real.cos (θ j / 2) -
      Real.sin (θ j / 2) * Real.sin (θ j / 2) := by
    intro j
    have := Real.cos_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    linear_combination Real.sin_sq_add_cos_sq (θ j / 2)
  have hs : ∀ j, Real.sin (θ j) = Real.cos (θ j / 2) * Real.sin (θ j / 2) +
      Real.sin (θ j / 2) * Real.cos (θ j / 2) := by
    intro j
    have := Real.sin_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    ring
  rw [kth_eq, kth_eq, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg, Matrix.neg_mul, dR_mul, dR_neg, dR_add]
  congr 1
  · congr 1
    funext j
    rw [hc j]
    ring
  · congr 1
    funext j
    rw [hs j]
  · congr 1
    funext j
    rw [hs j]
    ring
  · congr 1
    funext j
    rw [hc j]
    ring

end PositivityTheory.Rg.Sw.Glob.VacD
end
end

