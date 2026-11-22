import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0009
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0004

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.ApplyWordMemDualGen
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def elemMat (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (t : R) : Matrix (Fin r) (Fin r) R :=
  fun c d => (if c = d then 1 else 0) + (if c = b ∧ d = a then t else 0)

theorem eval_rowGen_gen (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (t : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.eval (C t) (rowGen R a b f) = rowAct R (elemMat R a b t) f := by
  have : (Polynomial.evalRingHom (C t)).comp (rowGen R (n := n) a b).toRingHom =
      (rowAct R (n := n) (elemMat R a b t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowGen, rowAct,
        aeval_X, Polynomial.coe_evalRingHom, elemMat, map_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · simp
      · by_cases hb : v.1 = b
        · simp only [hb, true_and, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
          rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
        · simp [hb]
  exact congrArg (fun φ => φ f) this

theorem eval_C_gen (R : Type) [CommRing R] {σ : Type} (P : Polynomial (MvPolynomial σ R)) (N : ℕ)
    (hN : P.natDegree < N) (t : R) :
    Polynomial.eval (C t) P = ∑ i ∈ Finset.range N, C (t ^ i) * P.coeff i := by
  rw [Polynomial.eval_eq_sum_range' hN]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mul_comm]

theorem extM_elemMat (R : Type) [CommRing R] {n : ℕ} (a b : Fin n) (t : R) :
    Formalism.BranchingDeterminantCap.extM R (elemMat R a b t) = elemMat R a.castSucc b.castSucc t := by
  ext c d
  unfold Formalism.BranchingDeterminantCap.extM elemMat
  simp only [Matrix.of_apply]
  by_cases h : c.val < n ∧ d.val < n
  · rw [dif_pos h]
    congr 1
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  · rw [dif_neg h]
    have : ¬ (c = b.castSucc ∧ d = a.castSucc) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨b.isLt, a.isLt⟩
    rw [if_neg this, add_zero]

def RowNat (R : Type) [CommRing R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ (g : Matrix (Fin n) (Fin n) R) (f f' : ↥(dualWeyl R n n σ)),
    (f' : MvPolynomial (Fin n × Fin n) R) = rowAct R g (f : MvPolynomial (Fin n × Fin n) R) →
      io f' = rowAct R (Formalism.BranchingDeterminantCap.extM R g) (io f)

theorem io_rowDiv_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (a b : Fin n) (k : ℕ) (f : ↥(dualWeyl R n n σ))
    (hk : rowDiv R a b k (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ) :
    io ⟨_, hk⟩ = rowDiv R a.castSucc b.castSucc k (io f) := by
  have hmem : ∀ i, rowDiv R a b i (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ :=
    fun i => Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable R n n σ a b i _ f.2
  set N := (rowGen R a b (f : MvPolynomial (Fin n × Fin n) R)).natDegree +
    (rowGen R a.castSucc b.castSucc (io f)).natDegree + k + 1 with hN
  have h1 : (rowGen R a b (f : MvPolynomial (Fin n × Fin n) R)).natDegree < N := by omega
  have h2 : (rowGen R a.castSucc b.castSucc (io f)).natDegree < N := by omega
  have hk' : k ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have key : ∀ t : R, ∑ i ∈ Finset.range N, t ^ i • io ⟨_, hmem i⟩ =
      ∑ i ∈ Finset.range N, t ^ i • rowDiv R a.castSucc b.castSucc i (io f) := by
    intro t
    have hrow : rowAct R (elemMat R a b t) (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ :=
      Formalism.GradedWeylDivisibility.dualWeylRowStable R n n σ _ _ f.2
    have e := hio2 (elemMat R a b t) f ⟨_, hrow⟩ rfl
    have e2 : rowAct R (elemMat R a.castSucc b.castSucc t) (io f) =
        ∑ i ∈ Finset.range N, C (t ^ i) * (rowGen R a.castSucc b.castSucc (io f)).coeff i := by
      rw [← eval_rowGen_gen, eval_C_gen R _ N h2]
    rw [extM_elemMat, e2] at e
    have hsub : (⟨_, hrow⟩ : ↥(dualWeyl R n n σ)) = ∑ i ∈ Finset.range N, t ^ i • ⟨_, hmem i⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← eval_rowGen_gen, eval_C_gen R _ N h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul]
      rfl
    rw [hsub, map_sum] at e
    simp only [map_smul] at e
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul]
    rfl
  ext m
  set P : Polynomial R := ∑ i ∈ Finset.range N, Polynomial.monomial i (coeff m (io ⟨_, hmem i⟩)) with hP
  set Q : Polynomial R := ∑ i ∈ Finset.range N,
    Polynomial.monomial i (coeff m (rowDiv R a.castSucc b.castSucc i (io f))) with hQ
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro t
    simp only [hP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    have := congrArg (coeff m) (key t)
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at this
    simpa [mul_comm] using this
  have := congrArg (fun p => Polynomial.coeff p k) hPQ
  simp only [hP, hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hk'] at this
  exact this

theorem applyWord_mem_dual_gen (R : Type) [CommRing R] {n : ℕ} (σ : Fin n → ℕ) (w : List (Fin n × Fin n × ℕ))
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n σ) : applyWord R w f ∈ dualWeyl R n n σ := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable R n n σ _ _ _ _ ih

theorem io_applyWord_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (w : List (Fin n × Fin n × ℕ)) (f : ↥(dualWeyl R n n σ))
    (hw : applyWord R w (f : MvPolynomial (Fin n × Fin n) R) ∈ dualWeyl R n n σ) :
    io ⟨_, hw⟩ = applyWord R (liftWord w) (io f) := by
  revert hw
  induction w with
  | nil => intro hw; rfl
  | cons x w ih =>
    intro hw
    have hw' := applyWord_mem_dual_gen R σ w _ f.2
    change io ⟨rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f : MvPolynomial (Fin n × Fin n) R)), hw⟩ =
      rowDiv R x.1.castSucc x.2.1.castSucc x.2.2 (applyWord R (liftWord w) (io f))
    rw [io_rowDiv_gen R σ io hio2 x.1 x.2.1 x.2.2 ⟨_, hw'⟩ hw, ih hw']

theorem applyWord_smul_gen (R : Type) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) : applyWord R w (c • f) = c • applyWord R w f := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (c • f)) = c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f)
    rw [ih, Formalism.GradedWeylDivisibility.rowDiv_smul]

def HwVal (R : Type) [CommRing R] {n : ℕ} (lam σ : Fin n → ℕ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) : Prop :=
  ∀ h : ↥(dualWeyl R n n σ), (h : MvPolynomial (Fin n × Fin n) R) = hw R le_rfl σ →
    io h = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (σ i : ℤ)) : ℤ) : R) • Formalism.BranchingDeterminantCap.xiB R lam σ

theorem io_weyl_gen (R : Type) [CommRing R] [IsDomain R] [Infinite R] {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (io : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hio2 : RowNat R σ io)
    (hio3 : HwVal R lam σ io)
    (w : List (Fin n × Fin n × ℕ)) (hwd : applyWord R w (hw R le_rfl σ) ∈ dualWeyl R n n σ) :
    io ⟨_, hwd⟩ = ((Formalism.BranchingDeterminantCap.cCap (Formalism.BranchingDeterminantCap.lamZ lam) (fun i => (σ i : ℤ)) : ℤ) : R) •
      applyWord R (liftWord w) (Formalism.BranchingDeterminantCap.xiB R lam σ) := by
  have hhw : hw R le_rfl σ ∈ dualWeyl R n n σ :=
    Formalism.GradedWeylDivisibility.weylLeDual R n n le_rfl _ hσ (Submodule.subset_span ⟨[], rfl⟩)
  rw [io_applyWord_gen R σ io hio2 w ⟨_, hhw⟩ hwd, hio3 ⟨_, hhw⟩ rfl, applyWord_smul_gen]

theorem map_initMinor_gen {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

theorem map_xiB {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam σ : Fin n → ℕ) :
    map φ (Formalism.BranchingDeterminantCap.xiB R lam σ) = Formalism.BranchingDeterminantCap.xiB S lam σ := by
  unfold Formalism.BranchingDeterminantCap.xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, map_initMinor_gen, map_initMinor_gen]

theorem map_smul_gen {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ : Type} (c : R) (f : MvPolynomial κ R) :
    map φ (c • f) = φ c • map φ f := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

theorem io_bc_weyl {R S : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing S] [IsDomain S] [Infinite S]
    (φ : R →+* S) {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (ioR : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hR2 : RowNat R σ ioR)
    (hR3 : HwVal R lam σ ioR)
    (ioS : ↥(dualWeyl S n n σ) →ₗ[S] MvPolynomial (Fin (n + 1) × Fin n) S) (hS2 : RowNat S σ ioS)
    (hS3 : HwVal S lam σ ioS)
    (y : MvPolynomial (Fin n × Fin n) R) (hy : y ∈ weyl R n n le_rfl σ) :
    ∀ (h1 : y ∈ dualWeyl R n n σ) (h2 : map φ y ∈ dualWeyl S n n σ), ioS ⟨_, h2⟩ = map φ (ioR ⟨y, h1⟩) := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual R n n le_rfl σ hσ
  have hmp : ∀ x, x ∈ dualWeyl R n n σ → map φ x ∈ dualWeyl S n n σ :=
    fun x hx => Formalism.GradedWeylDivisibility.dualWeylMap R S φ n n σ x hx
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    intro h1 h2
    have h2' : applyWord S w (hw S le_rfl σ) ∈ dualWeyl S n n σ := by
      rw [← lclosedeq_hw_map φ, lclosedeq_applyWord_map]
      exact h2
    have e : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = ⟨_, h2'⟩ := by
      apply Subtype.ext
      show map φ (applyWord R w (hw R le_rfl σ)) = applyWord S w (hw S le_rfl σ)
      rw [← lclosedeq_hw_map φ, lclosedeq_applyWord_map]
    rw [e, io_weyl_gen S lam σ hσ ioS hS2 hS3 w h2']
    have e1 := io_weyl_gen R lam σ hσ ioR hR2 hR3 w h1
    rw [e1, map_smul_gen, ← lclosedeq_applyWord_map, map_xiB, map_intCast]
  | zero =>
    intro h1 h2
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = 0 := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = 0 := Subtype.ext (map_zero _)
    rw [e1, e2, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    intro h1 h2
    have hx1 := hle hx
    have hy1 := hle hy
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = ⟨x, hx1⟩ + ⟨y, hy1⟩ := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = ⟨_, hmp x hx1⟩ + ⟨_, hmp y hy1⟩ := Subtype.ext (map_add _ _ _)
    rw [e1, e2, map_add, map_add, map_add, ihx hx1 (hmp x hx1), ihy hy1 (hmp y hy1)]
  | smul c x hx ihx =>
    intro h1 h2
    have hx1 := hle hx
    have e1 : (⟨_, h1⟩ : ↥(dualWeyl R n n σ)) = c • ⟨x, hx1⟩ := rfl
    have e2 : (⟨_, h2⟩ : ↥(dualWeyl S n n σ)) = φ c • ⟨_, hmp x hx1⟩ := Subtype.ext (map_smul_gen φ c x)
    rw [e1, e2, map_smul, map_smul, map_smul_gen, ihx hx1 (hmp x hx1)]

theorem io_bc {R S : Type} [CommRing R] [IsDomain R] [Infinite R] [CommRing S] [IsDomain S] [Infinite S]
    (φ : R →+* S) (hφ : Function.Injective φ) {n : ℕ} (lam σ : Fin n → ℕ) (hσ : Antitone σ)
    (ioR : ↥(dualWeyl R n n σ) →ₗ[R] MvPolynomial (Fin (n + 1) × Fin n) R) (hR2 : RowNat R σ ioR)
    (hR3 : HwVal R lam σ ioR)
    (ioS : ↥(dualWeyl S n n σ) →ₗ[S] MvPolynomial (Fin (n + 1) × Fin n) S) (hS2 : RowNat S σ ioS)
    (hS3 : HwVal S lam σ ioS)
    (q : MvPolynomial (Fin n × Fin n) R) (N : R) (hN : N ≠ 0) (hq : N • q ∈ weyl R n n le_rfl σ)
    (h1 : q ∈ dualWeyl R n n σ) (h2 : map φ q ∈ dualWeyl S n n σ) : ioS ⟨_, h2⟩ = map φ (ioR ⟨q, h1⟩) := by
  have h1' : N • q ∈ dualWeyl R n n σ := Submodule.smul_mem _ _ h1
  have h2' : map φ (N • q) ∈ dualWeyl S n n σ := Formalism.GradedWeylDivisibility.dualWeylMap R S φ n n σ _ h1'
  have key := io_bc_weyl φ lam σ hσ ioR hR2 hR3 ioS hS2 hS3 (N • q) hq h1' h2'
  have e1 : (⟨_, h1'⟩ : ↥(dualWeyl R n n σ)) = N • ⟨q, h1⟩ := rfl
  have e2 : (⟨_, h2'⟩ : ↥(dualWeyl S n n σ)) = φ N • ⟨_, h2⟩ := Subtype.ext (map_smul_gen φ N q)
  rw [e1, e2, map_smul, map_smul, map_smul_gen, smul_eq_C_mul, smul_eq_C_mul] at key
  have hC : (C (φ N) : MvPolynomial (Fin (n + 1) × Fin n) S) ≠ 0 := by
    rw [Ne, C_eq_zero]
    exact fun h => hN (hφ (by rw [h, map_zero]))
  exact mul_left_cancel₀ hC key

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.CTEqConjTranspose
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSMat

variable {ι : Type} [Fintype ι]

theorem cs_dot (u v : ι → ℂ) : ‖star u ⬝ᵥ v‖ ^ 2 ≤ ‖star u ⬝ᵥ u‖ * ‖star v ⬝ᵥ v‖ := by
  have hgen : ∀ a b : ι → ℂ, star a ⬝ᵥ b =
      inner ℂ (WithLp.toLp 2 a : EuclideanSpace ℂ ι) (WithLp.toLp 2 b : EuclideanSpace ℂ ι) := by
    intro a b
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [hgen u v, hgen u u, hgen v v, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  set y : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm, Complex.norm_real, norm_norm]
  calc _ ≤ (‖x‖ * ‖y‖) ^ 2 := by gcongr
    _ = _ := by ring

theorem cs_factor (Q : Matrix ι ι ℂ) (s : ℂ) (hs : ‖s‖ = 1) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ ^ 2 ≤
      ‖star a ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ a‖ * ‖star b ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ b‖ := by
  have key : ∀ x y : ι → ℂ,
      star x ⬝ᵥ (s • (Qᴴ * Q)) *ᵥ y = s * (star (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y)) := by
    intro x y
    rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec,
      smul_eq_mul]
  simp only [key, norm_mul, hs, one_mul]
  exact cs_dot _ _

end CSMat

theorem cT_eq_conjTranspose {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply]

theorem factor_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (p q : ℕ) (h : Formalism.UG.HasSignature G p q)
    (hpq : q = 0 ∨ p = 0) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (s : ℂ),
      ‖s‖ = 1 ∧ G.reindex e e = s • (Qᴴ * Q) := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_eq_conjTranspose] at hP
  have h1 : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
      ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hM : G.reindex e e = ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
      Formalism.UG.Jpq p q * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    rw [← hP]
    calc G.reindex e e = (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ *
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ) * G.reindex e e *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
            ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
          rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rcases hpq with rfl | rfl
  · refine ⟨e, ((P⁻¹ : GL (Fin p ⊕ Fin 0) ℂ) : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ), 1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq p 0 = 1 := by
      ext (i | i) (j | j)
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0
    rw [hM, hJ, Matrix.mul_one, one_smul]
  · refine ⟨e, ((P⁻¹ : GL (Fin 0 ⊕ Fin q) ℂ) : Matrix (Fin 0 ⊕ Fin q) (Fin 0 ⊕ Fin q) ℂ), -1, by simp, ?_⟩
    have hJ : Formalism.UG.Jpq 0 q = -1 := by
      ext (i | i) (j | j)
      · exact i.elim0
      · exact i.elim0
      · exact j.elim0
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
    rw [hM, hJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_one_smul]

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phi_hT (S : HSpace E) (φ : E →+* ℂ) (hstar : ∀ a, φ (star a) = star (φ a)) (x y : S.V) :
    φ (S.hT x y) = star (fun i => φ (S.frame.repr x i)) ⬝ᵥ (S.gram.map φ) *ᵥ (fun j => φ (S.frame.repr y j)) := by
  rw [hT_expand]
  simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, hstar,
    Finset.mul_sum]

theorem dot_reindex {m ι : Type} [Fintype m] [Fintype ι] (e : m ≃ ι) (G : Matrix m m ℂ) (a b : m → ℂ) :
    star (a ∘ e.symm) ⬝ᵥ (G.reindex e e) *ᵥ (b ∘ e.symm) = star a ⬝ᵥ G *ᵥ b := by
  rw [reindex_apply, submatrix_mulVec_equiv]
  have hb : (b ∘ e.symm) ∘ e.symm.symm = b := by
    funext x
    simp
  rw [hb]
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (a i) * (G *ᵥ b) i)

theorem csAt_of_definite (S : HSpace E) (hstar : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hdef : S.IsDefinite) : CSAt S := by
  intro φ x y
  obtain ⟨e, Q, s, hs, hG⟩ := factor_of_sig (S.gram.map φ) (S.sig φ).1 (S.sig φ).2 (hsig φ)
    (by rcases hdef φ with h | h <;> simp [h])
  simp only [phi_hT S φ (hstar φ)]
  rw [← dot_reindex e, ← dot_reindex e, ← dot_reindex e, hG]
  exact cs_factor Q s hs _ _

theorem csAt_of_isomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) (hι : HSpace.IsIsomEmb S S' ι) (h : CSAt S') :
    CSAt S := by
  intro φ x y
  rw [← hι x y, ← hι x x, ← hι y y]
  exact h φ (ι x) (ι y)

end CSSpace

section CSRecord

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem host_star (D : D7) (φ : D.host.E →+* ℂ) (a : D.host.E) : φ (star a) = star (φ a) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ φ a

theorem csAt_X (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : CSAt (D.sp.X i) :=
  csAt_of_definite (D.sp.X i) (host_star D) (D.sp.X_sig i) (D.sp.X_def i hi)

theorem csAt_X' (D : D7) : CSAt D.sp.X' :=
  csAt_of_isomEmb D.sp.X' (D.sp.X D.R.m) D.sp.iX' D.sp.iX'_isom (csAt_X D D.R.m le_rfl)

def FrameCoordAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (S : HSpace D.host.E) (q n : ℕ) : Prop :=
  ShortFrame S q (msRho D u C₀ n) ∧ CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n)

theorem msCount_of_frames (D : D7) (C₀ : ℝ) (hC : 3 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, FrameCoordAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
      FrameCoordAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : MsCount D C₀ :=
  msCount_of_short D C₀ hC fun u =>
    ⟨fun i hi => ⟨((h u).1 i hi).1, csAt_X D i hi, ((h u).1 i hi).2⟩, ⟨(h u).2.1, csAt_X' D, (h u).2.2⟩⟩

theorem Link1F_of_frames
    (h : ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
      Transference → ∃ C₀ : ℝ, 3 ≤ C₀ ∧ Formalism.MainNotions.flipTwoThree.fam0 Fm fun D => ∀ u : D.what₂.Word,
        (∀ i ≤ D.R.m, FrameCoordAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
        FrameCoordAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : Link1F :=
  Link1F_of_count fun eps Fm hH hT => by
    obtain ⟨C₀, hC, x0, h0⟩ := h eps Fm hH hT
    exact ⟨C₀, by linarith, x0, fun x hx hx1 i => msCount_of_frames _ C₀ hC (h0 x hx hx1 i)⟩

end CSRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

