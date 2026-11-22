import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0004
import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

theorem fin_smul_self (u : XFF F E nS nT) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) • (u : WOF F E nS nT) = u := by
  have h0 : pairA F 1 0 • (u : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (XFF.fin u)
  have h := PositivityTheory.ThKW.LatA.dec (u : WOF F E nS nT)
  rw [h0, zero_add] at h
  rw [algebraMap_smul]
  exact h.symm

theorem int_smul_mem {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ (latF F E nS nT Λ).toAddSubgroup) : a • u ∈ (latF F E nS nT Λ).toAddSubgroup := by
  show ((a • u : XFF F E nS nT) : WOF F E nS nT) ∈ latOF F E nS nT Λ
  rw [XFF.coe_asmul, ← fin_smul_self u, smul_smul, mul_comm, fin_mul_eq]
  exact liftF_smul_mem ha hu

theorem int_smul_mem_map {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (p : GAF σ JS × GAF σ JT) {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup) :
    a • u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨a • y, int_smul_mem ha hy, XFF.ext ?_⟩
  rw [coe_rhoFF, XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF, actOF_smul]

theorem mul_e_zero {a e : AEF F E} (ha : finPartF F E a = 0)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) : a * e = 0 := by
  rw [← hf, ← mul_assoc, mul_comm a, fin_mul_eq, ha, map_zero, zero_mul]

theorem finPart_cAF_zero {a : AEF F E} (ha : finPartF F E a = 0) : finPartF F E (cAF σ a) = 0 := by
  have hr : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 1 := rfl
  have hf : finPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 0 := TensorProduct.zero_tmul _ _
  have e : a = algebraMap (AF F) (AEF F E) (pairA F 1 0) * a := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · rw [map_sub, map_mul, hr, one_mul, sub_self]
    · rw [map_sub, map_mul, hf, ha, zero_mul, sub_self]
  rw [e, map_mul, GlobalTheory.HeisThetaF.cAF_algebraMap, map_mul, hf, zero_mul]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) :
    ∃ (r : 𝓞 E) (s : AEF F E), finPartF F E s ∈ hatO (F := F) E ∧ finPartF F E (cAF σ s) ∈ hatO (F := F) E ∧
      z = finPartF F E (incAF F E (r : E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, ⟨t, rfl⟩, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F k hk).2 α hα
    refine ⟨algebraMap (𝓞 F) (𝓞 E) x * t, pairA F 0 β ⊗ₜ[F] (t : E),
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨t, rfl⟩, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨sgOF σ t, rfl⟩, rfl⟩, ?_⟩
    rw [hx, map_add, map_nsmul]
    exact GlobalTheory.SplitIndex.tmul_split β (x : F) k (t : E)
  | zero => exact ⟨0, 0, by rw [map_zero]; exact zero_mem _,
      by rw [map_zero, map_zero]; exact zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [map_add]; exact add_mem h1 h1',
      by rw [map_add, map_add]; exact add_mem h2 h2', ?_⟩
    rw [← map_add]
    congr 1
    push_cast
    rw [map_add, smul_add]
    abel
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [map_neg]; exact neg_mem h1,
      by rw [map_neg, map_neg]; exact neg_mem h2, ?_⟩
    rw [← map_neg]
    congr 1
    push_cast
    rw [map_neg, smul_neg, neg_add]

theorem split_mem (h : IsCMExt F E σ) {e : AEF F E} (hee : e * e = e)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) (hec : e * cAF σ e = 0) {q : ℕ} (hq : q.Prime)
    (hin : InertQF σ q) {x : XFF F E nS nT} (hx : q • x ∈ (latF F E nS nT Λ).toAddSubgroup) :
    e • x ∈ (latF F E nS nT Λ).toAddSubgroup := by
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hee])
  obtain ⟨r, s, hs, hs', hz⟩ := approx (σ := σ) hq.pos heI
  have h0 : finPartF F E (e - (incAF F E (r : E) + q • s)) = 0 := by rw [map_sub, ← hz, sub_self]
  have h0' := finPart_cAF_zero (σ := σ) h0
  rw [map_sub, map_add, map_nsmul, GlobalTheory.HeisLineF.cAF_incAF, ← coe_sgOF] at h0'
  refine GlobalTheory.SplitIndex.core_split ((incAF F E).comp (algebraMap (𝓞 E) E)) _
    (fun a => finPartF F E a ∈ hatO (F := F) E) (fun a ha u hu => int_smul_mem ha hu)
    (fun r => AddSubgroup.subset_closure ⟨1, fun v => GlobalTheory.AdLat.adele_one_integral F v, _, ⟨r, rfl⟩, rfl⟩)
    q x hx e (cAF σ e) s (cAF σ s) heI hs hs' hee hec r (sgOF σ r) (mul_e_zero h0 hf) (mul_e_zero h0' hf) ?_
  intro P hP hqP hr
  have := hin P hP hqP _ hr
  rwa [show sgOF σ (sgOF σ r) = r from RingOfIntegers.ext (sg_sg h _)] at this

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : GAF σ J) : mtF σ J (a * b) = mtF σ J a * mtF σ J b := by
  simp only [mtF, map_mul, Units.val_mul]

theorem mtF_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mtF σ J 1 = 1 := by
  simp only [mtF, map_one, Units.val_one]

theorem supp_smul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  ext i j
  have := hg i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
  linear_combination -this

theorem supp_smul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  calc (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E))) * mtF σ J g⁻¹ := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = ((1 - (e + cAF σ e)) • mtF σ J g) * mtF σ J g⁻¹ := by rw [supp_smul hg]
    _ = _ := by rw [Matrix.smul_mul, ← mtF_mul, mul_inv_cancel, mtF_one]

theorem act_supp {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {e : AEF F E}
    {g : GAF σ JS} {k : GAF σ JT} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) (y : WOF F E nS nT) :
    (1 - (e + cAF σ e)) • actOF σ JS JT g k y = (1 - (e + cAF σ e)) • y := by
  unfold actOF
  calc (1 - (e + cAF σ e)) • (mtF σ JT k * y * mtF σ JS g⁻¹)
      = ((1 - (e + cAF σ e)) • mtF σ JT k) * y * mtF σ JS g⁻¹ := by rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nT) (Fin nT) (AEF F E))) * y * mtF σ JS g⁻¹ := by rw [supp_smul hk]
    _ = y * ((1 - (e + cAF σ e)) • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = y * ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nS) (Fin nS) (AEF F E))) := by rw [supp_smul_inv hg]
    _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem idx_main (h : IsCMExt F E σ) {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g k, SuppAtF σ e JS g → SuppAtF σ e JT k → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) := by
  intro e he g k hg hk q hq hin
  obtain ⟨hf, hfc, hcc⟩ := split_parts he
  have hc2 : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ (sg_sg h) e
  have hec : e * cAF σ e = 0 := he.2.1
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he.1])
  have hcI : finPartF F E (cAF σ e) ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hcc])
  have hcI' : finPartF F E (1 - (e + cAF σ e)) ∈ hatO (F := F) E := by
    rw [map_sub, map_add, map_one]
    exact sub_mem (GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩) (add_mem heI hcI)
  refine GlobalTheory.SplitIndex.not_dvd_of_saturated _ _ (hfin (g, k)) hq fun x hx hqx => ?_
  refine GlobalTheory.SplitIndex.mem_of_parts _ e (cAF σ e) x (split_mem h he.1 hf hec hq hin hqx)
    (split_mem h hcc hfc (by rw [hc2, mul_comm, hec]) hq hin hqx) ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have e1 : (1 - (e + cAF σ e)) • rhoFF σ JS JT (g, k) y = (1 - (e + cAF σ e)) • y :=
    XFF.ext (by rw [XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF]; exact act_supp hg hk _)
  rw [e1]
  exact int_smul_mem hcI' hy

end PositivityTheory.ThKW.LatB

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

section

variable {R : Type} [CommRing R] {n : ℕ}

abbrev aC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1)).submatrix finSumFinEquiv.symm id

theorem CC_add : dC R n * (dC R n)ᵀ + aC R n * (aC R n)ᵀ = (2 : R) • 1 := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [diagCols, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id, Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply] <;> split_ifs <;>
    first | (simp_all; done) | (simp_all; norm_num; done) | norm_num

theorem C_D (J : Matrix (Fin n) (Fin n) R) :
    (dC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (aC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_D (J : Matrix (Fin n) (Fin n) R) :
    (aC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (dC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_C : (aC R n)ᵀ * dC R n = 0 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp

theorem C_A : (dC R n)ᵀ * aC R n = 0 := by
  have := congrArg Matrix.transpose (A_C (R := R) (n := n))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this

theorem ring_facts {A : Type} [Ring A] [Algebra R A] {Q Q' D N : A} {x y : R} (hxy : x * y = 1) (h1 : Q + Q' = 1)
    (hQ : Q * Q' = 0) (hQ' : Q' * Q = 0) :
    (x • Q + y • Q') * (y • Q + x • Q') = 1 ∧
    (Q * D * Q = 0 → Q' * D * Q' = 0 → (x • Q + y • Q') * D * (x • Q + y • Q') = D) ∧
    (N * Q = 0 → Q' * N = 0 → N * N = 0 ∧ (x • Q + y • Q') * N * (y • Q + x • Q') = (x * x) • N) := by
  have e1 : Q * Q = Q := by
    have := congrArg (Q * ·) h1
    simpa only [mul_add, hQ, add_zero, mul_one] using this
  have e2 : Q' * Q' = Q' := by
    have := congrArg (Q' * ·) h1
    simpa only [mul_add, hQ', zero_add, mul_one] using this
  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  refine ⟨?_, fun a b => ?_, fun a b => ?_⟩
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, e1, e2, hQ, hQ', smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul, h1]
  · have hD : D = (Q + Q') * D * (Q + Q') := by rw [h1, one_mul, mul_one]
    conv_rhs => rw [hD]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, a, b, smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul]
  · have c1 : Q * N = N := by
      have := congrArg (· * N) h1
      simpa only [add_mul, b, add_zero, one_mul] using this
    have c2 : N * Q' = N := by
      have := congrArg (N * ·) h1
      simpa only [mul_add, a, zero_add, mul_one] using this
    refine ⟨by rw [← c2, mul_assoc, ← mul_assoc Q', b, zero_mul, mul_zero], ?_⟩
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, c1, b, smul_zero, add_zero, mul_add, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, a, c2, smul_zero, smul_zero, zero_add, smul_smul]

theorem one_add_pow {A : Type} [Ring A] {N : A} (h : N * N = 0) (m : ℕ) : (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc m N N, h, succ_nsmul]; simp [add_assoc, add_comm N]

end

theorem conj_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT → ∀ k : ℕ, 0 < k →
    ∃ (M : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
      mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) M * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 ∧
      ∀ n : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) n * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT →
        M * n * M⁻¹ = n ^ (k * k) := by
  intro F E _ _ _ _ _ σ n J hJ k hk
  let R := AF F ⊗[F] E
  let q : ℚ →+* R := (incAF F E).comp (algebraMap ℚ E)
  have hq : ∀ r, cAF σ (q r) = q r := fun r =>
    congrArg (incAF F E) (show σ (algebraMap ℚ E r) = algebraMap ℚ E r by simp)
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hxy : q k * q (k : ℚ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk', map_one]
  have hyx : q (k : ℚ)⁻¹ * q k = 1 := by rw [mul_comm, hxy]
  have h2 : q (1 / 2) * 2 = 1 := by rw [← map_ofNat q 2, ← map_mul]; norm_num
  let Q : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (dC R n * (dC R n)ᵀ)
  let Q' : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (aC R n * (aC R n)ᵀ)
  let J' := J.map (incAF F E)
  let D : Matrix (Fin (n + n)) (Fin (n + n)) R := (dbl J').submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hD : JR (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) = D := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
    simp only [JR, D, J', GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases p with p | p <;> rcases r with r | r <;> simp
  have h1 : Q + Q' = 1 := by rw [← smul_add, CC_add, smul_smul, h2, one_smul]
  have hQ : Q * Q' = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ' : Q' * Q = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD : Q * D * Q = 0 := by
    simp only [Q, Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (dC R n), C_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD' : Q' * D * Q' = 0 := by
    simp only [Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (aC R n), A_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ'C : Q' * dC R n = 0 := by
    simp only [Q', Matrix.smul_mul]
    rw [Matrix.mul_assoc, A_C]; simp
  have hQC : Q * dC R n = dC R n := by
    have := congrArg (· * dC R n) h1
    simpa only [Matrix.add_mul, hQ'C, add_zero, Matrix.one_mul] using this
  have f1 := fun N => ring_facts (D := D) (N := N) hxy h1 hQ hQ'
  have f2 := ring_facts (D := D) (N := 0) hyx h1 hQ hQ'
  let M : GL (Fin (n + n)) R := ⟨q k • Q + q (k : ℚ)⁻¹ • Q', q (k : ℚ)⁻¹ • Q + q k • Q', (f1 0).1, f2.1⟩
  have haC : (aC R n).map (cAF σ) = aC R n := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    rcases p with p | p <;> simp [Matrix.one_apply, apply_ite (cAF σ)]
  have hsm : ∀ (r : ℚ) (X : Matrix (Fin (n + n)) (Fin (n + n)) R), (q r • X).map (cAF σ) = q r • X.map (cAF σ) :=
    fun r X => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hq]
  have hM : (M.1.map (cAF σ))ᵀ = M.1 := by
    show ((q k • Q + q (k : ℚ)⁻¹ • Q').map (cAF σ))ᵀ = q k • Q + q (k : ℚ)⁻¹ • Q'
    rw [Matrix.map_add _ (map_add _), hsm, hsm, hsm, hsm, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.transpose_map, dC_map, haC]
    simp only [Q, Q', Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmem : M ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) := by
    show (M.1.map (cAF σ))ᵀ * JR (AF F) _ * M.1 = JR (AF F) _
    rw [hM, hD]
    exact (f1 0).2.1 hQD hQD'
  let t : GL (Fin n) R := ⟨q k • 1, q (k : ℚ)⁻¹ • 1, by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hxy, one_smul],
    by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hyx, one_smul]⟩
  refine ⟨(⟨M, hmem⟩ : HR (AF F) σ _), t, ?_, fun g hg => ?_⟩
  · show (q k • Q + q (k : ℚ)⁻¹ • Q') * dC R n = dC R n * (q k • 1)
    rw [Matrix.add_mul, Matrix.smul_mul _ Q, Matrix.smul_mul _ Q', hQC, hQ'C, smul_zero, add_zero, Matrix.mul_smul,
      Matrix.mul_one]
  · set G := mtF σ _ g with hG
    have hu : (G.map (cAF σ))ᵀ * JR (AF F) _ * G = JR (AF F) _ := g.2
    rw [hD] at hu
    have hJu : IsUnit J'.det := by
      have := (Ne.isUnit hJ.2).map (incAF F E)
      rwa [RingHom.map_det] at this
    have a1 : (G - 1) * Q = 0 := by
      simp only [Q, Matrix.mul_smul]
      rw [← Matrix.mul_assoc, Matrix.sub_mul, hg, Matrix.one_mul, sub_self, Matrix.zero_mul, smul_zero]
    have a2 : (aC R n)ᵀ * (G - 1) = 0 := by
      have b1 : (dC R n)ᵀ * (G.map (cAF σ))ᵀ = (dC R n)ᵀ := by
        rw [← Matrix.transpose_mul, ← dC_map (cAF σ) n, ← Matrix.map_mul, hg]
      have b2 : (dC R n)ᵀ * D * G = (dC R n)ᵀ * D := by
        conv_rhs => rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, b1]
      rw [C_D] at b2
      have b3 : J' * ((aC R n)ᵀ * (G - 1)) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, b2, sub_self]
      rw [← Matrix.one_mul (_ * _), ← Matrix.nonsing_inv_mul _ hJu, Matrix.mul_assoc, b3, Matrix.mul_zero]
    have a3 : Q' * (G - 1) = 0 := by
      simp only [Q', Matrix.smul_mul]
      rw [Matrix.mul_assoc, a2, Matrix.mul_zero, smul_zero]
    obtain ⟨n1, n2⟩ := (f1 (G - 1)).2.2 a1 a3
    refine Subtype.ext (Units.ext ?_)
    have e : mtF σ _ (g ^ (k * k)) = G ^ (k * k) := by
      rw [hG, mtF, mtF, map_pow, Units.val_pow_eq_pow_val]
    refine Eq.trans ?_ e.symm
    show (q k • Q + q (k : ℚ)⁻¹ • Q') * G * (q (k : ℚ)⁻¹ • Q + q k • Q') = _
    rw [← add_sub_cancel 1 G, one_add_pow n1, mul_add _ 1 (G - 1), mul_one, add_mul (q k • Q + q (k : ℚ)⁻¹ • Q'),
      (f1 0).1, n2, map_natCast, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalAdelicPairFundamental
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ParsevalPolarization

open GlobalTheory.ThetaTransform

theorem polar_pt (z w : ℂ) : z * starRingEnd ℂ w =
    (((‖z + 1 * w‖ ^ 2 - ‖z + (-1) * w‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((‖z + Complex.I * w‖ ^ 2 - ‖z + (-Complex.I) * w‖ ^ 2 : ℝ) : ℂ)) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem polar {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (f₁ f₂ : X → ℂ) (g₁ g₂ : Y → ℂ) (c : ℝ)
    (hf : ∀ a : ℂ, Integrable (fun x => ‖f₁ x + a * f₂ x‖ ^ 2) μ)
    (hg : ∀ a : ℂ, Integrable (fun y => ‖g₁ y + a * g₂ y‖ ^ 2) ν)
    (h : ∀ a : ℂ, ∫ y, ‖g₁ y + a * g₂ y‖ ^ 2 ∂ν = c * ∫ x, ‖f₁ x + a * f₂ x‖ ^ 2 ∂μ) :
    ∫ y, g₁ y * starRingEnd ℂ (g₂ y) ∂ν = (c : ℂ) * ∫ x, f₁ x * starRingEnd ℂ (f₂ x) ∂μ := by
  have key : ∀ {Z : Type} [MeasurableSpace Z] (ρ : Measure Z) (k₁ k₂ : Z → ℂ),
      (∀ a : ℂ, Integrable (fun x => ‖k₁ x + a * k₂ x‖ ^ 2) ρ) →
      ∫ x, k₁ x * starRingEnd ℂ (k₂ x) ∂ρ =
        (((∫ x, ‖k₁ x + 1 * k₂ x‖ ^ 2 ∂ρ) - ∫ x, ‖k₁ x + (-1) * k₂ x‖ ^ 2 ∂ρ : ℝ) +
          Complex.I * (((∫ x, ‖k₁ x + Complex.I * k₂ x‖ ^ 2 ∂ρ) -
            ∫ x, ‖k₁ x + (-Complex.I) * k₂ x‖ ^ 2 ∂ρ : ℝ) : ℂ)) / 4 := by
    intro Z _ ρ k₁ k₂ hk
    simp_rw [polar_pt (k₁ _) (k₂ _)]
    rw [integral_div, integral_add, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (hk 1) (hk (-1)), integral_sub (hk Complex.I) (hk (-Complex.I))]
    · exact ((hk 1).sub (hk (-1))).ofReal
    · exact (((hk Complex.I).sub (hk (-Complex.I))).ofReal).const_mul _
  rw [key ν g₁ g₂ hg, key μ f₁ f₂ hf, h 1, h (-1), h Complex.I, h (-Complex.I)]
  push_cast
  ring

theorem thV_smul {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {N : ℕ}
    (a : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (a • Φ) = a • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext ξ; ring

theorem parseval_adelic_pair_fundamental : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E}, B.IsGood σ → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  letI mA : MeasurableSpace (Fin N → AF F) := borel _
  letI mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop

  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK, mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₁ hΦ₁) (GlobalTheory.SchwartzDecay.decay_smul a (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this

end PositivityTheory.ThKW.ParsevalPolarization

end
end

