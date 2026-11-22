import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
import Formalism.HermitianCurvature.OperatorsCommuteTranslations

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OmegaNormCofactorOfParts
section
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem cofactorPair_statement : C7.CofactorPair := by
  intro V _ _ B r f x'
  constructor
  · intro a
    have h := congrArg (fun M => M a (Fin.last r)) (Matrix.mul_adjugate (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX'
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← h]
    apply Finset.sum_congr rfl; intro b _; rw [mul_comm]; rfl
  · intro b
    have h := congrArg (fun M => M (Fin.last r) b) (Matrix.adjugate_mul (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX
    simp only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
    have e : (if b = Fin.last r then (C7.zhat B f x').det else 0) =
        (if Fin.last r = b then (C7.zhat B f x').det else 0) := by
      by_cases hb : b = Fin.last r <;> simp [hb, eq_comm]
    rw [e, ← h]
    rfl

theorem cofactor_corner_identity : C7.CofactorCorner := by
  intro r Z
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold C7.minorR
  have : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

theorem adjLastCol_statement : C7.AdjLastCol := by
  intro r Z l u hl1 hl2 hu1 hu2 b
  have hdl : l.det = 1 := by
    rw [Matrix.det_of_lowerTriangular l (fun i j h => hl1 i j h)]; simp [hl2]
  have hdu : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hu1 i j h)]; simp [hu2]
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, M.det = 1 → adjugate M = M⁻¹ := by
    intro M hM; rw [Matrix.inv_def, hM]; simp
  have hcol : ∀ d, l d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    by_cases hd : d = Fin.last r
    · subst hd; simp [hl2]
    · rw [if_neg hd]; exact hl1 d _ (Fin.lt_last_iff_ne_last.2 hd)
  have hinv : ∀ d, l⁻¹ d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have e : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l (by rw [hdl]; exact isUnit_one)
    have := congrArg (fun M => M d (Fin.last r)) e
    simp only [Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Matrix.one_apply] at this
    rw [this]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadj u hdu, hadj l hdl, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro c _
  congr 1
  rw [Matrix.mul_apply]
  simp [hinv]

theorem gram_cofactor_identity : C7.GramCofactor := by
  intro V _ _ B r f x' T' h
  unfold C7.cofX'
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.map_smulₛₗ, h]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [cofactor_corner_identity r (C7.zhat B f x')]
  rw [← Complex.mul_conj]
  ring

theorem omega_norm_identity : C7.OmNorm := by
  intro V _ _ B x ω z T T' D Dr hH hT hxx hxω hxz hωz hzz hv
  have hωx : B ω x = 0 := by rw [hH x ω, hxω, map_zero]
  have hzx : B z x = 0 := by rw [hH x z, hxz, map_zero]
  have hzω : B z ω = 0 := by rw [hH ω z, hωz, map_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    hxx, hxω, hxz, hωx, hωz, hzx, hzω, hzz] at hv
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc : (-D / T) * (starRingEnd ℂ) (-D / T) = (Complex.normSq D : ℂ) / T ^ 2 := by
    rw [map_div₀, map_neg, Complex.conj_ofReal, ← Complex.mul_conj]; field_simp
  have e : B ω ω = -(T' : ℂ) * Complex.normSq Dr + (Complex.normSq D : ℂ) / T ^ 2 * T := by
    rw [← hc]; linear_combination hv
  rw [e]; field_simp; ring

theorem omNormCofactor_statement : C7.OmNormCofactor := by
  intro V _ _ B r f x' x ω z T T' hH hT hG hxx hxω hxz hωz hzz hcof
  have hv := gram_cofactor_identity V B r f x' T' hG
  rw [hcof] at hv
  exact omega_norm_identity V B x ω z T T' _ _ hH hT hxx hxω hxz hωz hzz hv

theorem omNormCofactorOfParts_statement : C7.OmNormCofactorOfParts := fun _ _ => omNormCofactor_statement

theorem scalar_pair_common_factor : C7.ScalarPairCommon := by
  intro V _ _ B V' _ _ ω₁ ω₂ ω₁' ω₂' D₁ D₂ Dr₁ Dr₂ T T' hD1 hD2 hT hT' h2 h2' hn1 hn2
  have hcD1 : (starRingEnd ℂ) D₁ ≠ 0 := (map_ne_zero _).2 hD1
  have hcD2 : (starRingEnd ℂ) D₂ ≠ 0 := (map_ne_zero _).2 hD2
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, smul_smul]; congr 1; field_simp
  · rw [h2', smul_smul]; congr 1; rw [map_div₀]; field_simp
  · have hu : (D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁) = (Complex.normSq D₂ : ℂ) / Complex.normSq D₁ := by
      rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj]
    rw [h2] at hn2
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at hn2
    have hN1 : (Complex.normSq D₁ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hD1).ne'
    have e : (T : ℂ) * ((starRingEnd ℂ) (D₂ / D₁) * (D₂ / D₁ * B ω₁ ω₁)) =
        ((D₂ / D₁) * (starRingEnd ℂ) (D₂ / D₁)) * (T * B ω₁ ω₁) := by ring
    rw [e, hu, hn1] at hn2
    have hTT : ((T : ℂ) * T') ≠ 0 := by
      have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      have : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
      exact mul_ne_zero (by assumption) (by assumption)
    have key : (Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      have h3 : ((T : ℂ) * T') * ((Complex.normSq D₂ : ℂ) * Complex.normSq Dr₁ -
          Complex.normSq D₁ * Complex.normSq Dr₂) = 0 := by
        field_simp at hn2
        linear_combination (-1 : ℂ) * hn2
      have := (mul_eq_zero.1 h3).resolve_left hTT
      linear_combination this
    have keyR : Complex.normSq D₂ * Complex.normSq Dr₁ = Complex.normSq D₁ * Complex.normSq Dr₂ := by
      exact_mod_cast key
    have p1 := Complex.normSq_pos.2 hD1
    have p2 := Complex.normSq_pos.2 hD2
    constructor
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₂ = 0 := by
        rcases mul_eq_zero.1 keyR.symm with h' | h'
        · exact absurd h' p1.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this
    · intro h; rw [h, Complex.normSq_zero, mul_zero] at keyR
      have : Complex.normSq Dr₁ = 0 := by
        rcases mul_eq_zero.1 keyR with h' | h'
        · exact absurd h' p2.ne'
        · exact h'
      exact Complex.normSq_eq_zero.1 this

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialTheoremCorollary
section
namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix

theorem normW_append {S : Type} (nn : ℝ → ℝ) (L w : List (Letter ℂ S)) :
    normW nn (L ++ w) = normW nn L * normW nn w := by
  unfold normW; rw [List.map_append, List.prod_append]

theorem normW_Lp {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn (Lp sl y) = ∏ a, nn (y a) := by
  unfold normW Lp
  rw [List.map_ofFn, List.prod_ofFn]
  simp [Function.comp_def]

theorem normW_Lp_dl {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn ((Lp sl y).map dl) = ∏ a, nn (y a + 1) := by
  unfold normW Lp
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  simp [Function.comp_def, dl]

theorem key (a b Q W N N' T c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 < Q) (hW : 0 < W)
    (hN : 0 < N) (hN' : 0 < N') (hT : 0 ≤ T) (hc : 0 ≤ c) (hNT : N * N' / Q ≤ T ^ 2) :
    c * Real.sqrt (a * b / Q) / W ≤ c * T * ((a / (N * W) + b / (N' * W)) / 2) := by
  have hA : 0 ≤ a / (N * W) := by positivity
  have hB : 0 ≤ b / (N' * W) := by positivity
  have e : a * b / Q = W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q) := by
    field_simp
  have hAB : (a / (N * W)) * (b / (N' * W)) ≤ ((a / (N * W) + b / (N' * W)) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a / (N * W) - b / (N' * W))]
  have h1 : a * b / Q ≤ (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by
    rw [e]
    calc W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q)
        ≤ W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * T ^ 2 :=
          mul_le_mul_of_nonneg_left hNT (by positivity)
      _ ≤ W ^ 2 * ((a / (N * W) + b / (N' * W)) / 2) ^ 2 * T ^ 2 := by gcongr
      _ = (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by ring
  have h2 : Real.sqrt (a * b / Q) ≤ W * T * ((a / (N * W) + b / (N' * W)) / 2) :=
    (Real.sqrt_le_left (by positivity)).mpr h1
  calc c * Real.sqrt (a * b / Q) / W ≤ c * (W * T * ((a / (N * W) + b / (N' * W)) / 2)) / W := by
        gcongr
    _ = c * T * ((a / (N * W) + b / (N' * W)) / 2) := by field_simp

theorem lagCo_ne {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.ne_of_mem_erase hi) (hy h).symm

theorem cg_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) : 0 < cg y := by
  unfold cg
  have h0 : 0 < |F7.lagCo y 0| := abs_pos.mpr (lagCo_ne y hy 0)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun k => |F7.lagCo y k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ 0))

theorem p1c : NormaliserLowerBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs hData
    hG0 hImp hinj hadm hnn hQw hBB
  have hu := u72 A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid hData hG0 hImp hinj hadm
  obtain ⟨-, -, -, hK, -, -, -, -, -, -, -⟩ := id hData
  let a0 : Fin K := ⟨0, by omega⟩
  let j0 : Fin K → Fin (2 * n + 1) := fun _ => ⟨0, by omega⟩

  have hlet : ∀ (j : Fin K → Fin (2 * n + 1)) (a : Fin K),
      grid a (j a) ∈ Set.Ioo α β ∧ grid a (j a) + 1 ∈ Set.Ioo α β ∧
        0 < (q (grid a (j a))).re ∧ 0 < (qw q w (grid a (j a))).re := by
    intro j a
    have hm := mem_Lp sl (fun a => grid a (j a)) a
    obtain ⟨-, h2, h3⟩ := (hadm j).1.2.1 _ (List.mem_append_left _ hm)
    simp only [Complex.ofReal_re, if_true] at h2 h3
    refine ⟨h2, h3, (hG0 _ h2).2, ?_⟩
    exact ((admissible_dual_kernel_identity S α β q w _ (plus_Lp sl _) hG0 (hadm j).1 (hadm j).2).2 _ hm).2
  have hWpos : 0 < normW nn w := by
    refine normW_pos nn w fun l hl => hnn _ ?_
    exact ((hadm j0).1.2.1 l (List.mem_append_right _ hl)).2.1
  have hQw0 : 0 ≤ Qw := by
    have h := hQw a0 (j0 a0)
    obtain ⟨-, -, hq, hqw⟩ := hlet j0 a0
    exact le_trans (div_pos hq hqw).le h
  have hBB0 : 0 ≤ BBs := le_trans (Real.sqrt_nonneg _) (hBB a0 (j0 a0))
  set T := (Real.sqrt Qw * BBs) ^ K with hT
  have hT0 : 0 ≤ T := by positivity
  have hpowK : ∀ c : ℝ, c ^ K = ∏ _a : Fin K, c := fun c => by simp
  have hcg : ∀ a, 0 < cg (grid a) := fun a => cg_pos (grid a) (hinj a)

  have hid : ∀ j : Fin K → Fin (2 * n + 1), (∏ a, cg (grid a) * Real.sqrt Qw * BBs) * F7.thGrid grid j =
      (∏ a, |F7.lagCo (grid a) (j a)|) * T := by
    intro j
    unfold F7.thGrid
    rw [← Finset.prod_mul_distrib, hT, hpowK (Real.sqrt Qw * BBs), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hcg a).ne'
    unfold cg at this ⊢
    field_simp

  have hterm : ∀ j : Fin K → Fin (2 * n + 1),
      (∏ a, |F7.lagCo (grid a) (j a)|) *
        Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re) / normW nn w ≤
      (∏ a, cg (grid a) * Real.sqrt Qw * BBs) *
        (F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) := by
    intro j
    have e : (∏ a, cg (grid a) * Real.sqrt Qw * BBs) *
        (F7.thGrid grid j * (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) =
        ((∏ a, cg (grid a) * Real.sqrt Qw * BBs) * F7.thGrid grid j) *
          ((N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) := by ring
    rw [e, hid j]
    unfold N0
    rw [normW_append, normW_append, normW_Lp, normW_Lp_dl]
    refine key _ _ _ _ _ _ _ _ (hImp _ (hadm j).1 _).1 (hImp _ (hadm j).2 _).1
      (Finset.prod_pos fun a _ => (hlet j a).2.2.2) hWpos
      (Finset.prod_pos fun a _ => hnn _ (hlet j a).1) (Finset.prod_pos fun a _ => hnn _ (hlet j a).2.1)
      hT0 (Finset.prod_nonneg fun a _ => abs_nonneg _) ?_
    have hsq : ((Real.sqrt Qw * BBs) ^ K) ^ 2 = ∏ _a : Fin K, (Real.sqrt Qw * BBs) ^ 2 := by
      rw [← pow_mul, mul_comm K 2, pow_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib, hT, hsq]
    refine Finset.prod_le_prod (fun a _ => ?_) fun a _ => ?_
    · obtain ⟨h1, h2, -, hqw⟩ := hlet j a
      have := hnn _ h1
      have := hnn _ h2
      positivity
    · obtain ⟨h1, h2, hq, hqw⟩ := hlet j a
      have hn1 := hnn _ h1
      have hn2 := hnn _ h2
      have hb := (Real.sqrt_le_left hBB0).mp (hBB a (j a))
      have hqq := hQw a (j a)
      have e2 : nn (grid a (j a)) * nn (grid a (j a) + 1) / (qw q w (grid a (j a))).re =
          (nn (grid a (j a)) * nn (grid a (j a) + 1) / (q (grid a (j a))).re) *
            ((q (grid a (j a))).re / (qw q w (grid a (j a))).re) := by
        field_simp
      rw [e2, mul_pow, Real.sq_sqrt hQw0, mul_comm Qw]
      exact mul_le_mul hb hqq (by positivity) (by positivity)

  have hW := hWpos
  calc ‖s‖ ^ K * (‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w)
      = ‖s‖ ^ K * ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w := by ring
    _ ≤ (∑ j : Fin K → Fin (2 * n + 1), (∏ a, |F7.lagCo (grid a) (j a)|) *
          Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re)) / normW nn w := by gcongr
    _ = ∑ j : Fin K → Fin (2 * n + 1), (∏ a, |F7.lagCo (grid a) (j a)|) *
          Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re) / normW nn w := Finset.sum_div _ _ _
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hterm j

theorem first_polynomial_corollary_identity : SmallParameterNormBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs X hData
    hG0 hImp hinj hAw hadm hnn hQw hBB hX
  obtain ⟨-, hW, hWQ, hK, -, -, hnd, -, -, -, -⟩ := id hData
  have hWpos : 0 < normW nn w := normW_pos nn w fun l hl => hnn _ (hAw.2.1 l hl).2.1
  refine ⟨fun _ => ?_, fun hXs => ?_⟩
  · exact p1a A S V ρ QQ f fi s nn w x hW hWQ hnd (hImp w hAw) fun l hl => hnn _ (hAw.2.1 l hl).2.1
  · have hc := p1c A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs hData hG0 hImp hinj
      hadm hnn hQw hBB
    let a0 : Fin K := ⟨0, by omega⟩
    let j0 : Fin K → Fin (2 * n + 1) := fun _ => ⟨0, by omega⟩
    have hBB0 : 0 ≤ BBs := le_trans (Real.sqrt_nonneg _) (hBB a0 (j0 a0))
    have hfac0 : ∀ a, 0 ≤ cg (grid a) * Real.sqrt Qw * BBs := fun a => by
      have : 0 ≤ cg (grid a) := Finset.sum_nonneg fun k _ => abs_nonneg _
      positivity
    have hX0 : 0 ≤ X := le_trans (hfac0 a0) (hX a0)
    have hs : 0 < ‖s‖ := lt_of_le_of_lt hX0 hXs
    have hprod : ∏ a, cg (grid a) * Real.sqrt Qw * BBs ≤ X ^ K := by
      calc ∏ a, cg (grid a) * Real.sqrt Qw * BBs ≤ ∏ _a : Fin K, X :=
            Finset.prod_le_prod (fun a _ => hfac0 a) fun a _ => hX a
        _ = X ^ K := by simp
    have hsum : 0 ≤ ∑ j : Fin K → Fin (2 * n + 1), F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2 := by
      refine Finset.sum_nonneg fun j _ => ?_
      have ht : 0 ≤ F7.thGrid grid j := by
        unfold F7.thGrid
        exact Finset.prod_nonneg fun a _ =>
          div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _)
      have hn1 : 0 ≤ N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
          (letters vA vB (Lp sl (fun a => grid a (j a))) x) := by
        unfold N0
        exact div_nonneg (hImp _ (hadm j).1 _).1 (normW_pos nn _ fun l hl =>
          hnn _ ((hadm j).1.2.1 l hl).2.1).le
      have hn2 : 0 ≤ N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
          (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x) := by
        unfold N0
        exact div_nonneg (hImp _ (hadm j).2 _).1 (normW_pos nn _ fun l hl =>
          hnn _ ((hadm j).2.2.1 l hl).2.1).le
      positivity
    have h1 := le_trans hc (mul_le_mul_of_nonneg_right hprod hsum)
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hs K)]
    linarith [h1, mul_comm (‖s‖ ^ K)
      (‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w)]

theorem first_polynomial_theorem_alt : PlaneWaveBoundAllPlaces := ⟨p1a, first_polynomial_degree, u72, p1c, first_polynomial_corollary_identity⟩

theorem p1cOfParts : NormaliserBoundOfParts := fun _ _ => p1c

theorem first_polynomial_corollary_of_parts : SmallParameterBoundOfParts := fun _ _ => first_polynomial_corollary_identity

theorem first_polynomial_theorem_of_parts : PlaneWaveTheoremOfParts := fun _ _ _ _ _ _ _ _ => first_polynomial_theorem_alt

end Formalism.FourierDecayAlt.P.WordNormLpLemmas

theorem Formalism.FourierDecayAlt.P.first_polynomial_third_clause : Formalism.FourierDecayAlt.FormPairingAction.NormaliserLowerBound := Formalism.FourierDecayAlt.P.WordNormLpLemmas.p1c
theorem Formalism.FourierDecayAlt.P.first_polynomial_corollary : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterNormBound := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_corollary_identity
theorem Formalism.FourierDecayAlt.P.first_polynomial_theorem : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveBoundAllPlaces := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_theorem_alt
theorem Formalism.FourierDecayAlt.P.third_clause_of_parts : Formalism.FourierDecayAlt.FormPairingAction.NormaliserBoundOfParts := Formalism.FourierDecayAlt.P.WordNormLpLemmas.p1cOfParts
theorem Formalism.FourierDecayAlt.P.corollary_of_parts : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterBoundOfParts := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_corollary_of_parts
theorem Formalism.FourierDecayAlt.P.first_polynomial_theorem_of_components : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveTheoremOfParts :=
  Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_theorem_of_parts
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem sgn_step (s : ℕ) : s * (s - 1) / 2 + (s + 1) * (s + 1 - 1) / 2 = s * s := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 1) * (s + 1 - 1) / 2 * 2 = (s + 1) * (s + 1 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
  have h3 : s * (s - 1) + (s + 1) * (s + 1 - 1) = 2 * (s * s) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 1) * (s + 1 - 1) = B at *
  generalize s * s = C at *
  omega

theorem sgn_step2 (s : ℕ) : s * (s - 1) / 2 + (s + 2) * (s + 2 - 1) / 2 = s * (s + 1) + 1 := by
  have h1 : s * (s - 1) / 2 * 2 = s * (s - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self s).two_dvd
  have h2 : (s + 2) * (s + 2 - 1) / 2 * 2 = (s + 2) * (s + 2 - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 2)).two_dvd
  have h3 : s * (s - 1) + (s + 2) * (s + 2 - 1) = 2 * (s * (s + 1) + 1) := by
    cases s with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel, show n + 1 + 2 - 1 = n + 2 by omega]; ring
  generalize s * (s - 1) = A at *
  generalize (s + 2) * (s + 2 - 1) = B at *
  generalize s * (s + 1) = C at *
  omega

theorem neg_one_pow_sq (s : ℕ) : (-1 : ℂ) ^ (s * s) = (-1) ^ s := by
  rcases Nat.even_or_odd s with h | h
  · rw [Even.neg_one_pow h, Even.neg_one_pow (h.mul_left s)]
  · rw [Odd.neg_one_pow h, Odd.neg_one_pow (h.mul h)]

theorem sign_permutation_identity : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring

theorem sgnW_succ (m : ℕ) : sgnW (m + 1) = (-1) ^ m * sgnW m := by
  have h := (sign_permutation_identity m).1
  have hsq : sgnW m * sgnW m = 1 := by
    unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp
  calc sgnW (m + 1) = (sgnW m * sgnW m) * sgnW (m + 1) := by rw [hsq, one_mul]
    _ = sgnW m * (sgnW m * sgnW (m + 1)) := by ring
    _ = (-1) ^ m * sgnW m := by rw [h]; ring

theorem antidiagonal_determinant : AntiDiagDet := by
  intro m
  induction m with
  | zero => simp [sgnW]
  | succ m ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last m)]
    · have hsub : ((Matrix.of fun a b : Fin (m + 1) => if a.val + b.val + 1 = m + 1 then (1 : ℂ) else 0).submatrix
          Fin.succ (Fin.last m).succAbove) =
          Matrix.of fun a b : Fin m => if a.val + b.val + 1 = m then (1 : ℂ) else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]
        congr 1
        apply propext; omega
      rw [hsub, ih, sgnW_succ]
      simp
    · intro j _ hj
      have hne : (j : ℕ) ≠ m := by intro h; apply hj; ext; simp [h]
      simp [hne]
    · simp

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

