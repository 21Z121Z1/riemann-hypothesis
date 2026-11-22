import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem first_expansion_of_parts : ExpansionFirstCaseFromComponents := by
  unfold ExpansionFirstCaseFromComponents
  intros
  exact first_expansion_identity
theorem second_expansion_of_parts : ExpansionSecondCaseFromComponents := by
  unfold ExpansionSecondCaseFromComponents
  intros
  exact second_expansion_identity
theorem third_expansion_of_parts : ExpansionThirdCaseFromComponents := by
  unfold ExpansionThirdCaseFromComponents
  intros
  exact column_indicator_expansion
theorem fourth_expansion_of_parts : ExpansionFourthCaseFromComponents := by
  unfold ExpansionFourthCaseFromComponents
  intros
  exact fourth_expansion_identity
theorem chain_first_of_parts : LastColumnChainFromComponents := by
  unfold LastColumnChainFromComponents
  intros
  exact chain_first_identity

theorem herm_bvec_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    herm H (bvec p) (bvec q) = H q p := by
  have hs : star (bvec q) = bvec q := by
    ext i
    by_cases h : i = q <;> simp [bvec, Pi.single_apply, h]
  unfold herm
  rw [hs]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

section dp
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))

theorem dp1 (hp : p.val < r) (hq : q.val < r) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_pos ⟨hp, hq⟩]
theorem dp2 (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by
  rw [dpsiP, if_neg (by omega), if_pos ⟨hp, hq1, hq2⟩]
theorem dp0 (hp : p.val < r) (hq : r + k < q.val) : dpsiP k r z' p q = 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem dp3 (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    dpsiP k r z' p q = if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_pos ⟨hp1, hp2, hq⟩]
theorem dp4 (hp : r + k < p.val) (hq : r + k < q.val) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hp, hq⟩]
end dp

theorem hpk_row_eI {k r : ℕ} (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) p = if p.val = 2 * r + k - b.val then 1 else 0 := by
  have hb := b.isLt
  have heI : (eI k r b).val = b.val := rfl
  simp only [Hpk]
  by_cases h : p.val = 2 * r + k - b.val
  · rw [if_pos h, if_pos ⟨by rw [heI]; exact hb, by rw [heI]; omega⟩]
  · rw [if_neg h, if_neg (fun hc => h (by rw [heI] at hc; omega)),
      if_neg (fun hc => by rw [heI] at hc; omega),
      if_neg (fun hc => by rw [heI] at hc; exact absurd hc.1 (by omega))]

theorem right_derivative_rule_psi : RuleRightDpsi := by
  intro k r z' l j hw
  have hl := l.isLt
  have hj := j.isLt
  simp only [Formalism.FourierDecayAlt.Q.mdim, Fin.val_succ] at hj
  have heI : ∀ a : Fin r, (eI k r a).val = a.val := fun _ => rfl
  have hesI : ∀ a : Fin r, (esI k r a).val = 2 * r + k - a.val := fun _ => rfl
  have hqv : (Formalism.FourierDecayAlt.Q.posL k r l.succ j).val = j.val + l.val + 1 := by
    simp only [Formalism.FourierDecayAlt.Q.posL, Fin.val_succ]
    omega
  have hz : ∀ q : Fin (2 * r + k + 1), (q.val < r ∨ r + k < q.val) →
      herm (Hpk k r) (bvec q) z' = 0 := by
    intro q hq
    unfold herm
    show ∑ m, (star z') m * (Hpk k r *ᵥ bvec q) m = 0
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : r ≤ m.val ∧ m.val ≤ r + k
    · have h0 : (Hpk k r *ᵥ bvec q) m = 0 := by
        have e : (Hpk k r *ᵥ bvec q) m = Hpk k r m q := by
          simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
        rw [e]
        simp only [Hpk]
        rw [if_neg (fun hc => by omega), if_neg (fun hc => by omega),
          if_neg (fun hc => by rw [hc.2.2] at hm; omega)]
      rw [h0, mul_zero]
    · have h0 : z' m = 0 := hw m (by omega)
      simp [h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold InNp
    rw [heI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, bvec, Pi.single_apply, Fin.ext_iff, hv, hqv, dpsiP, heI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xv, hf, dpsiP, heI, hqv]
      split_ifs <;> first
        | rfl
        | (exfalso; omega)
        | exact hw _ (by rw [hqv]; omega)
        | exact (hw _ (by rw [hqv]; omega)).symm
  · unfold InNp
    rw [hesI, hqv]
    omega
  · by_cases hlr : l.val + 1 < r
    · have hf : fvec k r z' l.succ = bvec (eI k r ⟨l.val + 1, hlr⟩) := by
        simp only [fvec, Fin.val_succ, dif_pos hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf, herm_bvec_bvec]
      have hv : (eI k r (⟨l.val + 1, hlr⟩ : Fin r)).val = l.val + 1 := rfl
      simp only [dpsiP, Hpk, Fin.ext_iff, hv, hqv, hesI]
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hf : fvec k r z' l.succ = z' := by
        simp only [fvec, Fin.val_succ, dif_neg hlr]
      simp only [Formalism.FourierDecayAlt.Q.xbv, hf]
      rw [dpsiP]
      split_ifs <;> first
        | rfl
        | (exfalso; rw [hqv, hesI] at *; omega)
        | exact hz _ (by rw [hqv]; omega)
        | (exfalso; omega)

theorem herm_unitary {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg']

theorem herm_bvec_eI {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  have h1 : herm (Hpk k r) v (bvec (eI k r b)) = ∑ p, Hpk k r (eI k r b) p * v p := by
    have hs : star (bvec (eI k r b)) = bvec (eI k r b) := by
      ext i
      by_cases h : i = eI k r b <;> simp [bvec, Pi.single_apply, h]
    unfold herm
    rw [hs]
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp_rw [hpk_row_eI]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp [esI]
  · intro p _ hp
    rw [if_neg, zero_mul]
    intro h
    exact hp (Fin.ext (by simp [esI, h]))
  · simp

theorem xi_Y_zhat_identity : XiYZhat := by
  intro k r z z' g a b hg
  have hf : ∀ (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r), fvec k r w c.castSucc = bvec (eI k r c) := by
    intro w c
    simp [fvec, c.isLt]
  have hZ : Zhat k r z z' g a.castSucc b.castSucc =
      herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
    simp only [Zhat, hf]
  refine ⟨hZ.symm, ?_⟩
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hdet : IsUnit g.det := by
    have h1 : (Hpk k r).det * (Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, hHH, Matrix.det_one]
    have h2 := congrArg Matrix.det hg'
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at h1
    exact zero_ne_one h1
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hsym : ∀ v w, star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
    intro v w
    unfold herm
    first
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]; done)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec];
        exact Matrix.dotProduct_comm _ _)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec];
        exact (Matrix.dotProduct_comm _ _).symm)
    | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_comm,
        Matrix.dotProduct_mulVec]; done)
    | (simp [Matrix.star_dotProduct, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]; done)
  calc (g⁻¹ *ᵥ bvec (eI k r a)) (esI k r b)
      = herm (Hpk k r) (g⁻¹ *ᵥ bvec (eI k r a)) (bvec (eI k r b)) := (herm_bvec_eI _ b).symm
    _ = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ bvec (eI k r a))) (g *ᵥ bvec (eI k r b)) :=
        (herm_unitary g hg _ _).symm
    _ = herm (Hpk k r) (bvec (eI k r a)) (g *ᵥ bvec (eI k r b)) := by
        rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
    _ = star (herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a))) := (hsym _ _).symm
    _ = star (Zhat k r z z' g a.castSucc b.castSucc) := by rw [hZ]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section utinv

open Formalism.FourierDecayAlt.P.Dx2.SplitM

def eQ (j : ℕ) : ((G.UT j → ℂ) × (Fin j → ℂ)) ≃ᵐ (G.UT (j + 1) → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : G.UT j ⊕ Fin j => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : G.UT (j + 1) => ℂ) eL)

theorem eQ_eq (j : ℕ) (p : (G.UT j → ℂ) × (Fin j → ℂ)) : eQ j p = combineUpperTriangularCoords p := rfl

theorem eQ_mp (j : ℕ) : MeasurePreserving (eQ j) volume volume := combined_coordinates_measure_preserving

theorem upper_eQ_cc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a b : Fin j) :
    G.upper (eQ j p) a.castSucc b.castSucc = G.upper p.1 a b := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj,
    Fin.castSucc_lt_castSucc_iff]
  congr 1
  split_ifs with h
  · have e : (⟨(a.castSucc, b.castSucc), Fin.castSucc_lt_castSucc_iff.mpr h⟩ : G.UT (j + 1)) = eL (Sum.inl ⟨(a, b), h⟩) := rfl
    rw [e, eQ_eq, combined_coordinates_left]
  · rfl

theorem upper_eQ_cl {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a : Fin j) :
    G.upper (eQ j p) a.castSucc (Fin.last j) = p.2 a := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Fin.castSucc_ne_last a), dif_pos (Fin.castSucc_lt_last a), zero_add]
  have e : (⟨(a.castSucc, Fin.last j), Fin.castSucc_lt_last a⟩ : G.UT (j + 1)) = eL (Sum.inr a) := rfl
  rw [e, eQ_eq, combineUpperTriangular_inr]

theorem upper_eQ_lc {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) (b : Fin j) :
    G.upper (eQ j p) (Fin.last j) b.castSucc = 0 := by
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  rw [if_neg (Ne.symm (Fin.castSucc_ne_last b)), dif_neg (not_lt.2 (Fin.castSucc_lt_last b).le), zero_add]

theorem upper_eQ_ll {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    G.upper (eQ j p) (Fin.last j) (Fin.last j) = 1 := by
  simp [G.upper, G.strictUpper]

def utInv (m : ℕ) (u : G.UT m → ℂ) : G.UT m → ℂ := StabilizerDisintegration.utc (G.upper u)⁻¹

theorem upper_inv_mem {m : ℕ} (u : G.UT m → ℂ) : (G.upper u)⁻¹ ∈ C2.UTset m :=
  Formalism.FourierDecayAlt.P.C2x2.ut_inv (StabilizerDisintegration.UC.upper_mem u)

theorem upper_utInv {m : ℕ} (u : G.UT m → ℂ) : G.upper (utInv m u) = (G.upper u)⁻¹ :=
  StabilizerDisintegration.UC.upper_utc (upper_inv_mem u)

theorem utInv_eQ {j : ℕ} (p : (G.UT j → ℂ) × (Fin j → ℂ)) :
    utInv (j + 1) (eQ j p) = eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
  have hu1 : IsUnit (G.upper p.1).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
  have hprod : G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) * G.upper (eQ j p) = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
    · simp [upper_eQ_lc, upper_eQ_ll]
    · simp [upper_eQ_lc, upper_eQ_ll, Matrix.one_apply]
      exact (Fin.castSucc_ne_last _).symm
    · simp only [upper_eQ_cc, upper_eQ_cl, upper_eQ_ll, mul_one, Matrix.one_apply, Fin.castSucc_ne_last, if_false,
        upper_utInv]
      have : ∑ x : Fin j, (G.upper p.1)⁻¹ a x * p.2 x = ((G.upper p.1)⁻¹ *ᵥ p.2) a := rfl
      rw [this]; simp
    · simp only [upper_eQ_cc, upper_eQ_lc, mul_zero, add_zero, upper_utInv, Matrix.one_apply,
        Fin.castSucc_inj]
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu1, Matrix.one_apply]
  have hinv : (G.upper (eQ j p))⁻¹ = G.upper (eQ j (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) :=
    Matrix.inv_eq_left_inv hprod
  unfold utInv
  rw [hinv, StabilizerDisintegration.UC.utc_upper]
  rfl

theorem utInv_mp : ∀ m : ℕ, MeasurePreserving (utInv m) volume volume
  | 0 => by
    have : IsEmpty (G.UT 0) := ⟨fun ⟨⟨a, _⟩, _⟩ => a.elim0⟩
    have : utInv 0 = id := funext fun u => funext fun q => isEmptyElim q
    rw [this]; exact MeasurePreserving.id _
  | j + 1 => by
    have ih := utInv_mp j
    have hA : ∀ u1 : G.UT j → ℂ, ‖(-(G.upper u1)⁻¹).det‖ = 1 := by
      intro u1
      have hu := upper_inv_mem u1
      rw [Matrix.det_neg, StabilizerDisintegration.UC.det_UT hu, mul_one]
      simp
    have hg : MeasurePreserving (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2)))
        volume volume := by
      rw [Measure.volume_eq_prod]
      refine MeasurePreserving.skew_product (f := utInv j) (g := fun u1 v => -((G.upper u1)⁻¹ *ᵥ v)) ih ?_ ?_
      · have hc : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => -((G.upper p.1)⁻¹ *ᵥ p.2)) := by
          have h1 : Continuous (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) := by
            have : (fun p : (G.UT j → ℂ) × (Fin j → ℂ) => (G.upper p.1)⁻¹) =
                fun p => (G.upper p.1).adjugate := by
              funext p
              rw [Matrix.inv_def, StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; simp
            rw [this]
            exact (StabilizerDisintegration.UC.cont_upper.comp continuous_fst).matrix_adjugate
          exact (h1.matrix_mulVec continuous_snd).neg
        exact hc.measurable
      · refine Filter.Eventually.of_forall fun u1 => ?_
        have h := mp_vec (-(G.upper u1)⁻¹) (hA u1)
        have e : (fun v : Fin j → ℂ => -((G.upper u1)⁻¹ *ᵥ v)) = fun v => (-(G.upper u1)⁻¹) *ᵥ v := by
          funext v; rw [Matrix.neg_mulVec]
        rw [e]; exact h.map_eq
    have e : utInv (j + 1) = eQ j ∘ (fun p : (G.UT j → ℂ) × (Fin j → ℂ) =>
        (utInv j p.1, -((G.upper p.1)⁻¹ *ᵥ p.2))) ∘ (eQ j).symm := by
      funext u
      obtain ⟨p, rfl⟩ := (eQ j).surjective u
      simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
      exact utInv_eQ p
    rw [e]
    exact (eQ_mp j).comp (hg.comp (eQ_mp j).symm)

end utinv

section rad

variable {k j ρ : ℕ}

theorem strictUpper_neg {d : ℕ} (v : G.UT d → ℂ) : G.strictUpper (-v) = -G.strictUpper v := by
  ext i j
  simp only [G.strictUpper, Matrix.of_apply, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem skewOf_neg (q : (G.UT j → ℂ) × (Fin j → ℝ)) : U.skewOf (-q) = -U.skewOf q := by
  simp only [U.skewOf, Prod.fst_neg, Prod.snd_neg, strictUpper_neg, Matrix.conjTranspose_neg]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply]
  split_ifs <;> push_cast <;> ring

theorem rn_mul_neg (x : U.RC k j ρ) : U.Rn k j ρ x * U.Rn k j ρ (-x) = 1 := by
  unfold U.Rn
  rw [Ux3.block3_mul, ← Ux3.block3_one]
  have hc : (Matrix.of (-x).1 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = -Matrix.of x.1 := rfl
  have hs : U.skewOf (-x).2 = -U.skewOf x.2 := skewOf_neg x.2
  rw [hc, hs]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_add_cancel, add_neg_cancel]

  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg, Matrix.mul_assoc]
  module

theorem rn_inv (x : U.RC k j ρ) : (U.Rn k j ρ x)⁻¹ = U.Rn k j ρ (-x) := Matrix.inv_eq_right_inv (rn_mul_neg x)

theorem negRC_mp : MeasurePreserving (fun x : U.RC k j ρ => -x) (U.muRC k j ρ) (U.muRC k j ρ) := by
  have h1 : MeasurePreserving (fun c : Fin (2 * ρ + k + 1) → Fin j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume))
  have h2 : MeasurePreserving (fun c : G.UT j → ℂ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  have h3 : MeasurePreserving (fun c : Fin j → ℝ => -c) volume volume :=
    volume_preserving_pi (fun _ => Measure.measurePreserving_neg volume)
  unfold U.muRC
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  exact h1.prod (h2.prod h3)

theorem muP_one : U.muP k j ρ (1 : Matrix (Fin j) (Fin j) ℂ) = 1 := by
  unfold U.muP
  rw [Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Ux3.wMat_mul_self, Ux3.block3_one]

theorem leviElement_inv (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) : (U.muP k j ρ q)⁻¹ = U.muP k j ρ q⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Dx2.Split.leviElement_mul, Matrix.mul_nonsing_inv _ hq, muP_one]

end rad

section split

variable {k : ℕ}

theorem embG_one {j ρ : ℕ} : U.embG k j ρ (1 : B.Mat k ρ) = 1 := by
  unfold U.embG; exact Ux3.block3_one

def psiF (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))

def psiR (k j : ℕ) (p : U.RC k j 0 × (G.UT j → ℂ)) : Mt k (j + 0) := Matrix.of.symm (U.muP k j 0 (G.upper p.2) * U.Rn k j 0 p.1)

theorem psiF_cont (j : ℕ) : Continuous (psiF k j) := by
  unfold psiF
  exact ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst).matrix_mul
    ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd)

theorem psiR_cont (j : ℕ) : Continuous (psiR k j) := by
  unfold psiR
  exact ((Dx2.SplitF.mup_cont (k := k) j 0).comp continuous_snd).matrix_mul
    ((Dx2.SplitF.rn_cont (k := k) j 0).comp continuous_fst)

theorem psiF_meas (j : ℕ) : Measurable (psiF k j) := by
  exact (psiF_cont j).measurable

theorem psiR_meas (j : ℕ) : Measurable (psiR k j) := by
  exact (psiR_cont j).measurable

theorem muN_fwd (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiF k j) := by
  have hs := Dx2.SplitF.split_all (k := k) j 0
  have h0 : D.muN k 0 = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := rfl
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  rw [hs, h0, Measure.prod_dirac]
  have hm : Measurable (fun u : G.UT j → ℂ => (u, Matrix.of.symm (1 : B.Mat k 0))) :=
    measurable_id.prodMk measurable_const
  conv_lhs => rw [← Measure.map_id (μ := U.muRC k j 0)]
  rw [Measure.map_prod_map _ _ measurable_id hm,
    Measure.map_map (Dx2.SplitF.psi_meas j 0) (measurable_id.prodMap hm)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map, id, Dx2.SplitF.Psi, psiF]
  rw [show Matrix.of (Matrix.of.symm (1 : B.Mat k 0)) = (1 : B.Mat k 0) from rfl, embG_one, Matrix.mul_one]

theorem muN_rev (j : ℕ) : D.muN k (j + 0) = ((U.muRC k j 0).prod (volume : Measure (G.UT j → ℂ))).map (psiR k j) := by
  have : SigmaFinite (U.muRC k j 0) := Dx2.SplitF.sf_RC j 0
  have hinv := Formalism.FourierDecayAlt.P.haar_measure_inversion k (j + 0) (Nset k (j + 0)) (D.muN k (j + 0))
    (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (j + 0)) (Dx2.MN.haar (k := k) (j + 0))
  rw [← hinv, muN_fwd j, Measure.map_map (Formalism.FourierDecayAlt.P.TwoByOneBlock.invM_meas) (psiF_meas j)]
  have hmp : MeasurePreserving (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2))
      ((U.muRC k j 0).prod volume) ((U.muRC k j 0).prod volume) :=
    negRC_mp.prod (utInv_mp j)
  have e : (B2.invM ∘ psiF k j) = psiR k j ∘ (fun p : U.RC k j 0 × (G.UT j → ℂ) => (-p.1, utInv j p.2)) := by
    funext p
    have hu : IsUnit (G.upper p.2).det := by rw [StabilizerDisintegration.UC.det_UT (StabilizerDisintegration.UC.upper_mem _)]; exact isUnit_one
    show Matrix.of.symm ((Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))))⁻¹) =
      Matrix.of.symm (U.muP k j 0 (G.upper (utInv j p.2)) * U.Rn k j 0 (-p.1))
    rw [show Matrix.of (Matrix.of.symm (U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2))) =
      U.Rn k j 0 p.1 * U.muP k j 0 (G.upper p.2) from rfl, Matrix.mul_inv_rev, rn_inv, leviElement_inv _ hu, upper_utInv]
  rw [e, ← Measure.map_map (psiR_meas j) hmp.measurable, hmp.map_eq]

end split

end Formalism.FourierDecayAlt.P.PBM
end
end

