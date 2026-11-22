import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0261
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0264
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmLongContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0260
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesOnPbT

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
section
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section hpart

variable {k r j : ℕ}

theorem hpk_row_eI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (eI k r c) l = if l = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_eI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (eI k r c) x * Hpk k r = Matrix.single p (esI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
  · rw [hpk_row_eI]
    by_cases hi : i = p <;> by_cases hl : l = esI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hpart1_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  rfl

theorem hpart2_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  rfl

theorem nN_smul_real (hj : j + 1 ≤ r) (a : Fin j → ℂ) (t : ℝ) :
    nN k r j hj (fun c => (t : ℂ) * a c) = (t : ℂ) • nN k r j hj a := by
  unfold nN
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_sub, smul_smul, smul_smul, map_mul, Complex.conj_ofReal]

theorem ell_nL (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a : Fin j → ℂ) :
    ell k r z (nL k r j hj a) = -conj (a ⟨j - 1, by omega⟩) := by
  unfold ell
  rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin r)]
  · rw [dif_pos (show j - 1 + 1 < r by omega), SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]),
      zero_add, Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin j)]
    · have e2 : eI k r ⟨j - 1 + 1, by omega⟩ = eI k r ⟨j, by omega⟩ := by ext; simp [eI]; omega
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, e2]
      rw [show (eI k r ⟨((⟨j - 1, by omega⟩ : Fin j) : ℕ), by omega⟩ : Fin (2 * r + k + 1)) = eI k r ⟨j - 1, by omega⟩
        from rfl, Matrix.single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub,
        Matrix.single_apply_of_row_ne, mul_zero, neg_zero]
      intro h
      apply hb
      have := congrArg Fin.val h
      simp only [eI] at this
      exact Fin.ext this
    · simp
  · intro a' _ ha'
    have hne : a'.val ≠ j - 1 := fun h => ha' (Fin.ext h)
    split_ifs with h
    · rw [SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]), zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
      rw [if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      omega
    · have hrow : ∀ q, nL k r j hj a (eI k r a') q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a') q := by
        intro q
        rw [SingleEntryHermitianProducts.nL_apply, Finset.sum_eq_zero, add_zero]
        intro b _
        rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
        rw [if_neg, mul_zero, neg_zero]
        rintro ⟨h1, _⟩
        have e1 := congrArg Fin.val h1
        simp only [eI] at e1
        have := b.isLt
        omega
      rw [Matrix.mulVec, dotProduct]
      simp_rw [hrow]
      rw [← dotProduct, ← Matrix.mulVec, Matrix.one_mulVec, hz _ (Or.inl (by simp [eI]))]
  · simp

end hpart

section deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r j : ℕ}

theorem hpk_row_esI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (esI k r c) l = if l = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_esI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (esI k r c) x * Hpk k r = Matrix.single p (eI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r c)]
  · rw [hpk_row_esI]
    by_cases hi : i = p <;> by_cases hl : l = eI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hM_lie (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) :
    (hM k r j hj x y s)ᴴ * Hpk k r + Hpk k r * hM k r j hj x y s = 0 := by
  unfold hM
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
    SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, single_mul_hpk_eI,
    single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI]
  abel

theorem psi_nL_hasDeriv (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : Fin j → ℂ) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)))
      (a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩)) 0 := by
  set R : ℝ := (cStd * -conj (a ⟨j - 1, by omega⟩)).re with hR
  have hfun : (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c))) =
      fun t : ℝ => Complex.exp (Complex.I * (((t * R : ℝ)) : ℂ)) := by
    funext t
    unfold psi
    rw [ell_nL hj hj1 z hz]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, hR]
    rw [show cStd * -((t : ℂ) * conj (a ⟨j - 1, by omega⟩)) = (t : ℂ) * (cStd * -conj (a ⟨j - 1, by omega⟩)) by ring,
      Complex.re_ofReal_mul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => ((t * R : ℝ) : ℂ)) ((R : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const R).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).cexp
  have hval : Complex.I * ((R : ℝ) : ℂ) = a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩) := by
    apply Complex.ext <;> simp [hR, cStd, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  rw [← hval]
  simpa using h2

theorem rdV_hM (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (hj1 : 1 ≤ j) (hz : inWb k r z) (hS : Q.SmoothLev k r 0 Dm Ψ) (hZ : Z.det ≠ 0)
    (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) (hx : x0 k r j hj Z τ γ ∈ Dm)
    (hEq : ∀ a : Fin j → ℂ,
      Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ))
    (b : Fin j) (s : ℂ) :
    RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ (x0 k r j hj Z τ γ) =
      (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩ - conj (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩)) • Ψ (x0 k r j hj Z τ γ) := by
  set x₁ := x0 k r j hj Z τ γ with hx₁
  have hxG : x₁ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS x₁ ⟨hxG, hx⟩
  have hd : DifferentiableAt ℝ F x₁ := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  set a : Fin j → ℂ := fun c => s * τ * Z⁻¹ b c with ha
  have hrd : RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ x₁ =
      fderiv ℝ F x₁ (x₁ * hM k r j hj (Fin.last j) b.castSucc s) :=
    (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hxU hxG ⟨hM_lie hj _ _ s, fun a ha => absurd ha (Nat.not_lt_zero _)⟩ hd
      hFU).deriv
  rw [hrd, hx₁, level_point_conj_unipotent hj hZ hτ γ b s, ← hx₁]
  have hc : HasDerivAt (fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) (nN k r j hj a * x₁) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (h0.smul_const (nN k r j hj a * x₁)).const_add x₁
    rw [one_smul] at this
    exact this
  have hcF := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hcurve : ∀ t : ℝ, x₁ + (t : ℂ) • (nN k r j hj a * x₁) = nL k r j hj (fun c => (t : ℂ) * a c) * x₁ := by
    intro t
    rw [nL_eq, nN_smul_real, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hev : (F ∘ fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) =ᶠ[𝓝 0]
      fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)) • Ψ x₁ := by
    have hUn : U ∈ 𝓝 (x₁ + ((0 : ℝ) : ℂ) • (nN k r j hj a * x₁)) := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hU.mem_nhds hxU
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ U :=
      hc.continuousAt.preimage_mem_nhds hUn
    filter_upwards [hmem] with t ht
    have hG : x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ Q.Glev k r 0 := by
      rw [hcurve t]; exact Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj _) hxG
    simp only [Function.comp]
    rw [← hFU _ ht hG, hcurve t, hEq]
  have h2 := (psi_nL_hasDeriv hj hj1 z hz a).smul_const (Ψ x₁)
  exact (hcF.congr_of_eventuallyEq hev.symm).unique h2

theorem left_rule_level_point : CutHL.LeftActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single hj b, hpart2_single hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end deriv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe
section
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem qU_pos : 0 < qU := by
  unfold qU
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  have hc : 0 < ‖U.betaU‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
  exact_mod_cast Real.toNNReal_pos.2 hc

theorem qU_coe (N : ℕ) : (((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ N : NNReal) : ℝ) : ℂ) = ((qU ^ N : ℝ) : ℂ) := by
  unfold qU; push_cast; rfl

theorem exists_hMat_n (a : C.LPt) (ha : ∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) (n : ℕ) (hn : D.ptSize a = n) :
    ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
  subst hn
  obtain ⟨σ, d, -, hM⟩ := PBJ.Asm.exists_hMat a ha
  exact ⟨σ, d, hM⟩

section vec

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem vec_om {n : ℕ} (vec : C.LPt → V) (Φ0 : G.Mat n → V) (hΦ0 : PBJ.KCls Φ0)
    (hV : ∀ (a : C.LPt) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt a n → U.hMat σ d = D.ptMatN a n →
      vec a = U.PhiTop (p := n) (s := 0) U.betaU σ d Φ0 fun x => x.elim0)
    (H : C.LPt) (hH : ∀ b ∈ H, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hn : D.ptSize H + (m + 1 + 1) = n) :
    ∃ (σh : Equiv.Perm (Fin (D.ptSize H))) (dh : Fin (D.ptSize H) → ℂ) (Ψ0 : G.Mat (D.ptSize H + (m + 1 + 1)) → V),
      (∀ i, dh i ≠ 0) ∧ PBJ.KCls Ψ0 ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → vec (H ++ [(m + 1, t), (1, c)]) =
        (((qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))))⁻¹ : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) t c) ∧
      (∀ z : ℂ, z ≠ 0 → vec (H ++ [(m + 1 + 1, z)]) =
        (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) z) := by
  subst hn
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  obtain ⟨σh, dh, hdh, hMh⟩ := PBJ.Asm.exists_hMat H hH
  refine ⟨σh, dh, Φ0, hdh, hΦ0, ?_, ?_⟩
  · intro t c ht hc
    set a := H ++ [(m + 1, t), (1, c)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact ⟨by omega, ht⟩
          · exact ⟨le_rfl, hc⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hdb : ∀ i, PBJ.Om.dB (m + 1) t c i ≠ 0 := by
      intro i
      induction i using Fin.addCases with
      | left j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_left]; exact ht
      | right j => simp only [PBJ.Om.dB, PBJ.Fub.dQ, Fin.addCases_right]; exact hc
    have e1 := PBJ.Asm.ptMatN_append H [(m + 1, t), (1, c)]
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat (PBJ.Om.σB (m + 1)) (PBJ.Om.dB (m + 1) t c)) := by
      rw [hM, hMh, PBJ.Om.hMat_block, ← PBJ.Asm.ptMatN_block]; exact e1
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh (PBJ.Om.σB (m + 1))
      (PBJ.Om.dB (m + 1) t c) V Φ0 hdh hdb hM' hΦ0]
    rw [PBJ.Om.omBlock_eq U.betaU (m + 1) t c, qU_coe, smul_smul, Fintype.card_fin]
    have hq : (qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]
    rfl
  · intro z hz
    set a := H ++ [(m + 1 + 1, z)] with ha
    have hloc : D.IsLocPt a (D.ptSize H + (m + 1 + 1)) := by
      refine ⟨fun b hb => ?_, ?_⟩
      · rcases List.mem_append.1 hb with hb | hb
        · exact hH b hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl
          exact ⟨by omega, hz⟩
      · rw [ha, PBJ.Asm.ptSize_append]; simp [D.ptSize]
    obtain ⟨σ, d, hM⟩ := exists_hMat_n a hloc.1 _ hloc.2
    have hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1 + 1))) (fun _ => z) =
        D.ptMatN [(m + 1 + 1, z)] (D.ptSize [(m + 1 + 1, z)]) := by
      rw [PBJ.Asm.hMat_rev]; exact (PBJ.Asm.ptMatN_long (m + 1 + 1) z).symm
    have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => z)) := by
      rw [hM, hMh, hMb]; exact PBJ.Asm.ptMatN_append H [(m + 1 + 1, z)]
    rw [hV a σ d hloc hM, PBJ.fubini_head_last_part U.betaU (D.ptSize H) (m + 1 + 1) σ d σh dh Fin.revPerm (fun _ => z) V Φ0
      hdh (fun _ => hz) hM' hΦ0]
    rw [PBJ.Om.omLong_eq U.betaU (m + 1) z, qU_coe, smul_smul]
    have hq : (qU ^ Fintype.card (G.UT (m + 1 + 1)) : ℝ) ≠ 0 := pow_ne_zero _ qU_pos.ne'
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hq, Complex.ofReal_one, one_smul]

end vec

section rho

theorem one_sub_pow_le (u : ℝ) (hu0 : 0 ≤ u) (n : ℕ) : 1 - u ^ n ≤ n * (1 - u) := by
  have := one_add_mul_le_pow (a := u - 1) (by linarith) n
  simp only [add_sub_cancel] at this
  linarith

theorem rho_fac (δ : ℝ) (hδ : 0 < δ) (k N : ℕ) (u : ℝ) (hu1 : δ ≤ u) (hu2 : u ≤ 1) :
    |√(u ^ k) * √((u⁻¹) ^ N)| ≤ √((δ⁻¹) ^ N) ∧
      |√(u ^ k) * √((u⁻¹) ^ N) - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
  have hu0 : 0 < u := lt_of_lt_of_le hδ hu1
  have hk0 : 0 ≤ u ^ k := pow_nonneg hu0.le k
  have hk1 : u ^ k ≤ 1 := pow_le_one₀ hu0.le hu2
  have hi1 : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.2 hu2
  have hiδ : u⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hu1
  have hN1 : 1 ≤ (u⁻¹) ^ N := one_le_pow₀ hi1
  have hNδ : (u⁻¹) ^ N ≤ (δ⁻¹) ^ N := pow_le_pow_left₀ (by positivity) hiδ N
  set f := √(u ^ k) * √((u⁻¹) ^ N) with hf
  have hf0 : 0 ≤ f := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hf2 : f ^ 2 = u ^ k * (u⁻¹) ^ N := by
    rw [hf, mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg hf0, hf]
    calc √(u ^ k) * √((u⁻¹) ^ N) ≤ 1 * √((δ⁻¹) ^ N) := by
          refine mul_le_mul ?_ (Real.sqrt_le_sqrt hNδ) (Real.sqrt_nonneg _) zero_le_one
          rw [Real.sqrt_le_one]; exact hk1
      _ = √((δ⁻¹) ^ N) := one_mul _
  ·
    have h1 : |f - 1| ≤ |f ^ 2 - 1| := by
      have : f ^ 2 - 1 = (f - 1) * (f + 1) := by ring
      rw [this, abs_mul]
      have : 1 ≤ |f + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_nonneg (f - 1)]
    have hA : 1 - u ^ k ≤ k * (1 - u) := one_sub_pow_le u hu0.le k
    have hB : (u⁻¹) ^ N - 1 ≤ N * (δ⁻¹) ^ N * (1 - u) := by
      have e : (u⁻¹) ^ N - 1 = (u⁻¹) ^ N * (1 - u ^ N) := by
        rw [mul_sub, mul_one, ← mul_pow, inv_mul_cancel₀ hu0.ne', one_pow]
      rw [e]
      have hC := one_sub_pow_le u hu0.le N
      have h0 : 0 ≤ 1 - u ^ N := by linarith [pow_le_one₀ (n := N) hu0.le hu2]
      calc (u⁻¹) ^ N * (1 - u ^ N) ≤ (δ⁻¹) ^ N * (N * (1 - u)) :=
            mul_le_mul hNδ hC h0 (by positivity)
        _ = N * (δ⁻¹) ^ N * (1 - u) := by ring
    have h2 : |f ^ 2 - 1| ≤ (k + N * (δ⁻¹) ^ N) * (1 - u) := by
      rw [hf2]
      have e : u ^ k * (u⁻¹) ^ N - 1 = u ^ k * ((u⁻¹) ^ N - 1) - (1 - u ^ k) := by ring
      rw [e]
      have ha : 0 ≤ u ^ k * ((u⁻¹) ^ N - 1) := mul_nonneg hk0 (by linarith)
      have hb : u ^ k * ((u⁻¹) ^ N - 1) ≤ N * (δ⁻¹) ^ N * (1 - u) :=
        le_trans (mul_le_of_le_one_left (by linarith) hk1) hB
      rw [abs_le]; constructor <;> nlinarith
    linarith

theorem rho_bound (TT ε0 dH0 MK mK : ℝ) (hTT : 0 < TT) (hε0 : 0 < ε0) (hdH0 : 0 ≤ dH0) (hmK : 0 < mK)
    (k N m : ℕ) (l1 x y c : ℂ) (hl1 : l1 ≠ 0) (hx : x ≠ 0) (hy0 : y ≠ 0) (hc0 : c ≠ 0) (hyM : ‖y‖ ≤ MK)
    (hym : mK ≤ ‖y‖) (hnc : Complex.normSq c = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2)
    (hA : ε0 ≤ dH0 * ‖l1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq c - TT)) :
    |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N)| ≤
        √(((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) ∧
      |√((Complex.normSq c - TT) ^ k) / ‖c‖ ^ k * √((Complex.normSq c / (Complex.normSq c - TT)) ^ N) - 1| ≤
        ((k : ℝ) + N * ((ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2))⁻¹) ^ N) *
          (TT / mK ^ 2) * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
  set n := 2 * (m + 1) with hn
  set δ := ε0 / (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) with hδ
  set GG := Complex.normSq c - TT with hGG
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hl1pos : 0 < ‖l1‖ := norm_pos_iff.2 hl1
  have hncpos : 0 < Complex.normSq c := by rw [hnc]; positivity
  have hnt : ‖l1 * x⁻¹‖ ^ n = ‖l1‖ ^ n * (‖x‖ ^ n)⁻¹ := by
    rw [norm_mul, norm_inv, mul_pow, inv_pow]
  rw [hnt] at hA
  have hGGpos : 0 < GG := by
    by_contra hle
    have : dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hle)
    linarith
  set u := GG / Complex.normSq c with hu
  have hu0 : 0 ≤ u := div_nonneg hGGpos.le hncpos.le
  have huy : u * ‖y‖ ^ 2 = GG * (‖x‖ ^ n)⁻¹ := by
    rw [hu, hnc]; field_simp
  have hu1 : δ ≤ u := by
    have hden : 0 < max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2 := by positivity
    rw [hδ, div_le_iff₀ hden]
    have hyM' : ‖y‖ ^ 2 ≤ (max MK 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hyM.trans (le_max_left _ _)) 2
    calc ε0 ≤ dH0 * (‖l1‖ ^ n * (‖x‖ ^ n)⁻¹) * GG := hA
      _ = dH0 * ‖l1‖ ^ n * (u * ‖y‖ ^ 2) := by rw [huy]; ring
      _ ≤ max dH0 1 * ‖l1‖ ^ n * (u * (max MK 1) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (mul_le_mul_of_nonneg_left hyM' hu0) (by positivity) (by positivity)
      _ = u * (max dH0 1 * ‖l1‖ ^ n * (max MK 1) ^ 2) := by ring
  have hu2 : u ≤ 1 := by
    rw [hu, div_le_one hncpos, hGG]; linarith
  have h1u : 1 - u ≤ TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by
    have e : 1 - u = TT / Complex.normSq c := by
      rw [hu, hGG]; field_simp; ring
    rw [e, hnc]
    have hmy : mK ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hmK.le hym 2
    calc TT / (‖x‖ ^ n * ‖y‖ ^ 2) ≤ TT / (‖x‖ ^ n * mK ^ 2) :=
          div_le_div_of_nonneg_left hTT.le (by positivity) (mul_le_mul_of_nonneg_left hmy (by positivity))
      _ = TT / mK ^ 2 * (‖x‖ ^ n)⁻¹ := by field_simp
  have hρu : √(GG ^ k) / ‖c‖ ^ k * √((Complex.normSq c / GG) ^ N) = √(u ^ k) * √((u⁻¹) ^ N) := by
    have hinv : Complex.normSq c / GG = u⁻¹ := by rw [hu, inv_div]
    rw [hinv]
    congr 1
    have hcn : ‖c‖ ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hGu : GG = u * ‖c‖ ^ 2 := by rw [hcn, hu, div_mul_cancel₀ _ hncpos.ne']
    rw [hGu, mul_pow, Real.sqrt_mul (pow_nonneg hu0 _), ← pow_mul, mul_comm 2, pow_mul,
      Real.sqrt_sq (pow_nonneg (norm_nonneg _) _)]
    have : ‖c‖ ^ k ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc0)
    field_simp
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨hb1, hb2⟩ := rho_fac δ hδpos k N u hu1 hu2
  rw [hρu]
  refine ⟨hb1, hb2.trans ?_⟩
  rw [mul_assoc, inv_pow ‖x‖ n]
  exact mul_le_mul_of_nonneg_left h1u (by positivity)

end rho

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesEq
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem rules_eq : CutHB.RulesEq := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj _hF
  refine ⟨fun g hg m hm => ⟨minorDomain_mul_unipotent p.T.base j hg.2 hm, ?_⟩,
    fun g hg a => ⟨domP_N_mul p.T.base j hg.2 (nL_mem hj a), ?_⟩⟩
  · exact pbF_right _ _ _ F g m hm
  · show pbF (p.T.bs j) p.T.base _ F (LevelPointCoordinates.nL P.k P.r j hj a * g) =
      psi P.k P.r p.T.base.z cStd (LevelPointCoordinates.nL P.k P.r j hj a) • pbF (p.T.bs j) p.T.base _ F g
    rw [nL_castM hj a, pbF_left_rn p.T.base _ (p.T.bs j).z_mem F (cL a, 0) g,
      psi_castM _ (p.T.bs j).z p.T.base.z (p.T.z_lev j (by omega))]

end Formalism.FourierDecayAlt.P
end
end

