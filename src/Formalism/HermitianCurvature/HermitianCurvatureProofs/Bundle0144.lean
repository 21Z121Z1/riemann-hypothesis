import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0020
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OoConvOf
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_Y_eq (hNI : NormInv) {P Q γ : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    B.gN (Q * γ⁻¹ * P⁻¹) = B.gN (P * γ * Q⁻¹) := by
  set H := Formalism.QuantumDeterminants.Hpk k r with hHdef
  have hU : ∀ g ∈ Formalism.QuantumDeterminants.UH H, IsUnit g.det := by
    intro g hg
    have h1 : gᴴ * H * g = H := hg
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH : IsUnit H.det := Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r
    have h3 : (gᴴ).det * g.det = 1 := by
      apply hH.mul_left_cancel
      calc H.det * ((gᴴ).det * g.det) = (gᴴ).det * H.det * g.det := by ring
        _ = H.det := h2
        _ = H.det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)
  have hmem_mul : ∀ a ∈ Formalism.QuantumDeterminants.UH H, ∀ b ∈ Formalism.QuantumDeterminants.UH H, a * b ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha b hb
    have ha' : aᴴ * H * a = H := ha
    have hb' : bᴴ * H * b = H := hb
    show (a * b)ᴴ * H * (a * b) = H
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
      _ = H := by rw [ha', hb']
  have hmem_inv : ∀ a ∈ Formalism.QuantumDeterminants.UH H, a⁻¹ ∈ Formalism.QuantumDeterminants.UH H := by
    intro a ha
    have hd := hU a ha
    have ha' : aᴴ * H * a = H := ha
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hx : Q * γ⁻¹ * P⁻¹ ∈ Formalism.QuantumDeterminants.UH H :=
    hmem_mul _ (hmem_mul _ hQ _ (hmem_inv _ hγ)) _ (hmem_inv _ hP)
  have hxinv : (Q * γ⁻¹ * P⁻¹)⁻¹ = P * γ * Q⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hU _ hγ),
      Matrix.nonsing_inv_nonsing_inv _ (hU _ hP), mul_assoc]
  rw [← ((hNI k r).2 _ hx).1, hxinv]

set_option maxHeartbeats 1000000 in
theorem ooConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGG : GrowthG) (hDD : DecDD)
    (hBC : BeConv) : More.OOConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe' γ hγ
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, -, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1
  obtain ⟨hγi, hγγ, hγγ'⟩ := MatrixMultiplicationContinuity.uh_inv hγU
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hP1 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN
    D.μG νq hS1 l hbe w0 hw0DD
  have hP2 := phiReg_of hSch hNIs hGG hDD hBC hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN
    D.μG νq' hS2 l' hbe' w0 hw0DD
  have cont2' : ContinuousOn (fun g : Mx k r => l' (σ (γ⁻¹ * g) w0)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    hP2.1.comp (continuous_const.matrix_mul continuous_id).continuousOn (fun g hg => DDSmoothness.uh_mul hγi hg)
  have hop : ContinuousOn (fun g : Mx k r => (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))).smulRight (l (σ g w0)))
      (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
    have ha : ContinuousOn (fun g : Mx k r =>
        ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (l' (σ (γ⁻¹ * g) w0))))
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
      (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous.comp_continuousOn
        ((innerSL ℂ).continuous.comp_continuousOn cont2')
    exact (ha.clm_apply hP1.1).congr fun g _ => rfl
  have hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))) D.μG := by
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r =>
        (innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0)))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
      hop.comp mt_cont.continuousOn (fun x hx => hx)
    have := hc.aestronglyMeasurable (μ := D.μG) uh_mem_measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}) hGc] at this
  refine ⟨hmeas, ?_⟩
  show ∫⁻ x, ‖(innerSL ℂ (l' (σ (γ⁻¹ * Matrix.of x) w0))).smulRight (l (σ (Matrix.of x) w0))‖ₑ ∂D.μG < ⊤
  simp only [enorm_smulRight]
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA _ (dd_stable hds hx w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    have e : ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_]
      · simp
      filter_upwards [hGc] with x hx
      rw [hA' _ (dd_stable hds (DDSmoothness.uh_mul hγi hx) w0 hw0DD)]; simp
    rw [e]; exact ENNReal.zero_lt_top
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa := la_fin hNI D hThrb hb0.ne' hγ
  have hpt : ∀ᵐ x ∂D.μG, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤
      ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
        ((∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN)) *
          (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN))) := by
    filter_upwards [hGc] with x hx
    have hgx : γ⁻¹ * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hγi hx
    have b1 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hx
    have b2 := l_enorm_le (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hgx
    have i1 : ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x) w0⟫_ℂ‖ₑ ∂(D.μW.prod D.μN) =
        ∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂(D.μW.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW hN] with p hp
      rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hx)]
    have i2 : ∫⁻ q, ‖⟪v', σ (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x)) w0⟫_ℂ‖ₑ
        ∂(D.μW'.prod D.μN) =
        ∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γ⁻¹ * Matrix.of x))‖ₑ ∂(D.μW'.prod D.μN) := by
      apply lintegral_congr_ae
      filter_upwards [prod_ae hW' hN] with q hq
      rw [hee2 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hq.1.1 hq.2.1) hgx)]
    rw [i1] at b1; rw [i2] at b2
    calc ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ≤ _ * _ := mul_le_mul' b2 b1
      _ = _ := by ring
  have hinner : ∀ᵐ p ∂(D.μW.prod D.μN), ∀ᵐ q ∂(D.μW'.prod D.μN),
      ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ≤
        (ENNReal.ofReal (|C1| * |C2|) *
          ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
        ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
          (-(aOf r h - AG k r - 1))‖ₑ := by
    filter_upwards [prod_ae hW hN] with p hp
    filter_upwards [prod_ae hW' hN] with q hq
    have hPU : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hQU : Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hq.1.1 hq.2.1
    have hIB := inner_bound hNI D.haarG hGc he1 he2 hb1 hb2 hb0.le hba hPU hQU hγi
    have hY := gN_Y_eq hNI hPU hQU hγU
    have e : Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ =
        Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹ := by
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    unfold Phi3
    rw [hY, e] at hIB
    calc _ ≤ _ := hIB
      _ = _ := by ring
  have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
  calc ∫⁻ x, ‖l' (σ (γ⁻¹ * Matrix.of x) w0)‖ₑ * ‖l (σ (Matrix.of x) w0)‖ₑ ∂D.μG
      ≤ ∫⁻ x, ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γ⁻¹ x p q ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) ∂D.μG := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        rw [← triple_lintegral_product he1 he2 γ⁻¹]; exact hx
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, ∫⁻ x, Phi3 e1 e2 γ⁻¹ x p q ∂D.μG ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), triple_lintegral_swap he1 he2 γ⁻¹]
    _ ≤ ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ∫⁻ p, ∫⁻ q, (ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
            ‖B.gN (Matrix.of p.1 * Matrix.of p.2 * γ * (Matrix.of q.2)⁻¹ * (Matrix.of q.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) := by
        gcongr 1
        exact lintegral_mono_ae (hinner.mono fun p hp => lintegral_mono_ae hp)
    _ = ((‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) * (‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ)) *
          ((ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG) *
          ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^
              (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS) := by
        congr 1
        have hc0 : ENNReal.ofReal (|C1| * |C2|) *
            ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKg.ne
        simp_rw [lintegral_const_mul' _ _ hc0]
        rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) (ENNReal.mul_lt_top ?_ hLa)
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKg

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

theorem norm_psiG (g : ℝ) (l c : ℂ) : ‖psiG g l c‖ = 1 := by
  simp only [psiG]
  rw [Complex.norm_exp]
  simp

theorem continuous_psiG (g : ℝ) (l : ℂ) : Continuous (psiG g l) := by
  unfold psiG
  fun_prop

theorem psi_prod (g : ℝ) (hg : g ≠ 0) (σ z : crystallineComparison.V f) :
    crystallineComparison.psi (σ * z) = ∏ v, psiG g ((g • σ) v) (z v) := by
  have key : ∀ v, (2 * (((g • σ) v) * z v).re / g : ℝ) = 2 * (σ v * z v).re := by
    intro v
    rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
    field_simp
  simp only [psiG, key]
  rw [← Complex.exp_sum, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair, Complex.ofReal_sum,
    Finset.mul_sum]

theorem integrable_mul_psiG {φ : ℂ → ℂ} (hφ : Integrable φ) (g : ℝ) (l : ℂ) :
    Integrable fun c => φ c * psiG g l c := by
  refine hφ.norm.mono' (hφ.aestronglyMeasurable.mul (continuous_psiG g l).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun c => by rw [norm_mul, norm_psiG, mul_one]

theorem fourier_Nz (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : g ≠ 0) (dl : Fin f → ℝ)
    (hdl : ∀ v, dl v ≠ 0) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c) (σ : crystallineComparison.V f) :
    crystallineComparison.fourier (Nz Y κ D) σ = (∏ v, ((dl v : ℝ) : ℂ)) * Hh Y κ hat (g • σ) := by
  have hae : (fun z => ((Nz Y κ D z : ℝ) : ℂ) * crystallineComparison.psi (σ * z)) =ᵐ[volume]
      fun z => Fz Y κ D z * crystallineComparison.psi (σ * z) := by
    filter_upwards [ae_good] with z hz
    have h0 := Complex.nonneg_iff.mp (Fz_nonneg Y κ hκ D hD z hz)
    rw [Nz, if_pos hz]
    congr 1
    exact Complex.ext (by simp) (by simp [← h0.2])
  have hpt : ∀ z : crystallineComparison.V f, Fz Y κ D z * crystallineComparison.psi (σ * z) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v)) := by
    intro z
    rw [Fz, psi_prod g hg σ z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  have hone : ∀ v h h', ∫ c, D v h h' c * psiG g ((g • σ) v) c =
      ((dl v : ℝ) : ℂ) * hat v ((g • σ) v) h h' := by
    intro v h h'
    rw [hhat, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hdl v), one_mul]
  have hint : ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (fun z : crystallineComparison.V f =>
      κ h h' * ∏ v, (D v h h' (z v) * psiG g ((g • σ) v) (z v))) := by
    intro h hh h' hh'
    exact (Integrable.fintype_prod (fun v => integrable_mul_psiG (hDi v h hh h' hh') g _)).const_mul _
  unfold crystallineComparison.fourier
  rw [integral_congr_ae hae]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun h hh => integrable_finsetSum _ (fun h' hh' => hint h hh h' hh')),
    Hh, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [integral_finsetSum _ (fun h' hh' => hint h hh h' hh'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h' hh' => ?_
  have hp := integral_fintype_prod_volume_eq_prod (fun v (c : ℂ) => D v h h' c * psiG g ((g • σ) v) c)
  rw [integral_const_mul, hp]
  simp_rw [hone]
  rw [Finset.prod_mul_distrib]
  ring

theorem exists_good (τ : crystallineComparison.V f) : ∃ x : crystallineComparison.V f, Good x ∧ Good (x + τ) := by
  refine ⟨fun v => ((‖τ v‖ + 1 : ℝ) : ℂ), fun v => ?_, fun v => ?_⟩
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) ≠ 0
    have hpos : (0 : ℝ) < ‖τ v‖ + 1 := by positivity
    exact_mod_cast hpos.ne'
  · show ((‖τ v‖ + 1 : ℝ) : ℂ) + τ v ≠ 0
    intro h
    have h2 : τ v = -(((‖τ v‖ + 1 : ℝ) : ℂ)) := by linear_combination h
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_neg] at h3
    rw [Complex.norm_of_nonneg (by positivity)] at h3
    linarith

theorem herglotz_germ (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (hat : Fin f → ℂ → H → H → ℂ)
    (hG : GermData Y U P Q hat)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (Lm : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology Lm] [IsZLattice ℝ Lm]
    (hLm : ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm) (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V f, Good x → Good (x + g • σ) → ‖phi Y κ U x (x + g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  obtain ⟨LIM, hL⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists f Lm
  have hbd : ∀ σ ∈ crystallineComparison.dualSet La,
      ‖Hh Y κ hat (g • σ) + A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)‖ ≤ F σ := by
    intro σ hσ
    rw [← mean_split Lm.toAddSubgroup LIM hG κ hκ hL (g • σ)]
    refine Formalism.FourierDecayAlt.P.mean_bound_estimate _ LIM _ (F σ) hL.1 ?_
    intro x
    unfold phiG
    split_ifs with hx
    · exact hF σ hσ x hx.1 hx.2
    · obtain ⟨x0, h1, h2⟩ := exists_good (g • σ)
      simpa using (norm_nonneg _).trans (hF σ hσ x0 h1 h2)
  let A : crystallineComparison.V f → ℂ := fun σ => ((∏ v, dl v : ℝ) : ℂ) * A0 Lm.toAddSubgroup LIM Y κ U P Q (g • σ)
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) A := by
    intro T w hT
    have hinj : Set.InjOn (fun σ : crystallineComparison.V f => g • σ) T :=
      fun a _ b _ hab => smul_right_injective (crystallineComparison.V f) hgne hab
    have hT' : ∀ τ ∈ T.image (fun σ : crystallineComparison.V f => g • σ), τ ∈ Lm.toAddSubgroup := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      exact hLm σ (hT σ hσ)
    have h0 := limit_average_positive_definite Lm.toAddSubgroup LIM hG κ hκ hL.1 (T.image (fun σ : crystallineComparison.V f => g • σ)) hT'
      (fun τ => w (g⁻¹ • τ))
    simp_rw [Finset.sum_image hinj] at h0
    simp only [inv_smul_smul₀ hgne, ← smul_sub] at h0
    have hsplit : (∑ σ ∈ T, ∑ σ' ∈ T, A (σ - σ') * w σ * starRingEnd ℂ (w σ')) =
        ((∏ v, dl v : ℝ) : ℂ) * ∑ σ ∈ T, ∑ σ' ∈ T,
          A0 Lm.toAddSubgroup LIM Y κ U P Q (g • (σ - σ')) * w σ * starRingEnd ℂ (w σ') := by
      simp only [A, Finset.mul_sum, mul_assoc]
    rw [hsplit, Complex.re_ofReal_mul]
    exact mul_nonneg hc0 h0
  have hb : ∀ σ : crystallineComparison.dualSet La, ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [hfour]
    simp only [A]
    rw [← mul_add, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hbd σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + A σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) A (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

theorem herglotz_plain (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) (g : ℝ) (hg : 0 < g) (dl : Fin f → ℝ)
    (hdl : ∀ v, 0 < dl v) (hat : Fin f → ℂ → H → H → ℂ)
    (hhat : ∀ v l h h', hat v l h h' = ((dl v : ℝ) : ℂ)⁻¹ * ∫ c, D v h h' c * psiG g l c)
    (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (F : crystallineComparison.V f → ℝ)
    (hFs : Summable fun σ : crystallineComparison.dualSet La => F σ)
    (hF : ∀ σ ∈ crystallineComparison.dualSet La, ‖Hh Y κ hat (g • σ)‖ ≤ F σ)
    (z₀ : crystallineComparison.V f) (S : Finset (crystallineComparison.V f)) (hS : ∀ z ∈ S, z - z₀ ∈ La) :
    ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := by
  have hgne : g ≠ 0 := hg.ne'
  have hdlne : ∀ v, dl v ≠ 0 := fun v => (hdl v).ne'
  have hc0 : 0 ≤ ∏ v, dl v := Finset.prod_nonneg fun v _ => (hdl v).le
  have hfour : ∀ σ : crystallineComparison.V f, crystallineComparison.fourier (Nz Y κ D) σ = ((∏ v, dl v : ℝ) : ℂ) * Hh Y κ hat (g • σ) := by
    intro σ
    rw [fourier_Nz Y κ hκ D hD hDi g hgne dl hdlne hat hhat σ, Complex.ofReal_prod]
  have hPD : crystallineComparison.PDOn (crystallineComparison.dualSet La) (0 : crystallineComparison.V f → ℂ) := by
    intro T w _
    simp
  have hb : ∀ σ : crystallineComparison.dualSet La,
      ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ ≤ (∏ v, dl v) * F σ := by
    intro σ
    rw [Pi.zero_apply, add_zero, hfour, norm_mul, Complex.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hF σ σ.2) hc0
  have hsum : Summable fun σ : crystallineComparison.dualSet La => (∏ v, dl v) * F σ := hFs.mul_left _
  have hS2 : Summable fun σ : crystallineComparison.dualSet La => ‖crystallineComparison.fourier (Nz Y κ D) σ + (0 : crystallineComparison.V f → ℂ) σ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsum
  have key := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement f La (Nz Y κ D) 0 (Nz_nonneg Y κ hκ D hD)
    (Nz_lsc Y κ hκ D hD hDc) (Nz_integrable Y κ D hDi) hPD hS2 z₀ S hS
  calc ZLattice.covolume La * ∑ z ∈ S, Nz Y κ D z ≤ _ := key
    _ ≤ ∑' σ : crystallineComparison.dualSet La, (∏ v, dl v) * F σ := hS2.tsum_le_tsum hb hsum
    _ = (∏ v, dl v) * ∑' σ : crystallineComparison.dualSet La, F σ := tsum_mul_left

end

end Formalism.FourierDecayAlt.P.PBC
end

