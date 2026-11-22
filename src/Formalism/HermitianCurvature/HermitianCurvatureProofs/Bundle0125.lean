import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (a : ℂ) (X : Wq →L[ℂ] Wp) : B.hsVec (a • X) = a • B.hsVec X := by
  simp only [B.hsVec, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  rfl

theorem tc_hsVec_sum {ι : Type} (s : Finset ι) (X : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [B.hsVec, ContinuousLinearMap.zero_apply]
    exact WithLp.toLp_zero 2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [B.hsVec, ContinuousLinearMap.add_apply]
    exact WithLp.toLp_add 2 _ _

theorem tc_gq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    B.gq Bs x = Q.wCell P.k P.r (Fin.last P.r) x.1 * NF.muZ P.k P.r Bs.μsec x.2 := by
  show bigCell P.k P.r x.1 (Bs.μsec x.2) = _
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r x.1 (Bs.μsec x.2)).1, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  rfl

theorem tc_sqrt_wq (k r : ℕ) (TT : ℝ) (x : MA.E r) :
    Real.sqrt (MA.wq k x TT) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) *
        wR k TT x.2 := by
  unfold MA.wq wR
  rw [Real.sqrt_mul (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)]
  congr 1
  have h : ∏ l : Fin r, Complex.normSq (x.1 l) ^ (MA.Mdim k r l - 1) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hM : MA.Mdim k r a = Formalism.QuantumDeterminants.Mdim k r a := rfl
    rw [if_pos (by simp), Complex.normSq_eq_norm_sq, hM, ← pow_mul, ← pow_mul, mul_comm]
  rw [h, Real.sqrt_sq (Finset.prod_nonneg fun a _ => by split_ifs <;> positivity)]

theorem tc_rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ := by
  funext q
  simp only [rawJ, rawR, Q.resG, tc_gq, tc_sqrt_wq]
  rw [tc_hsVec_smul, inner_smul_right]
  push_cast
  ring

theorem tc_mu (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∧
      Q.wCell P.k P.r (Fin.last P.r) q.1.1 * NF.muZ P.k P.r Bs.μsec q.1.2 ∈ OmB Bs := by
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hTT]; exact q.2.2
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
    linarith
  have h := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hG hGG
  exact ⟨hG, h.2, fun a => h.1 ⟨(a : ℕ) + 1, by omega⟩ (by show (a : ℕ) + 1 ≤ P.r; omega)⟩

theorem tc_famR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) :
    FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs})
      (Q.resG P.k P.r (Fin.last P.r) J) := by
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  refine ⟨?_, ?_, fun q => (tc_mu P Bs hpl q).2, ?_⟩
  · have hw : ContDiffOn ℝ ∞ (fun c : Fin P.r → ℂ => Q.wCell P.k P.r (Fin.last P.r) c) (OmX P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
    have hm : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
        {x | x.1 ∈ OmX P.r} :=
      Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
    exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1
  · intro c hc
    refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
    rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hhm : h * m ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
    have hcomm : Q.wCell P.k P.r (Fin.last P.r) c * (h * m) = (h * m) * Q.wCell P.k P.r (Fin.last P.r) c :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last P.r) c _ (fun a _ => a.isLt) hhm
    have hwg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
    have e : Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) =
        h * m * (Q.wCell P.k P.r (Fin.last P.r) c * g) * (h' * m') := by
      rw [← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c), ← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c),
        hcomm, Matrix.mul_assoc (h * m)]
    show Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) ∈ OmB Bs
    rw [e]
    exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
      ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩
  · exact Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
      (Fin.last P.r)

end

theorem gauge_transition_chain_holds : GTrChain := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ J hJ
  refine ⟨tc_famR P Bs hpl J hJ, fun e ρ => tc_rawJ P Bs e J ρ, fun e ρ Y => ?_⟩
  rw [tc_rawJ]
  funext q
  have hmu := tc_mu P Bs hpl q
  have hcv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) (OmB Bs) (Y : ℂ)
    Bs.z_mem Bs.z'_mem (isDom_omP Bs.z_mem Bs.z'_mem) J hJ q.1.1 q.2.1 _ hmu.1 hmu.2
  simp only [rawR, Finset.sum_apply]
  rw [hcv]
  simp only [Finset.sum_apply, tc_hsVec_sum, inner_sum, Finset.mul_sum, Fin.val_last]

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcLin
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)}

theorem lie_rsmul {X : Q.Mx k r} (hX : Q.inLieLev k r i X) (x : ℝ) : Q.inLieLev k r i (x • X) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX ⊢
  obtain ⟨h1, h2⟩ := hX
  have hs : ∀ v : Fin (2 * r + k + 1) → ℂ, (x • X) *ᵥ v = x • (X *ᵥ v) := fun v => by
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc, mul_assoc]
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [hs, (h2 a ha).1, smul_zero]
  · rw [hs, (h2 a ha).2, smul_zero]

private theorem inLieLev_add {X Y : Q.Mx k r} (hX : Q.inLieLev k r i X) (hY : Q.inLieLev k r i Y) :
    Q.inLieLev k r i (X + Y) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX hY ⊢
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
        (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX.1, hY.1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]

theorem glc_lin {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) : GLc k r (a • Z + Z') := by
  unfold GLc at *
  obtain ⟨h1, h2⟩ := hZ
  obtain ⟨h1', h2'⟩ := hZ'
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have e1 : hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    first | ring | (ring_nf; simp only [Complex.I_sq]; ring)
  have e2 : hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq
  rw [e1, e2]
  exact ⟨inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2'⟩

private theorem hermitian_halves_smul_add (Z Z' : Q.Mx k r) (a : ℂ) :
    hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' ∧
    hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  constructor
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq

private theorem rdV_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E)
    (X g : Q.Mx k r) (s : ℝ) : RdV (s • X) f g = (s : ℂ) • RdV X f g := by
  have hx : ∀ t : ℝ, (t : ℂ) • (s • X) = ((s * t : ℝ) : ℂ) • X := fun t => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  unfold Formalism.REAL.RdV
  simp only [hx]
  have key := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
  simp only [mul_zero] at key
  rw [key, Complex.coe_smul]

private theorem gLc_zero : GLc k r (0 : Q.Mx k r) := by
  unfold GLc Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2 Formalism.FourierDecayAlt.Q.inLieLev
  simp

private theorem rc_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc Formalism.REAL.RdV Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
  simp

private theorem rc_smul_add_of_smoothLev_of_gLc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
    {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r}
    (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) :
    Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g := by
  obtain ⟨e1, e2⟩ := hermitian_halves_smul_add Z Z' a
  have hz := hZ
  have hz' := hZ'
  unfold GLc at hz hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1', h2'⟩ := hz'
  unfold Rc
  rw [e1, e2,
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _),
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _)]
  simp only [rdV_real_smul, Complex.ofReal_neg]
  have haI : a * Complex.I = (a.re : ℂ) * Complex.I - a.im := by
    apply Complex.ext <;> simp
  rw [smul_add a, smul_smul a Complex.I, haI,
    show a • RdV (hpart1 (Hpk k r) Z) f g = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • RdV (hpart1 (Hpk k r) Z) f g by
      rw [Complex.re_add_im]]
  module

theorem rc_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)} {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    ∃ L : Q.Mx k r →ₗ[ℂ] E, ∀ Z, GLc k r Z → Rc Z f g = L Z := by
  let S : Submodule ℂ (Q.Mx k r) :=
    { carrier := {Z | GLc k r Z}
      add_mem' := fun {Z Z'} hZ hZ' => by simpa using glc_lin hZ hZ' 1
      zero_mem' := gLc_zero
      smul_mem' := fun c Z hZ => by simpa using glc_lin hZ gLc_zero c }
  let f0 : S →ₗ[ℂ] E :=
    { toFun := fun Z => Rc (Z : Q.Mx k r) f g
      map_add' := fun Z Z' => by simpa using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 Z'.2 1
      map_smul' := fun c Z => by simpa [rc_zero_left] using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 gLc_zero c }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f0
  exact ⟨L, fun Z hZ => (LinearMap.congr_fun hL ⟨Z, hZ⟩).symm⟩

theorem radial_coefficient_linearity : RcLin := by
  unfold RcLin
  intro k r E _ _ D f _ hf g hg a Z Z' hZ hZ'
  obtain ⟨L, hL⟩ := rc_linear hf hg
  rw [hL _ (glc_lin hZ hZ' a), hL Z hZ, hL Z' hZ', map_add, map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

def cW (k r : ℕ) (θ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def PhaseSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ θ : ℝ, ∃ h h' : Q.Mx k r, h ∈ UWset k r z ∧ h' ∈ UWset k r z' ∧
      (∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        h *ᵥ (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = Complex.exp (-((θ : ℂ) * Complex.I)) • (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) ∧
        (∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = 0 → h *ᵥ v = v) ∧
        CP.mu0 k r z z' (rot θ ζ) = h * cW k r θ * CP.mu0 k r z z' ζ * h') ∧
      ∀ v, inWb k r v → herm (Hpk k r) v z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v

def LowerUnipotentRotation : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (θ : ℝ) (Y : ℂ) (f : Q.Mx k r → E), ∀ g ∈ Q.Glev k r (Fin.last r),
      Q.tL k r z z' (Fin.last r) Y 1 0 f (cW k r θ * g) =
        Complex.exp (-((θ : ℂ) * Complex.I)) • Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => f (cW k r θ * x)) g

def RotRadSp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ (θ : ℝ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)), Φ ∈ Q.RadSp k r z z' π π' →
      (fun c g => Φ c (cW k r θ * g)) ∈ Q.RadSp k r z z' π π'

def ThtRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ (θ : ℝ) (h h' : Q.Mx P.k P.r), h ∈ UWset P.k P.r Bs.z → h' ∈ UWset P.k P.r Bs.z' →
    ∀ ζ ∈ Gauge.GC.Ann P,
      h *ᵥ SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = Complex.exp (-((θ : ℂ) * Complex.I)) • SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z = 0 → herm (Hpk P.k P.r) v (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 →
        h *ᵥ v = v) →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v) →
      ∀ Xf : Wq →L[ℂ] Wp,
        (Bs.π h).comp (((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) Xf).comp (Bs.π' h')) =
          Complex.exp ((θ : ℂ) * Complex.I) • (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) ((Bs.π h).comp (Xf.comp (Bs.π' h')))

def PhaseInvOfCut : Prop :=
  PhaseSec → LowerUnipotentRotation → RotRadSp → ThtRot → KapLine → AlgSS → DatumConst → FibStable → PhaseInv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
section
open Matrix Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ

def bigPt {n : ℕ} (d : Fin n → ℂ) : C.LPt := List.ofFn fun i => (1, d i)

def BigCellVan : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → Top.IsRadOf P p.T.base 0 F →
    ∀ d : Fin (P.r + 1) → ℂ, (∀ i, d i ≠ 0) → p.V F (bigPt d) = 0

def DensCOfParts : Prop := KB.PhiZero → KB.KloostDens → BigCellVan → KB.DensC

namespace Dens

theorem ptEntry_ones (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b ∧ a < l.length then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    cases a <;> cases b <;> simp [D.ptEntry, ih]

theorem ptMatN_bigPt {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = U.hMat 1 d := by
  ext a b
  have h : bigPt d = (List.ofFn d).map fun c => ((1 : ℕ), c) := by
    simp [bigPt, List.map_ofFn, Function.comp_def]
  simp only [D.ptMatN, h, ptEntry_ones, U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply,
    Equiv.Perm.one_apply, List.length_ofFn]
  by_cases hab : a = b
  · subst hab
    simp [List.getD_eq_getElem?_getD]
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [hab, hab']

theorem isLocPt_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.IsLocPt (bigPt d) n := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [bigPt, List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hd i⟩
  · simp [D.ptSize, bigPt, List.map_ofFn, Function.comp_def, List.sum_ofFn]

end Dens

theorem density_constant_of_parts : DensCOfParts := by
  intro hPZ hKD hBV Wp Wq _ _ _ _ _ _ P p F hC hR a
  obtain ⟨Φ0, hs, hcs, hdet, hV⟩ := hPZ Wp Wq P p F hC
  by_cases ha : D.IsLocPt a (P.r + 1)
  · have key : ∀ n, D.ptSize a = n →
        ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
      rintro n rfl
      obtain ⟨σ, d, -, h⟩ := Asm.exists_hMat a ha.1
      exact ⟨σ, d, h⟩
    obtain ⟨σ, d, hσd⟩ := key _ ha.2
    rw [hV a σ d ha hσd]
    refine hKD (P.r + 1) (Wq →L[ℂ] Wp) Φ0 hs hcs hdet ?_ a σ d ha hσd
    intro d' hd'
    rw [← hV (bigPt d') 1 d' (Dens.isLocPt_bigPt d' hd') (Dens.ptMatN_bigPt d').symm]
    exact hBV Wp Wq P p F hC hR d' hd'
  · unfold KB.Pl.V D.vecV
    rw [dif_neg (fun h => ha h.1)]

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

theorem pb_densC_of (hPZ : Formalism.FourierDecayAlt.KB.PhiZero) (hBV : PBJ.BigCellVan) : Formalism.FourierDecayAlt.KB.DensC :=
  PBJ.density_constant_of_parts hPZ kloosterman_density hBV

end Formalism.FourierDecayAlt.P
end
end

