import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinor
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.ScalarColsMinor

noncomputable def bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    Matrix (Fin (p + m)) (Fin (p + m)) ℂ :=
  Matrix.of fun a : Fin (p + m) => Fin.append (M a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)

theorem det_bord {p m : ℕ} (M : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m)) :
    (bord M c).det = ∑ σ : Equiv.Perm (Fin (p + m)),
      if (fun k => σ (Fin.natAdd p k)) = c then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k else 0 := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [bord, Matrix.of_apply, Fin.append_left, Fin.append_right]
  rw [Finset.prod_boole]
  by_cases h : (fun k => σ (Fin.natAdd p k)) = c
  · rw [if_pos h, if_pos (fun k _ => congrFun h k), mul_one]
  · rw [if_neg h, if_neg (fun hh => h (funext fun k => hh k (Finset.mem_univ _)))]
    simp

theorem sum_perm_eq {A : Type} [AddCommGroup A] [Module ℂ A] {p m : ℕ}
    (M : Matrix (Fin (p + m)) (Fin p) ℂ) (F : (Fin m → Fin (p + m)) → A) :
    ∑ σ : Equiv.Perm (Fin (p + m)),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, M (σ (Fin.castAdd m k)) k) •
        F (fun k => σ (Fin.natAdd p k)) = ∑ c, (bord M c).det • F c := by
  simp only [det_bord, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp

theorem det_bord_mul {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ)
    (c : Fin m → Fin (p + m)) : (bord (Λ * N) c).det = N.det * (bord Λ c).det := by
  have h : bord (Λ * N) c = bord Λ c * (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks N 0 0 (1 : Matrix (Fin m) (Fin m) ℂ))) := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord, Matrix.mul_apply]
    · simp [bord, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
    mul_comm]

theorem det_bord_perm {p m : ℕ} (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (c : Fin m → Fin (p + m))
    (τ : Equiv.Perm (Fin m)) :
    (bord Λ (fun k => c (τ k))).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (bord Λ c).det := by
  have h : bord Λ (fun k => c (τ k)) = (bord Λ c).submatrix id
      (finSumFinEquiv.permCongr (Equiv.sumCongr (1 : Equiv.Perm (Fin p)) τ)) := by
    ext a b
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simp [bord]
    · simp [bord]
  rw [h, Matrix.det_permute', Equiv.Perm.sign_permCongr]
  have := Equiv.Perm.sign_sumCongr (1 : Equiv.Perm (Fin p)) τ
  simp only [Equiv.Perm.sumCongr] at this
  rw [this]
  simp

theorem prod_ofFn_sum {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℂ)
    (T : Fin m → Fin n → A) :
    (List.ofFn fun k => ∑ d, Q k d • T k d).prod =
      ∑ d : Fin m → Fin n, (∏ k, Q k (d k)) • (List.ofFn fun k => T k (d k)).prod := by
  have h := (MultilinearMap.mkPiAlgebraFin ℂ m A).map_sum (fun k d => Q k d • T k d)
  simp only [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply] at h
  exact h

theorem sum_det_qminor {A : Type} [Ring A] [Algebra ℂ A] {p m : ℕ} (E : Fin (p + m) → Fin (p + m) → A)
    (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (d : Fin m → Fin (p + m)) (w : ℂ) :
    ∑ c : Fin m → Fin (p + m), (bord Λ c).det • qminor E c d w =
      ((m.factorial : ℕ) : ℂ) • ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
  simp only [qminor, Finset.smul_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))]
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin m), ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
      (((Equiv.Perm.sign τ : ℤ) : A) *
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c (τ k)) (d k)).prod) =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro τ
    refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ fun c => ?_
    have hc : (Equiv.arrowCongr τ.symm (Equiv.refl _)) c = fun k => c (τ k) := by
      ext k; simp
    rw [hc, det_bord_perm, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

theorem antisym_prod_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin m) (Fin (p + m)) ℂ) (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) (w : ℂ), ∑ σ : Equiv.Perm (Fin (p + m)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, (Λ * N) (σ (Fin.castAdd m k)) k) • (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m), ((Matrix.of fun a : Fin (p + m) => Fin.append (Λ a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w := by
  intro A _ _ p m E Q Λ N w
  have h1 := sum_perm_eq (Λ * N) (fun c : Fin m → Fin (p + m) =>
    (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (c k) d).prod)
  rw [h1]
  change _ = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m),
    ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w
  rw [Finset.sum_comm]
  have hf : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have h2 : ∀ d : Fin m → Fin (p + m), ∑ c : Fin m → Fin (p + m),
      ((bord Λ c).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w =
      ∑ c : Fin m → Fin (p + m), (bord Λ c).det • (∏ k, Q k (d k)) •
        (List.ofFn fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) (c k) (d k)).prod := by
    intro d
    simp only [mul_comm (bord Λ _).det, mul_smul]
    rw [← Finset.smul_sum, ← Finset.smul_sum, sum_det_qminor, smul_smul _ ((m.factorial : ℕ) : ℂ),
      inv_mul_cancel₀ hf, one_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  rw [Finset.sum_congr rfl fun d _ => h2 d, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [det_bord_mul, mul_smul, prod_ofFn_sum Q (fun k d => Tm E (w - ((k : ℕ) : ℂ)) (c k) d),
    Finset.smul_sum (r := (bord Λ c).det)]

end GlobalTheory.ScalarColsMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFrameEntryRelation
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselIntertwine

theorem bessel_dsig (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDS ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp} (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hl : IsBes R z π l) {X : Mx k r} (hX : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X) (hX' : PI.UpqRep.InLieHpk k r X)
    {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = Formalism.FourierDecayAlt.Q.dRep π X (l v) := by
  have hd := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 v hv).2 X hX'
  have h1 : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Formalism.QuantumDeterminants.UH]
    · intro a i _
      simp [Matrix.one_apply]
    · intro i j _ _ _
      simp [Matrix.one_apply]
  have he : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (l v) := by
    funext t
    have := hl.2.2.1 _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) 1 h1 v hv
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.Qx8.psi_one hz, one_smul] at this
    exact this
  rw [he] at hd
  exact hd.deriv.symm

theorem bessel_intertwines_glW : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l g hz hT hg hl i j v hv
  obtain ⟨hF, hU⟩ := (GlobalTheory.T.frameW_conj_matrix_units k r z g hz hT hg).2.2.1
  rw [← hU i j]
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.QrD.frame_lie hF i j
  set Y := Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) _ i j with hY
  have hinv : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r :=
    Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have e1 : (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart1, hinv, sub_eq_add_neg]
  have e2 : (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart2, hinv, sub_neg_eq_add]
  have l1 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y) := h1.1.1
  have l2 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y) := h2.1.1
  have s1 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l1).1 v hv).1
  have s2 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l2).1 v hv).1
  rw [Rep.dC, e1, e2, hl.1 _ s1 _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ s2), hl.2.1 _ _ s2,
    bessel_dsig hK hR hz hl h1 l1 hv, bessel_dsig hK hR hz hl h2 l2 hv]
  rfl

end GlobalTheory.BesselIntertwine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapNormIdentityStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  first | exact @GlobalTheory.BesselAdjoint.adjoint_be | exact GlobalTheory.BesselAdjoint.adjoint_be | (intros; apply GlobalTheory.BesselAdjoint.adjoint_be <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselGrowth

theorem continuous_hsNorm (k r : ℕ) :
    Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r)) := by
  unfold Formalism.FourierDecayAlt.B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  refine Complex.continuous_normSq.comp ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem measurable_hsNorm_rpow (k r : ℕ) (A : ℝ) :
    Measurable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) :=
  (continuous_hsNorm k r).measurable.pow_const _

theorem hsNorm_nonneg {k r : ℕ} (g : Mx k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem growthS_of (hN : NormInv) (hG : GrowthG) : GrowthS := by
  intro k r z μW μN μG νq A _ _ hW hNn hGm hq hA
  obtain ⟨hS0, hS⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hNn
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 hS0 hS hq
  have hA0 : 0 ≤ A := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  have hint := hG k r μG A hGm hA
  have hm := measurable_hsNorm_rpow k r A
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A)) with hF
  have hFm : Measurable F := hm.ennreal_ofReal
  have hfin : ∫⁻ x, F x ∂μG < ⊤ := hint.lintegral_lt_top
  have hν : νq Set.univ ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [Measure.measure_univ_eq_zero.mp h0, lintegral_zero_measure, lintegral_one] at h1
    exact hGm.2.1 (Measure.measure_univ_eq_zero.mp h1)
  have hSfin : ∫⁻ s, F s ∂(muSof μW μN) < ⊤ := by
    by_contra hc
    have htop : ∫⁻ s, F s ∂(muSof μW μN) = ⊤ := top_le_iff.mp (not_lt.mp hc)
    have hle : ∫⁻ _x, (⊤ : ℝ≥0∞) ∂νq ≤
        ∫⁻ x, (∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muSof μW μN)) ∂νq := by
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with x hx
      have hx1 := ((hN k r).2 _ hx).2
      have hFx : F x ≠ 0 := by
        simp only [hF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (by linarith) _
      have h2 : ∫⁻ s, F s * F x ∂(muSof μW μN) = ⊤ := by
        rw [lintegral_mul_const _ hFm, htop, ENNReal.top_mul hFx]
      rw [← h2]
      refine lintegral_mono_ae ?_
      filter_upwards [(ae_iff.mpr hS : ∀ᵐ s ∂(muSof μW μN),
        Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))] with s hs
      have hsx := ((hN k r).2 _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hs hx)).2
      simp only [hF]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hsNorm_nonneg _) _),
        ← Real.mul_rpow (hsNorm_nonneg _) (hsNorm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hsx) ((hN k r).1 _ _) (by linarith)
    rw [← hq F hFm, lintegral_const, ENNReal.top_mul hν] at hle
    exact absurd hfin (not_lt.mpr hle)
  have hf : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) :=
      continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) :=
      continuous_snd
    exact h1.matrix_mul h2
  have hI : Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x : Mx k r) ^ (-A))
      (muSof μW μN) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hsNorm_nonneg _) _)).mpr hSfin⟩
  exact (integrable_map_measure hm.aestronglyMeasurable hf.measurable.aemeasurable).mp hI

end BesselGrowth

theorem besselGrowthS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS :=
  BesselGrowth.growthS_of GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one GlobalTheory.T.growth_unitaryGroup_rpow_neg_integrable

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselLieTriangularVanishing
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNilp

variable {k r : ℕ}

theorem H_ne {i j : Fin (2 * r + k + 1)} (h : Formalism.QuantumDeterminants.Hpk k r i j ≠ 0) :
    (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
      (r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val) := by
  unfold Formalism.QuantumDeterminants.Hpk at h
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact Or.inl h1
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · exact Or.inr (Or.inl h2)
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · exact Or.inr (Or.inr ⟨h3.1, h3.2.1, congrArg Fin.val h3.2.2⟩)
  · rw [if_neg h1, if_neg h2, if_neg h3] at h
    exact absurd rfl h

theorem H_herm : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Formalism.QuantumDeterminants.Hpk]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem H_sq : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff, and_true]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : Formalism.QuantumDeterminants.Hpk k r i b = 0 := by
        by_contra hne
        have h1 := H_ne hne
        have : b.val ≠ i.val := fun e => hb (Fin.ext e)
        omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : Formalism.QuantumDeterminants.Hpk k r i b = 0 := by
        by_contra hne
        have h1 := H_ne hne
        have : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
        omega
      rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

def Pat (Y : Mx k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0

theorem pat_theta {Y : Mx k r} (hY : Pat Y) : Pat (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : Formalism.QuantumDeterminants.Hpk k r b j = 0
  · rw [hb, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
  intro a _
  by_cases ha : Formalism.QuantumDeterminants.Hpk k r i a = 0
  · rw [ha, zero_mul]
  have h1 := H_ne ha
  have h2 := H_ne hb
  have : Y b a = 0 := by
    apply hY
    rw [Fin.lt_def] at hij ⊢
    omega
  rw [conjTranspose_apply, this, star_zero, mul_zero]

theorem ell_add (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A + B) = Formalism.QuantumDeterminants.ell k r z A + Formalism.QuantumDeterminants.ell k r z B := by
  unfold Formalism.QuantumDeterminants.ell
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rw [Matrix.add_mulVec]; rfl

theorem ell_smul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (A : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (c • A) = c * Formalism.QuantumDeterminants.ell k r z A := by
  unfold Formalism.QuantumDeterminants.ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rw [Matrix.smul_mulVec]; rfl

theorem ell_sub (z : Fin (2 * r + k + 1) → ℂ) (A B : Mx k r) :
    Formalism.QuantumDeterminants.ell k r z (A - B) = Formalism.QuantumDeterminants.ell k r z A - Formalism.QuantumDeterminants.ell k r z B := by
  have : A - B = A + (-1 : ℂ) • B := by simp [sub_eq_add_neg]
  rw [this, ell_add, ell_smul]; ring

theorem theta_key (Y : Mx k r) :
    (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * Y ∧
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r) = Yᴴ * Formalism.QuantumDeterminants.Hpk k r := by
  constructor
  · rw [conjTranspose_mul, conjTranspose_mul, H_herm, conjTranspose_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc, H_sq, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, H_sq, Matrix.one_mul]

theorem lie_re (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  show _ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  obtain ⟨h1, h2⟩ := theta_key Y
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add,
    conjTranspose_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h1, h2]
  simp

theorem lie_im (Y : Mx k r) : PI.UpqRep.InLieHpk k r
    ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  show _ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  obtain ⟨h1, h2⟩ := theta_key Y
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, neg_smul, neg_add_eq_zero, sub_neg_eq_add,
    conjTranspose_add, Matrix.add_mul, Matrix.mul_add, h1, h2, add_comm (Yᴴ * _)]

theorem on_real (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDS ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hπ : ∀ x, π 1 x = x) (hl : IsBes R z π l) {X : Mx k r}
    (hX : PI.UpqRep.InLieHpk k r X) (hP : Pat X) {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) =
      (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) • l v := by
  obtain ⟨hadd, hsmul, heq, hc⟩ := hl
  obtain ⟨hN, hd⟩ := GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character k r z X hz hX hP
  have h1 := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hadd hsmul hc v hv).2 X hX
  have h2 := hd.smul_const (l v)
  have hone : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
    refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  have e : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X)) • l v := by
    funext t
    have := heq 1 hone _ (hN t) v hv
    rwa [Matrix.one_mul, hπ] at this
  rw [e] at h1
  exact h1.unique h2

theorem bessel_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l hz hπ hl Y hY v hv
  have hθ := pat_theta (Y := Y) hY
  have p1 : Pat ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    intro i j hij
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, hY i j hij, hθ i j hij]
    simp
  have p2 : Pat ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    intro i j hij
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, hY i j hij, hθ i j hij]
    simp
  have s1 := GlobalTheory.DerivedAction.dsig_smooth hR.2 (lie_re Y) hv
  have s2 := GlobalTheory.DerivedAction.dsig_smooth hR.2 (lie_im Y) hv
  have e1 := on_real hK hR hz hπ hl (lie_re Y) p1 hv
  have e2 := on_real hK hR hz hπ hl (lie_im Y) p2 hv
  unfold Rep.dC
  rw [hl.1 _ s1 _ (R.smSub.smul_mem Complex.I s2), hl.2.1 _ _ s2, e1, e2, smul_smul, ← add_smul,
    ell_smul, ell_smul, ell_add, ell_sub]
  congr 1
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp
    simp
  rw [hI]
  simp only [star_mul', star_add, star_sub, star_neg, star_div₀, star_one, star_ofNat, Complex.star_def,
    Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

end GlobalTheory.BesselNilp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelationsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_mulRel_of_entry_relations : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  first | exact @GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | exact GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | (intros; apply GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOpsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  first | exact @GlobalTheory.HatNF.MulCoord.mul_coord | exact GlobalTheory.HatNF.MulCoord.mul_coord | (intros; apply GlobalTheory.HatNF.MulCoord.mul_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodIntegerPlanLowLevelsBoundStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodIntegerPlan_low_levels_bound : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  first | exact @GlobalTheory.GoodPlan.exists_plan | exact GlobalTheory.GoodPlan.exists_plan | (intros; apply GlobalTheory.GoodPlan.exists_plan <;> assumption)
end

