import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneParameterConjugationBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundConjAndMeasure
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol.UnipConj
variable {k r : ℕ} {ι : Type}

theorem of_conjM (a : Mat k r) (x : Mt k r) : Matrix.of (conjM a x) = a * Matrix.of x * a⁻¹ := rfl

theorem conjM_lmulM {a : Mat k r} (ha : IsUnit a.det) (m x : Mt k r) :
    conjM a (lmulM (Matrix.of m) x) = lmulM (Matrix.of (conjM a m)) (conjM a x) := by
  apply Matrix.of.injective
  have hl : ∀ (b : Mat k r) (y : Mt k r), Matrix.of (lmulM b y) = b * Matrix.of y := fun _ _ => rfl
  rw [of_conjM, hl, hl, of_conjM, of_conjM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.one_mul]

theorem mulVec_conj_iff (a M : Mat k r) (ha : IsUnit a.det) (w w' : Fin (2 * r + k + 1) → ℂ) :
    M *ᵥ (a *ᵥ w) = a *ᵥ w' ↔ (a⁻¹ * M * a) *ᵥ w = w' := by
  constructor
  · intro h
    have h' := congrArg (fun u => a⁻¹ *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec] at h'
    rw [← h', Matrix.mul_assoc]
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a ha, Matrix.one_mul]

theorem mem_realPts_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n : ι → Mat k r)
    (hn : ∀ v, IsUnit (n v).det) (m : ι → Mt k r) :
    m ∈ realPts (fun v y => n v *ᵥ Φ v y) Γ ↔ (fun v => conjM (n v)⁻¹ (m v)) ∈ realPts Φ Γ := by
  have key : ∀ v (w w' : Fin (2 * r + k + 1) → ℂ),
      (Matrix.of (m v) *ᵥ (n v *ᵥ w) = n v *ᵥ w') ↔ Matrix.of (conjM (n v)⁻¹ (m v)) *ᵥ w = w' := by
    intro v w w'
    rw [mulVec_conj_iff _ _ (hn v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hn v)]
  simp only [realPts, Set.mem_ofPred_eq, key]

theorem mem_RP_iff (n₁ g n₂ : ι → Mat k r) (h₁ : ∀ v, n₁ v ∈ Nset k r) (h₂ : ∀ v, n₂ v ∈ Nset k r)
    (x : ι → Mt k r) :
    x ∈ RP k r g ↔ (fun v => conjM (n₂ v)⁻¹ (x v)) ∈ RP k r (fun v => n₁ v * g v * n₂ v) := by
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (h₂ v).1
  simp only [RP, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  rw [StabHaar.Rset_conj (g v) (h₁ v) (h₂ v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hu v)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu v), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (hu v)]

private theorem conjM_conjM_inv {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a (conjM a⁻¹ y) = y := by
  have h := congrFun (StabHaar.conj_conj a a⁻¹) y
  rw [Matrix.mul_nonsing_inv a ha, StabHaar.conj_one] at h
  exact h

private theorem conjM_inv_conjM' {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a⁻¹ (conjM a y) = y := by
  have h := congrFun (StabHaar.conj_conj a⁻¹ a) y
  rw [Matrix.nonsing_inv_mul a ha, StabHaar.conj_one] at h
  exact h

theorem isFund_conj_and_measure : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k r : ℕ) (ι : Type) [Fintype ι] (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n₁ g n₂ : ι → Mat k r) (Ω : Set (ι → Mt k r)) (lam : Measure (Mt k r)), SigmaFinite lam → (∀ v, n₁ v ∈ Nset k r ∧ n₂ v ∈ Nset k r ∧ IsUnit (g v).det) → IsFund (realPts Φ Γ) (RP k r (fun v => n₁ v * g v * n₂ v)) Ω → IsFund (realPts (fun v y => n₂ v *ᵥ Φ v y) Γ) (RP k r g) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) ∧ Measure.pi (fun v => lam.map (conjM (n₂ v)⁻¹)) Ω = Measure.pi (fun _ : ι => lam) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) := by
  intro K V _ _ _ k r ι _ Φ Γ n₁ g n₂ Ω lam hlam hN hF
  have := hlam
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (hN v).2.1.1
  have hui : ∀ v, IsUnit ((n₂ v)⁻¹).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hu v)
  let e : ∀ _ : ι, Mt k r ≃ᵐ Mt k r := fun v => StabHaar.conjE (n₂ v)⁻¹ (hui v)
  let E : (ι → Mt k r) ≃ᵐ (ι → Mt k r) := MeasurableEquiv.piCongrRight e
  let Cf : (ι → Mt k r) → (ι → Mt k r) := fun x v => conjM (n₂ v) (x v)
  have hEC : ∀ y, E (Cf y) = y := fun y => funext fun v => conjM_inv_conjM' (hu v) (y v)
  have hCE : ∀ y, Cf (E y) = y := fun y => funext fun v => conjM_conjM_inv (hu v) (y v)
  have hC : Cf '' Ω = E ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show E (Cf x) ∈ Ω
      rw [hEC]
      exact hx
    · intro hy
      exact ⟨E y, hy, hCE y⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show MeasurableSet (Cf '' Ω)
    rw [hC]
    exact E.measurable hF.1
  · intro x hx
    have hx' : E x ∈ RP k r (fun v => n₁ v * g v * n₂ v) :=
      (mem_RP_iff n₁ g n₂ (fun v => (hN v).1) (fun v => (hN v).2.1) x).1 hx
    obtain ⟨m', ⟨hm'Γ, hm'Ω⟩, huniq⟩ := hF.2 (E x) hx'
    have hR : ∀ m, m ∈ realPts (fun v y => n₂ v *ᵥ Φ v y) Γ ↔ E m ∈ realPts Φ Γ :=
      fun m => mem_realPts_iff Φ Γ n₂ hu m
    have hM : ∀ m, E (mulP m x) = mulP (E m) (E x) := fun m =>
      funext fun v => conjM_lmulM (hui v) (m v) (x v)
    refine ⟨Cf m', ⟨(hR _).2 (by rw [hEC]; exact hm'Γ), ?_⟩, ?_⟩
    · show mulP (Cf m') x ∈ Cf '' Ω
      rw [hC]
      show E (mulP (Cf m') x) ∈ Ω
      rw [hM, hEC]
      exact hm'Ω
    · rintro m ⟨hmΓ, hmΩ⟩
      have hmΩ' : E (mulP m x) ∈ Ω := by
        have h0 : mulP m x ∈ Cf '' Ω := hmΩ
        rw [hC] at h0
        exact h0
      have h1 : E m = m' := huniq (E m) ⟨(hR m).1 hmΓ, by rw [← hM]; exact hmΩ'⟩
      rw [← h1, hCE]
  · have hmp : MeasurePreserving E (Measure.pi fun _ : ι => lam)
        (Measure.pi fun v => lam.map (e v)) :=
      haveI : ∀ v, SigmaFinite (lam.map (e v)) := fun v => (e v).sigmaFinite_map
      measurePreserving_pi _ _ (fun v => ⟨(e v).measurable, rfl⟩)
    show _ = Measure.pi (fun _ : ι => lam) (Cf '' Ω)
    rw [hC, hmp.measure_preimage_equiv]
    rfl
end GlobalTheory.DegVol.UnipConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPos
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.LastLen

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_inv_mulVec_eq_of_mem {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hg : g ∈ _root_.BranchingSupport.GG k r) (w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w w := by
  have hgH : gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg
  have hdet : IsUnit g.det := _root_.GlobalTheory.TensLen.isUnit_det_of_unitary (_root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r) hgH
  have h := _root_.Formalism.FourierDecayAlt.P.SettingConstruction.form_of_unitary (_root_.Formalism.QuantumDeterminants.Hpk k r) hgH (g⁻¹ *ᵥ w) (g⁻¹ *ᵥ w)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  exact h.symm

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma splitForm_mulVec_apply_eq_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) :
    (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = _root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) := by
  simp only [Matrix.mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_eq_sum_star_mul_sgn_mul_sig (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u = ∑ i, star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  unfold _root_.Formalism.QuantumDeterminants.herm
  simp only [dotProduct, Pi.star_apply, splitForm_mulVec_apply_eq_sgn_mul_sig]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma herm_splitForm_sub_eq_of_isotropic {k r : ℕ} (z y : Fin (2 * r + k + 1) → ℂ)
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hy : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (z - y) (z - y) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z := by
  have hz' : ∀ i : Fin (2 * r + k + 1), (i : ℕ) < r ∨ r + k < (i : ℕ) → z i = 0 := hz
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, herm_splitForm_eq_sum_star_mul_sgn_mul_sig]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  by_cases h1 : (i : ℕ) < r
  · have hσ := _root_.Formalism.QuantumDeterminants.GBasic.sig_lo k r i h1
    rw [hz' i (Or.inl h1), hz' (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (Or.inr (by omega)),
      hy (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i) (by omega)]
    simp
  · by_cases h2 : r + k < (i : ℕ)
    · rw [hz' i (Or.inr h2), hy i (by omega)]
      simp
    · rw [_root_.Formalism.QuantumDeterminants.GBasic.sig_mid k r i (by omega) (by omega), hy i (by omega), sub_zero]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma neg_re_herm_splitForm_le_sum_normSq (k r : ℕ) (u : Fin (2 * r + k + 1) → ℂ) :
    -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) u u).re ≤ ∑ i, Complex.normSq (u i) := by
  have hs : ∀ i, ‖_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i‖ = 1 := by
    intro i
    unfold _root_.Formalism.QuantumDeterminants.GBasic.sgn
    split_ifs <;> simp
  have hperm : ∑ i, Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)) = ∑ i, Complex.normSq (u i) :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (_root_.Formalism.QuantumDeterminants.GBasic.sig_sig k r)) (fun i => Complex.normSq (u i))
  rw [herm_splitForm_eq_sum_star_mul_sgn_mul_sig, Complex.re_sum, ← Finset.sum_neg_distrib]
  calc ∑ i, -(star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re
      ≤ ∑ i, (Complex.normSq (u i) + Complex.normSq (u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))) / 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Complex.abs_re_le_norm (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)))
        rw [norm_mul, norm_mul, norm_star, hs, one_mul] at h1
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        nlinarith [neg_le_abs (star (u i) * (_root_.Formalism.QuantumDeterminants.GBasic.sgn k r i * u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i))).re,
          sq_nonneg (‖u i‖ - ‖u (_root_.Formalism.QuantumDeterminants.GBasic.sig k r i)‖)]
    _ = ∑ i, Complex.normSq (u i) := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hperm]
        ring

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.LastLen.last_len : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ _root_.BranchingSupport.GG k r, _root_.Formalism.QuantumDeterminants.Tz k r z ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) ^ 2 ∧ ∀ a, 0 < _root_.BranchingSupport.lenA k r z g a ∧ _root_.BranchingSupport.lenA k r z g a = _root_.Formalism.MainNotions.S.lA k r z g a := by
  intro k r z hz hT g hg
  have hpos := (_root_.GlobalTheory.TensLen.lengths k r z hz hT g hg).2.2.1
  refine ⟨?_, fun a => ⟨hpos a, _root_.BranchingSupport.TensInh.lenA_eq_lA z g a⟩⟩
  have hbound : √(_root_.Formalism.QuantumDeterminants.Tz k r z) ≤ _root_.BranchingSupport.lenA k r z g (Fin.last r) := by
    rw [_root_.BranchingSupport.TensInh.lenA_eq_lA]
    unfold _root_.Formalism.MainNotions.S.lA _root_.Formalism.MainNotions.S.eucl
    refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
    rintro t ⟨y, hy, rfl⟩
    apply Real.sqrt_le_sqrt
    have hy0 : ∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0 := by
      intro i hi
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        unfold _root_.Formalism.QuantumDeterminants.bvec _root_.Formalism.QuantumDeterminants.eI
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have h' := congrArg Fin.val h
        have := b.1.isLt
        simp only at h'
        omega
      | zero => rfl
      | add x x' _ _ hx hx' => simp [hx, hx']
      | smul c x _ hx => simp [hx]
    have hf : _root_.Formalism.QuantumDeterminants.fvec k r z (Fin.last r) = z := by
      unfold _root_.Formalism.QuantumDeterminants.fvec
      simp
    rw [hf]
    calc _root_.Formalism.QuantumDeterminants.Tz k r z = -(_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (g⁻¹ *ᵥ (z - y)) (g⁻¹ *ᵥ (z - y))).re := by
          rw [herm_splitForm_inv_mulVec_eq_of_mem hg, herm_splitForm_sub_eq_of_isotropic z y hz hy0,
            _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq]
          simp
      _ ≤ _ := neg_re_herm_splitForm_le_sum_normSq k r _
  calc _root_.Formalism.QuantumDeterminants.Tz k r z = √(_root_.Formalism.QuantumDeterminants.Tz k r z) ^ 2 := (Real.sq_sqrt hT.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2

end GlobalTheory.LastLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.SeenIso

section General

variable {K U V W : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem exists_proj [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {h0 : W →ₗ⋆[K] W →ₗ[K] K}
    (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (X H : Submodule K V)
    (hWX : ∀ w, ι w ∈ X → w = 0)
    (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0) (hXH : ∀ x ∈ X, ∀ v ∈ H, h x v = 0)
    (hsp : ∀ v ∈ H, ∃ w, v - ι w ∈ X) (hHX : H ⊓ X = ⊥) :
    ∃ π : H →ₗ[K] W, Function.Injective π ∧ (∀ x y, h0 (π x) (π y) = h x y) ∧
      ∀ x : H, (x : V) - ι (π x) ∈ X := by
  obtain ⟨g, hg⟩ := (X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    exact hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))
  let p : V →ₗ[K] W := g ∘ₗ X.mkQ
  have hpι : ∀ w, p (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hpX : ∀ u ∈ X, p u = 0 := fun u hu => by
    have : X.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero X).2 hu
    simp only [p, LinearMap.comp_apply, this, map_zero]
  have hF : ∀ x : H, (x : V) - ι (p x) ∈ X := fun x => by
    obtain ⟨w, hw⟩ := hsp x x.2
    have := hpX _ hw
    rw [map_sub, hpι, sub_eq_zero] at this
    rwa [this]
  refine ⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : p x = 0 := hx
    have h2 := hF x
    rw [h1, map_zero, sub_zero] at h2
    have h3 : (x : V) ∈ H ⊓ X := ⟨x.2, h2⟩
    rw [hHX] at h3
    exact Subtype.ext h3
  · change h0 (p x) (p y) = _
    have a := hXH _ (hF x) _ y.2
    have b := hXι _ (hF y) (p x)
    have c : h (ι (p x)) ((y : V) - ι (p y)) = 0 := by rw [← hs.eq, b, map_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at a
    rw [map_sub, sub_eq_zero] at c
    rw [a, c, hι]

variable [NumberField K] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finrank_span_map (i : U →ₗ[K] V) (hi : Function.Injective i) (N : Submodule (𝓞 K) U) :
    finrank K (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      finrank K (Submodule.span K (N : Set U)) := by
  have : ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U) := rfl
  rw [this, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective i hi _).finrank_eq.symm

theorem card_quot_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    Nat.card (↥(A.map (i.restrictScalars (𝓞 K))) ⧸
      (B.map (i.restrictScalars (𝓞 K))).comap (A.map (i.restrictScalars (𝓞 K))).subtype) =
      Nat.card (A ⧸ B.comap A.subtype) := by
  have := AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  intro D T F H hW hH hHX N N' hN hN'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)
  have hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0 := fun w hw =>
    (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y
  obtain ⟨π, hinj, hπ, hF⟩ := exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι
    (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx))
    (fun v hv => by
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hv))
      exact ⟨w, by simpa using hx⟩) hHX
  have key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H,
      M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧
        seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E)) := by
    intro M hM
    refine ⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, hM hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · ext w
      constructor
      · intro hw
        obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hw
        refine ⟨⟨l, hM hl⟩, hl, ?_⟩
        have e' : l + x = D.sp.iXY 0 w := e
        have h1 := (Xsp F).add_mem (hF ⟨l, hM hl⟩) hx
        have h2 : w - π ⟨l, hM hl⟩ = 0 := hWX _ (by
          rw [map_sub, ← e']
          convert h1 using 1
          abel)
        exact (sub_eq_zero.1 h2).symm
      · rintro ⟨y, hy, rfl⟩
        refine Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩
        change _ = D.sp.iXY 0 (π y)
        abel
  obtain ⟨A, rfl, a⟩ := key N hN
  obtain ⟨B, rfl, b⟩ := key N' hN'
  rw [a, b]
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans
      (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm
  · exact (finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm
  · exact (card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm

end GlobalTheory.LoopC.SeenIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfold
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.SiegelUnfold

open Filter Topology in

theorem lseriesSummable_idealCount (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

theorem hasSum_zetaE (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    HasSum (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹)
      (zetaE K l) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := Complex.hasSum_re (lseriesSummable_idealCount K hs).hasSum
  unfold zetaE dedekindZeta LSeries
  simp only [Complex.ofReal_natCast] at h
  convert h using 2 with n
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]

theorem tsum_absNorm_pow_inv (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (zetaE K l) := by
  have hl0 : l ≠ 0 := by omega
  have h1 : ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ∑' 𝔞 : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹) := by
    refine tsum_subtype_eq_of_support_subset (s := {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ ⊥})
      (f := fun 𝔞 : Ideal (𝓞 K) => ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹)) ?_
    rintro 𝔞 h rfl
    exact h (by simp [hl0])
  have h := hasSum_zetaE K hl
  rw [h1, ← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable,
    ← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have key : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ENNReal.ofReal (((Ideal.absNorm
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I) ⟨n, I⟩) : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (((n : ℝ) ^ l)⁻¹) := by
    rintro ⟨I, rfl⟩; rfl
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  haveI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.card_eq_fintype_card]

def sumLat (E : Type) [Field E] [NumberField E] (k : ℕ) (𝔞 : Ideal (𝓞 E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule (𝓞 E) (Fin (k + 1) → E) where
  carrier := {y | (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ'}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun t ht => ?_, Λ'.add_mem ha' hb'⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha t ht) (hb t ht)
  zero_mem' := ⟨fun t _ => by simp, Λ'.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨fun t ht => ?_, Λ'.smul_mem c ha'⟩
    have := ha (t * c) (𝔞.mul_mem_right c ht)
    simpa [Algebra.smul_def, mul_assoc] using this

theorem latMean_sum_ne_zero : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE j hj w Φ hw hΦ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) := by
    unfold Formalism.HermitianLatticesTheory.vInv; positivity
  rw [GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits E hE k (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ]
  simp only [fun (𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥})
      (Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsLattice E Λ}) =>
    GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution E hE k (by omega) (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ 𝔞.1 Λ'.1 𝔞.2 Λ'.2]
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.ofReal_mul hv,
    Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rw [tsum_absNorm_pow_inv E hj]
  rfl

end GlobalTheory.FlagBase.SiegelUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneParameterConjugationBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_conjugation_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W) → ∀ κ : ℝ, (∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (w : H) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0) → ∃ C₀ : ℝ, ∀ v : H, (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∀ X, inG ε X → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g))))) → ∀ s : ℝ, |s| ≤ 1 → ∫ g : UJ ε, (β g).toReal * ‖(∫ m, ⟪v, σ (umat (m * (a s * g))) w⟫_ℂ ∂ν) - (∫ m, ⟪v, σ (umat (m * g)) w⟫_ℂ ∂ν)‖ ^ 2 ∂(muG ε) ≤ C₀ * s ^ 2 * (∫ m, ⟪v, σ (umat m) v⟫_ℂ ∂ν).re := by
  first | exact @GlobalTheory.TorusLip.torus_lipschitz | exact GlobalTheory.TorusLip.torus_lipschitz | (intros; apply GlobalTheory.TorusLip.torus_lipschitz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeriesStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries : PsiEigen := by
  first | exact @GlobalTheory.Dec.PsiEig.psiEigen | exact GlobalTheory.Dec.PsiEig.psiEigen | (intros; apply GlobalTheory.Dec.PsiEig.psiEigen <;> assumption)
end

