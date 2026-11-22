import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare
open scoped TensorProduct ContDiff Topology Pointwise

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem taylor_bound {φ φ' φ'' : ℝ → ℂ} (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) {C : ℝ}
    (hC : ∀ s, ‖φ'' s‖ ≤ C) {t : ℝ} (ht : 0 < t) : ‖(t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0‖ ≤ C * t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have a : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖φ' s - φ' 0‖ ≤ C * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (h2 s).hasDerivWithinAt) fun s _ => hC s
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ s - (s : ℂ) * φ' 0) (φ' s - φ' 0) s := fun s => by
    have := (h1 s).sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (φ' 0))
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
    exact this
  have b := norm_image_sub_le_of_norm_deriv_le_segment' (C := C * t) (a := 0) (b := t)
    (fun s _ => (d s).hasDerivWithinAt) (fun s hs => (a s ⟨hs.1, hs.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC0)) t ⟨ht.le, le_rfl⟩
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have e : (t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0 = (t : ℂ)⁻¹ * (φ t - t * φ' 0 - (φ 0 - ((0 : ℝ) : ℂ) * φ' 0)) := by
    field_simp
    simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_le_iff₀ ht]
  linarith

theorem eq_zero_of_lintegral_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : Continuous f)
    (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  have ho : IsOpen {w | f w ≠ 0} := isOpen_ne_fun hf continuous_const
  have h1 := (lintegral_eq_zero_iff (hf.measurable.enorm.pow_const 2)).1 h0
  have h2 : μ ({w | f w ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply ho.measurableSet]
    refine measure_mono_null (fun w hw => ?_) h1
    simpa using hw
  have h3 := h𝓕.measure_zero_of_invariant _ (fun γ => by
    ext w
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show f (((-γ : Γ) : G) + w) ≠ 0 ↔ f w ≠ 0
    rw [← norm_ne_zero_iff, hp _ (-γ).2, norm_ne_zero_iff]) h2
  have h4 := (ho.measure_eq_zero_iff μ).1 h3
  funext w
  by_contra hw
  exact (Set.eq_empty_iff_forall_notMem.1 h4) w hw

theorem lintegral_eq_zero_of_approx {G : Type} [MeasurableSpace G] (ν : Measure G) (hν : ν Set.univ = 1) (δ : G → ℂ)
    (C C' : ℝ) (h : ∀ t : ℝ, 0 < t → ∃ a b r : G → ℂ, δ = a - b ∧ ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ∧
      (∀ w, ‖r w‖ ≤ C * t) ∧ ∀ w, ‖b w‖ ≤ C' * t) : ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν = 0 := by
  have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have key : ∀ t : ℝ, 0 < t → ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) := by
    intro t ht
    obtain ⟨a, b, r, e, h1, h2, h3⟩ := h t ht
    have h4 : ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((C * t) ^ 2) := by
      refine (lintegral_mono (g := fun _ => ENNReal.ofReal ((C * t) ^ 2)) fun w => ?_).trans ?_
      · show ‖r w‖ₑ ^ 2 ≤ _
        rw [en]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h2 w) 2)
      · rw [lintegral_const, hν, mul_one]
    calc ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ∫⁻ w, (2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)) ∂ν := by
          refine lintegral_mono fun w => ?_
          show ‖δ w‖ₑ ^ 2 ≤ 2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)
          rw [en, en, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h5 : ‖δ w‖ ≤ ‖a w‖ + ‖b w‖ := by rw [e]; exact norm_sub_le _ _
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          have h7 := pow_le_pow_left₀ (norm_nonneg _) (h3 w) 2
          nlinarith [sq_nonneg (‖a w‖ - ‖b w‖)]
      _ = 2 * ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const, hν, mul_one]
      _ ≤ 2 * ENNReal.ofReal ((C * t) ^ 2) + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [h1]; gcongr
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (q := (C * t) ^ 2) (by norm_num),
            ENNReal.ofReal_ofNat]
  have hc : Continuous fun t : ℝ => ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, ENNReal.ofReal_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)) bot_le

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem theta_norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem theta_bounded (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc w
  rw [← theta_norm_periodic hψ hf γ hγ w]
  exact hC _ h

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    have := symplOH_add_right w 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  unfold heisO
  rw [h, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem quotient_bound (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ w,
      ‖((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f) - dLine ψ S T L f) w‖ ≤ C * t := by
  have h1 := theta_dLine hθ hψ hL hf
  obtain ⟨C, hC⟩ := theta_bounded hψ (theta_dLine hθ hψ hL h1)
  refine ⟨C, fun t ht w => ?_⟩
  have := taylor_bound (hasDerivAt_heisO hθ hψ hL hf w) (hasDerivAt_heisO hθ hψ hL h1 w) (C := C) (fun s => by
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hC _) ht
  rw [L.map_zero, heisO_zero, heisO_zero] at this
  exact this

variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hom.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hf' := hom.om_pres (g, h) f hf
  have hδ := theta_sub (theta_dLine hθ hψ hL' hf') (hom.om_pres (g, h) _ (theta_dLine hθ hψ hL hf))
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C', hC'⟩ := quotient_bound hθ hψ hL' hf'
  refine (sub_eq_zero.1 (eq_zero_of_lintegral_eq_zero (G := WA T S) (ratL T S) μ 𝓕 h𝓕 _ hδ.cont
    (theta_norm_periodic hψ hδ) ?_)).symm
  refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) (by rw [Measure.restrict_apply_univ, h1]) _ C C' fun t ht => ?_
  have hr := theta_sub (theta_smul (t : ℂ)⁻¹ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf))
    (theta_dLine hθ hψ hL hf)
  refine ⟨_, _, _, ?_, hom.om_unit μ 𝓕 hμ h𝓕 (g, h) _ hr, hC t ht, hC' t ht⟩
  rw [map_sub, map_smul, map_sub, hom.om_heis g h _ f hf, hLL]
  abel

theorem isLineAt_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem isRealDir_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    IsRealDir T S (lineAt θ τ z) := ⟨(isLineAt_lineAt hθ τ z).1, (isLineAt_lineAt hθ τ z).2.1⟩

theorem compAt_mul (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_mul_inv (τ : D.what₂.Tau) (g : GA D S) : compAt θ τ (mt S g) * compAt θ τ (mt S g⁻¹) = 1 := by
  have e : mt S g * mt S g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← compAt_mul]
  erw [e]
  exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)

theorem lineAt_move (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T :=
    { toFun := fun t => actO S T g h (lineAt θ τ z t)
      map_zero' := by unfold actO; rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold actO; rw [AddMonoidHom.map_add, Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      unfold actO
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem theta_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) :=
  theta_dLine hθ hψ (isRealDir_lineAt hθ τ z) hf

theorem om_dRho (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hom hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _) (lineAt_move hθ g h τ z) hf

end GlobalTheory.OrientedHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrientedRealForm

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem map_inv_of_det_ne {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map φ)⁻¹ = G⁻¹.map φ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.2 h), Matrix.map_one _ φ.map_zero φ.map_one]

theorem trace_eq_sum {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ e, ∑ d, P a b * starRingEnd ℂ (y e b) * Q e d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  rfl

variable {D : D7}

theorem formAt_eq (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ x y =
      2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace).re := by
  rw [trace_eq_sum]
  unfold formAt gramAt
  rw [map_inv_of_det_ne _ _ (gram_det_ne S)]
  rfl

theorem realPlace_imaginaryGenerator_re_eq_zero (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  have h := tauE_star τ D.host.xi0
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg] at h
  have h2 := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at h2
  linarith

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  unfold cplxO
  rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun z := fun τ => cplxO (sS τ) (sT τ) (z τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem exists_real_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  intro D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ) (tauE D τ D.host.xi0)
    (realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ (z : RW T S) τ, jO S T sS sT z τ = cplxO (sS τ) (sT τ) (z τ) := fun _ _ => rfl
  refine ⟨omO S T, jO S T sS sT, fun x y hy => ?_, hJ, omO_self h, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [← psi_symplOH h hψ, h.iota_pi (V := T) (W := S) hy]
  · funext τ
    exact (key τ).2.1 (v τ)
  · rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (formAt_eq S T τ _ _).trans (Eq.trans ?_ (formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  · rw [hom]
    have hp : ∀ τ, v τ ≠ 0 → 0 < formAt S T τ (v τ) (jO S T sS sT v τ) := fun τ h0 =>
      lt_of_lt_of_eq (mul_pos two_pos ((key τ).2.2.2 (v τ) h0)) (formAt_eq S T τ _ _).symm
    obtain ⟨τ₀, h₀⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, hp τ₀ h₀⟩
    by_cases h0 : v τ = 0
    · rw [h0]
      simp [formAt]
    · exact (hp τ h0).le

end GlobalTheory.OrientedRealForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open GlobalTheory.Member

namespace GlobalTheory.UnRep.Space

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem isUnA_finHom {D : D7} (V : HSp D) (g : GA D V) : GlobalTheory.UnRep.IsUnA (cF D) V.gramᵀ (finHom V g).1 := by
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem herm_neg_eq {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) u v = -GlobalTheory.UnRep.hermE (cF D) V.gramᵀ u v := by
  unfold herm GlobalTheory.UnRep.hermE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change u a * (-V.gram b a) * cc (v b) = -(u a * V.gram b a * cc (v b))
  ring

set_option maxHeartbeats 1000000 in

theorem exists_rep_suppSplit : ∀ (D : D7) (V : HSp D) (N : ℕ), 0 < N → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ h ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * h * k ∧ FinCong V N k ∧ GlobalTheory.UnRep.SuppSplit (cF D) N (finHom V h).1 := by
  intro D V N hN g
  obtain ⟨e1, -, hfg, hsp, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, -⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (finrank_two D) (latC V) hfg hsp (finHom V g) N (isUnA_finHom V g) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [herm_neg_eq, herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * k⁻¹ * h⁻¹, ?_, h, hh, k, hk', by group, ?_, ?_⟩
  · change finHom V _ = 1
    simp only [map_mul, map_inv, e]
    group
  · unfold FinCong
    rw [e1, ek]
    exact hk
  · rw [eh]
    exact hs

end GlobalTheory.UnRep.Space
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSumIntegralBasis
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem isClosed_int_add_mul {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (M : ℕ) (hM : 0 < M) (hcl : IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c}) :
    IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} := by
  have key : {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} =
      ⋃ r : Fin M, (fun x => x - ((r : ℕ) : A)) ⁻¹' {a : A | ∃ c ∈ O, a = (M : A) * c} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨z, c, hc, rfl⟩
      have hMz : (0 : ℤ) < M := by exact_mod_cast hM
      have h0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg z hMz.ne'
      have h1 : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMz
      have hdiv := congrArg (fun t : ℤ => (t : A)) (Int.emod_add_mul_ediv z M)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hdiv
      refine ⟨⟨(z % M).toNat, by omega⟩, ((z / M : ℤ) : A) + c, add_mem (intCast_mem O _) hc, ?_⟩
      have hr : (((z % M).toNat : ℕ) : A) = ((z % M : ℤ) : A) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
      simp only [hr]
      linear_combination -hdiv
    · rintro ⟨r, c, hc, hx⟩
      refine ⟨((r : ℕ) : ℤ), c, hc, ?_⟩
      rw [Int.cast_natCast]
      linear_combination hx
  rw [key]
  exact isClosed_iUnion_of_finite fun r => hcl.preimage (continuous_id.sub continuous_const)

theorem exists_sum_of_approx {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (O : Subring A) (hO : IsCompact (O : Set A))
    (hcl : ∀ M : ℕ, 0 < M → IsClosed {a : A | ∃ c ∈ O, a = (M : A) * c})
    (hz : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c ∈ O, a = (M : A) * c) → a = 0)
    {β : Type} [Fintype β] (w : β → A) (a : A)
    (ha : ∀ M : ℕ, 0 < M → ∃ (z : β → ℤ) (c : A), c ∈ O ∧ a = ∑ i, (z i : A) * w i + (M : A) * c) :
    ∃ r : β → A, (∀ i, ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r i = (z : A) + (M : A) * c) ∧
      a = ∑ i, r i * w i := by
  classical
  have hSc : ∀ M : ℕ, 0 < M →
      IsClosed {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + (M : A) * c} :=
    fun M hM => isClosed_int_add_mul O M hM (hcl M hM)
  have hL : Continuous fun r : β → A => a - ∑ i, r i * w i :=
    continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  let t : ℕ → Set (β → A) := fun m =>
    (⋂ i, (fun r : β → A => r i) ⁻¹'
      {x : A | ∃ (z : ℤ) (c : A), c ∈ O ∧ x = (z : A) + ((m + 1 : ℕ) : A) * c}) ∩
    (fun r : β → A => a - ∑ i, r i * w i) ⁻¹' {x : A | ∃ c ∈ O, x = ((m + 1 : ℕ) : A) * c}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_iInter fun i => (hSc (m + 1) m.succ_pos).preimage (continuous_apply i)).inter
      ((hcl (m + 1) m.succ_pos).preimage hL)
  have hs : IsCompact (Set.univ.pi fun _ : β => (O : Set A)) := isCompact_univ_pi fun _ => hO
  have hne : ∀ u : Finset ℕ, ((Set.univ.pi fun _ : β => (O : Set A)) ∩ ⋂ m ∈ u, t m).Nonempty := by
    intro u
    have hNpos : 0 < ∏ m ∈ u, (m + 1) := Finset.prod_pos fun m _ => m.succ_pos
    obtain ⟨z, c, hc, hac⟩ := ha _ hNpos
    refine ⟨fun i => (z i : A), fun i _ => intCast_mem O (z i), ?_⟩
    simp only [Set.mem_iInter]
    intro m hm
    obtain ⟨k, hk⟩ : (m + 1) ∣ ∏ m ∈ u, (m + 1) := Finset.dvd_prod_of_mem _ hm
    rw [hk] at hac
    simp only [t, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun i => ⟨z i, 0, zero_mem O, by ring⟩, (k : A) * c, mul_mem (natCast_mem O k) hc, ?_⟩
    push_cast at hac ⊢
    linear_combination hac
  obtain ⟨r, -, hr⟩ := hs.inter_iInter_nonempty t htc hne
  simp only [t, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hr
  have hpred : ∀ M : ℕ, 0 < M → ∃ m : ℕ, M = m + 1 := fun M hM => ⟨M - 1, by omega⟩
  refine ⟨r, fun i M hM => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := hpred M hM
    exact (hr m).1 i
  · have h0 : a - ∑ i, r i * w i = 0 := hz _ fun M hM => by
      obtain ⟨m, rfl⟩ := hpred M hM
      exact (hr m).2
    exact sub_eq_zero.mp h0

private def intAdeles (F : Type) [Field F] [NumberField F] :
    Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' ha v := neg_mem (ha v)

theorem exists_sum_integralBasis : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ r : β → FiniteAdeleRing (𝓞 F) F, (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) ∧ a = ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) := by
  intro F _ _ β _ ω a ha
  obtain ⟨hcomp, hclM, hzero, -, -, -⟩ := GlobalTheory.T.integralFiniteAdele_compact_closed_multiples F
  have hexp : ∀ x : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) =
      ∑ i, ((ω.repr x i : ℤ) : FiniteAdeleRing (𝓞 F) F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω i : 𝓞 F) : F) := by
    intro x
    conv_lhs => rw [← ω.sum_repr x]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine exists_sum_of_approx (intAdeles F) hcomp hclM hzero _ a ?_
  intro M hM
  obtain ⟨x, c, hc, hac⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F M hM).2 a ha
  refine ⟨fun i => ω.repr x i, c, hc, ?_⟩
  rw [hac, hexp, nsmul_eq_mul]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrouStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  first | exact @GlobalTheory.IntegralPointsCompact.isCompact_integral_points | exact GlobalTheory.IntegralPointsCompact.isCompact_integral_points | (intros; apply GlobalTheory.IntegralPointsCompact.isCompact_integral_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  first | exact @GlobalTheory.LatOpen.isOpen_nsmul_latO | exact GlobalTheory.LatOpen.isOpen_nsmul_latO | (intros; apply GlobalTheory.LatOpen.isOpen_nsmul_latO <;> assumption)
end

