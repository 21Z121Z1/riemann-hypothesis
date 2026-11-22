import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Formalism.UnipotentAdelicQuotients.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnitsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_character_finite_order_integral_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  first | exact @GlobalTheory.CharFin.char_finUnit_finite_order | exact GlobalTheory.CharFin.char_finUnit_finite_order | (intros; apply GlobalTheory.CharFin.char_finUnit_finite_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology ENNReal

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter

section Abstract

theorem ae_zero_of_lintegral_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (a b : ℕ → X → ℂ) (c : X → ℂ) (C : ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (hc : Measurable c) (hC : ∀ n x, ‖a n x‖ ≤ C) (ha0 : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 0))
    (hbc : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 (c x)))
    (he : ∀ n, ∫⁻ x, ‖b n x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) : ∀ᵐ x ∂ν, c x = 0 := by
  have hq : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have h1 : Tendsto (fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) atTop (𝓝 (∫⁻ _, 0 ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C ^ 2)
      (fun n => hq.measurable.comp (ha n)) (fun n => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · refine pow_le_pow_left' ?_ 2
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC n x)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    · simpa [Function.comp_def] using (hq.tendsto 0).comp (ha0 x)
  rw [lintegral_zero] at h1
  have h2 : ∫⁻ x, ‖c x‖ₑ ^ 2 ∂ν ≤ 0 := by
    have e : ∀ x, ‖c x‖ₑ ^ 2 = liminf (fun n => ‖b n x‖ₑ ^ 2) atTop := fun x =>
      ((hq.tendsto _).comp (hbc x)).liminf_eq.symm
    simp_rw [e]
    refine (lintegral_liminf_le fun n => hq.measurable.comp (hb n)).trans ?_
    have e2 : (fun n => ∫⁻ x, ((fun z : ℂ => ‖z‖ₑ ^ 2) ∘ b n) x ∂ν) = fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν := funext he
    rw [e2]
    exact h1.liminf_eq.le
  have h3 := (lintegral_eq_zero_iff (hq.measurable.comp hc)).1 (le_antisymm h2 zero_le')
  filter_upwards [h3] with x hx
  simpa using hx

theorem eq_zero_of_ae_fundamentalDomain {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Continuous c) (hp : ∀ γ ∈ Γ, ∀ w, ‖c (γ + w)‖ = ‖c w‖) (h0 : ∀ᵐ x ∂μ.restrict 𝓕, c x = 0) : c = 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have ho : IsOpen {x | c x ≠ 0} := isOpen_ne_fun hc continuous_const
  have h1 : μ {x | c x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show c (((-g : Γ) : G) + x) ≠ 0 ↔ c x ≠ 0
      rw [← norm_ne_zero_iff, hp _ (-g).2, norm_ne_zero_iff]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact h0
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h1

theorem tendsto_diffQuot {F : ℝ → ℂ} {d : ℂ} (h : HasDerivAt F d 0) :
    Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ * (F (1 / ((n : ℝ) + 1)) - F 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n =>
      (Nat.one_div_pos_of_nat (n := n)).ne'⟩
  refine (h.tendsto_slope_zero.comp h1).congr fun n => ?_
  simp only [Function.comp_apply, zero_add, Complex.real_smul, Complex.ofReal_inv]

theorem norm_diffQuot_le {F F' : ℝ → ℂ} {C : ℝ} (h : ∀ s, HasDerivAt F (F' s) s) (hC : ∀ s, ‖F' s‖ ≤ C) (t : ℝ)
    (ht : t ≠ 0) : ‖(t : ℂ)⁻¹ * (F t - F 0)‖ ≤ C := by
  have h1 := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F') (C := C)
    (fun s _ => (h s).hasDerivWithinAt) (fun s _ => hC s) (Set.mem_univ 0) (Set.mem_univ t)
  rw [sub_zero] at h1
  rw [norm_mul, norm_inv, Complex.norm_real, inv_mul_le_iff₀ (norm_pos_iff.2 ht), mul_comm]
  exact h1

end Abstract

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := hf.quasi γ w
  exact (congrArg norm this).trans (by rw [norm_mul, hψ.1.2.1, one_mul])

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← norm_periodic hψ hf γ hγ w]
  exact hC _ h

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hW : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T) {L L' : ℝ →+ WO S T}
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L')
    (hL0' : ∀ t, (L' t).map (finPart D) = 0) (e : ∀ t, L' t = actO S T g h (L t)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hW.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hF := hW.om_pres (g, h) f hf
  obtain ⟨hd, hdt⟩ := hasDerivAt_zero_and_isTheta hψ hL hL0 hf
  obtain ⟨hd', hdt'⟩ := hasDerivAt_zero_and_isTheta hψ hL' hL0' hF
  obtain ⟨C, hC⟩ := exists_bound hψ hdt
  let a : ℕ → WO S T → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ •
    (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f - f) - dLine ψ S T L f
  have hat : ∀ n, IsThetaFunO ψ S T (a n) := fun n =>
    isTheta_sub (isTheta_smul _ (isTheta_sub (isTheta_heisO_real hψ (hL0 _) hf) hf)) hdt
  have hct : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f) - om (g, h) (dLine ψ S T L f)) :=
    isTheta_sub hdt' (hW.om_pres _ _ hdt)
  have ha : ∀ n x, a n x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f x - heisO ψ S T (L 0) f x) - dLine ψ S T L f x := by
    intro n x
    rw [map_zero L, heisO_zero]
    rfl
  have hb : ∀ n x, om (g, h) (a n) x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L' (1 / ((n : ℝ) + 1))) (om (g, h) f) x - heisO ψ S T (L' 0) (om (g, h) f) x) -
        om (g, h) (dLine ψ S T L f) x := by
    intro n x
    rw [map_zero L', heisO_zero, e, ← hW.om_heis g h _ f hf, map_sub, map_smul, map_sub]
    rfl
  have key := ae_zero_of_lintegral_eq (μ.restrict 𝓕) a (fun n => om (g, h) (a n)) _ (C + C)
    (fun n => (hat n).cont.measurable) (fun n => (hW.om_pres _ _ (hat n)).cont.measurable) hct.cont.measurable
    (fun n x => by
      rw [ha]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC x))
      refine norm_diffQuot_le (hasDerivAt_line hψ hL hL0 hf x) (fun s => ?_) _ (Nat.one_div_pos_of_nat (n := n)).ne'
      rw [heisO, norm_mul, hψ.1.2.1, one_mul]
      exact hC _)
    (fun x => by
      have := (tendsto_diffQuot (hd x)).sub_const (dLine ψ S T L f x)
      rw [sub_self] at this
      exact this.congr fun n => (ha n x).symm)
    (fun x => ((tendsto_diffQuot (hd' x)).sub_const (om (g, h) (dLine ψ S T L f) x)).congr fun n => (hb n x).symm)
    (fun n => hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hat n))
  exact (sub_eq_zero.1 (eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hct.cont (norm_periodic hψ hct) key)).symm

variable {θ : InfFam D}

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem compAt_mt_mul_inv (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) * compAt θ τ (mt V g⁻¹) = 1 := by
  rw [← compAt_mul, ← mt_mul, mul_inv_cancel, mt_one, compAt_one]

theorem compAt_mt_inv_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g⁻¹) * compAt θ τ (mt V g) = 1 := by
  rw [← compAt_mul, ← mt_mul, inv_mul_cancel, mt_one, compAt_one]

theorem compAt_actO (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T) (x : WO S T) :
    compAt θ τ (actO S T g h x) = compAt θ τ (mt T h) * compAt θ τ x * compAt θ τ (mt S g⁻¹) := by
  unfold actO
  rw [compAt_mul, compAt_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem lineAt_actO (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  obtain ⟨h1, h2, h3⟩ := isLineAt_lineAt hθ τ z
  let M : ℝ →+ WO S T := AddMonoidHom.mk' (fun t => actO S T g h (lineAt θ τ z t)) fun s t => by
    rw [map_add, actO_add]
  have hM : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) M := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      rw [compAt_actO, h3]
      split_ifs with hτ
      · rw [hτ, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hM]
  rfl

theorem om_dRho (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hW g h (isLineAt_lineAt hθ τ z).1 (isLineAt_lineAt hθ τ z).2.1 (isLineAt_lineAt hθ τ _).1
    (isLineAt_lineAt hθ τ _).2.1 (lineAt_actO hθ τ g h z) hf

theorem cplxO_move (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO sS' sT' (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) =
      compAt θ τ (mt T h) * cplxO sS sT z * compAt θ τ (mt S g⁻¹) := by
  have h1 : compAt θ τ (mt S g⁻¹) * sS' = sS * compAt θ τ (mt S g⁻¹) := by
    calc _ = compAt θ τ (mt S g⁻¹) * (sS' * compAt θ τ (mt S g)) * compAt θ τ (mt S g⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.mul_one]
      _ = _ := by rw [hS, ← Matrix.mul_assoc, compAt_mt_inv_mul, Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (sT' * compAt θ τ (mt T h)) * z * (compAt θ τ (mt S g⁻¹) * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, h1]; simp only [Matrix.mul_assoc]

end GlobalTheory.WeilVacMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiplesStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdele_compact_closed_multiples : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | exact GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | (intros; apply GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedZeroLocusGL
section
open NumberField IsDedekindDomain

namespace GlobalTheory.LocusOpenCompact

theorem continuous_aeval_comp {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ i, Continuous fun x => f x i) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf i)

theorem isClosed_zeroLocusGL {F : Type} [Field F] {n : ℕ}
    (S : Set (MvPolynomial (Fin n × Fin n) F)) (A : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (HeckeCharacterZeroLocus.zeroLocusGL S A) := by
  have e : HeckeCharacterZeroLocus.zeroLocusGL S A = ⋂ P ∈ S, {g : GL (Fin n) A | MvPolynomial.aeval
      (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0} := by
    ext g; simp only [HeckeCharacterZeroLocus.zeroLocusGL, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A) :=
    Units.continuous_val
  exact continuous_aeval_comp (X := GL (Fin n) A)
    (fun g (ij : Fin n × Fin n) => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2)
    (fun ij => hv.matrix_elem ij.1 ij.2) P

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S), ∃ U : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n S hS
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact F n
  refine ⟨U.subgroupOf _, hUo.preimage continuous_subtype_val, ?_⟩
  exact (isClosed_zeroLocusGL S (FiniteAdeleRing (𝓞 F) F)).isClosedEmbedding_subtypeVal.isCompact_preimage hUc

end GlobalTheory.LocusOpenCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrou
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralPointsCompact

theorem continuous_aeval_family {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ s, Continuous fun x => f x s) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf s)

theorem isClosed_of_equations {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Fintype ι] [DecidableEq ι]
    (S : Set (MvPolynomial (ι × ι) F)) (H : Subgroup (GL ι A))
    (hH : ∀ g, g ∈ H ↔ ∀ P ∈ S, MvPolynomial.aeval
      (fun ij : ι × ι => ((g : GL ι A) : Matrix ι ι A) ij.1 ij.2) P = 0) :
    IsClosed (H : Set (GL ι A)) := by
  have e : (H : Set (GL ι A)) = ⋂ P ∈ S, {g : GL ι A | MvPolynomial.aeval
      (fun ij : ι × ι => (g : Matrix ι ι A) ij.1 ij.2) P = 0} := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe]
    exact hH g
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  exact continuous_aeval_family (fun (g : GL ι A) (ij : ι × ι) => (g : Matrix ι ι A) ij.1 ij.2)
    (fun s => Units.continuous_val.matrix_elem s.1 s.2) P

theorem isCompact_integral_points : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  intro F _ _ n S H hH
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have hK := GlobalTheory.GLIntegral.isCompact_glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring F)
    (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have hc := isClosed_of_equations S H hH
  have h := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine (congrArg IsCompact (Set.ext fun u => ?_)).mpr h
  exact ⟨fun hu => ⟨fun i j => (hu i j).1, fun i j => (hu i j).2⟩,
    fun hu i j => ⟨hu.1 i j, hu.2 i j⟩⟩

end GlobalTheory.IntegralPointsCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFinitePartsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_congruence_ideles_and_real_finite_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  first | exact @GlobalTheory.IdeleParts.congr_open_and_parts | exact GlobalTheory.IdeleParts.congr_open_and_parts | (intros; apply GlobalTheory.IdeleParts.congr_open_and_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatOpen

open GlobalTheory.LatVac Topology

theorem isOpen_of_nhds {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup G'] (φ : G →+ G') (L : AddSubgroup G) (N : ℕ) (U : Set G) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ l ∈ L, φ (x - N • l) = 0) : IsOpen {x : G | ∃ l ∈ L, φ (x - N • l) = 0} := by
  let H : AddSubgroup G :=
    { carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add, e, e', add_zero]
      neg_mem' := by
        rintro x ⟨l, hl, e⟩
        refine ⟨-l, L.neg_mem hl, ?_⟩
        rw [show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }
  exact H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)

theorem isOpen_intAf (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem zero_mem_intAf (F : Type) [Field F] [NumberField F] : (0 : Af F) ∈ intAf F :=
  fun v => zero_mem (v.adicCompletionIntegers F)

variable {D : D7}

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem finPart_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι D.host.F D.host.E) (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).coord k z) ⊗ₜ[D.host.F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
  rw [show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show finPart D _ = _
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem nsmul_tmul_cancel {F A E : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [AddCommGroup E] [Module F E]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (a : A) (e : E) :
    N • ((algebraMap F A ((N * M : ℕ) : F)⁻¹ * a) ⊗ₜ[F] (M • e)) = a ⊗ₜ[F] e := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]

theorem isOpen_nsmul_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  intro D S T ΛS ΛT hS hT N hN
  classical
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) =>
    GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT hS.1 hT.1 (Matrix.single p.1 p.2.1 (b p.2.2))
  let f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun p x =>
    algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))
  have hf : ∀ p, Continuous (f p) := fun p => by
    have h1 : Continuous (B.coord p.2.2) := IsModuleTopology.continuous_of_linearMap _
    have h2 : Continuous (sndA D.host.F) := continuous_snd
    exact continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  have hf0 : ∀ p, f p 0 = 0 := fun p => by
    show _ * sndA D.host.F (B.coord p.2.2 0) = 0
    rw [LinearMap.map_zero, map_zero, mul_zero]
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finPart D).toAddMonoidHom.mapMatrix
  refine isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_
    show f p 0 ∈ intAf D.host.F
    rw [hf0]; exact zero_mem_intAf _
  · intro x hx
    refine ⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)),
      AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩
    rw [AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]
    ext i j
    rw [Matrix.sum_apply]
    have e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E),
        (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j =
        sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j) :=
      fun p => nsmul_tmul_cancel hN (hM p) _ _
    rw [Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type,
      Finset.sum_eq_single j]
    · simp only [Matrix.single_apply_same]
      exact finPart_eq_sum b (x i j)
    · intro j' _ hj
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]
    · simp
    · intro i' _ hi
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]
    · simp

end GlobalTheory.LatOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realSymplecticForm_alternating_invariant_definite : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  first | exact @GlobalTheory.RealSymplForm.form_alt_inv_def | exact GlobalTheory.RealSymplForm.form_alt_inv_def | (intros; apply GlobalTheory.RealSymplForm.form_alt_inv_def <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_finite_matrix_mem_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem | exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem | (intros; apply GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  first | exact @GlobalTheory.OrientedChar.char_symplOH | exact GlobalTheory.OrientedChar.char_symplOH | (intros; apply GlobalTheory.OrientedChar.char_symplOH <;> assumption)
end

