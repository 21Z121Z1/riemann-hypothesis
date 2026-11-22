import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpPull2Cob1
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

theorem inL_const {f : MvPowerSeries (Fin d) O} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) O} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) hf

theorem map_pull2 (h : O →+* E) (φ : Fin d → MvPowerSeries (Fin d) O)
    (t : MvPowerSeries (Fin d ⊕ Fin d) O) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    pull2 (fun i => map h (φ i)) (map h t) = map h (pull2 φ t) := by
  unfold pull2 at2
  rw [map_subst (CobCob.elim_has (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i)))]
  congr 1
  funext j
  cases j with
  | inl i => exact (map_inL h (φ i)).symm
  | inr i => exact (map_inR h (φ i)).symm

theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

theorem up_pull2_cob1 : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ), (∀ (φ : Fin d → MvPowerSeries (Fin d) O) (t : MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, constantCoeff (φ i) = 0) → pull2 (up E φ) (map (algebraMap O E) t) = map (algebraMap O E) (pull2 φ t)) ∧ ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (s : MvPowerSeries (Fin d) O), (∀ i, constantCoeff (μ i) = 0) → cob1 (up E μ) (map (algebraMap O E) s) = map (algebraMap O E) (cob1 μ s) := by
  intro O E _ _ _ d
  exact ⟨fun φ t hφ => map_pull2 (algebraMap O E) φ t hφ,
    fun μ s hμ => map_formalGroupLawCoboundaryOne_eq (algebraMap O E) μ s hμ⟩

end ExtCoeff

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem vact_vmul (N : ℕ) (D α : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    vact N (vmul e (α * D)) γ = vmul e (gact N D α γ * D) := by
  have h : gact N D α γ * D = α * D * redGL N γ := by
    simp only [gact]
    group
  rw [h]
  simp only [vact, vmul, Units.val_mul, Matrix.vecMul_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (D : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N), IsFam (gact N D) 2 (fun α => wp N (vmul e (α * D))) ∧ IsFam (gact N D) 3 (fun α => wpd N (vmul e (α * D))) := by
  intro N _ D e
  obtain ⟨h2, h3⟩ := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  refine ⟨fun α γ => ?_, fun α γ => ?_⟩
  · have h := h2 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h
  · have h := h3 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h

end GlobalTheory.WpFamGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAtSimpleZeroOfWeightedSqIntegrable
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem vanish_at_simple_zero_of_weighted_sq_integrable :
    ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O →
      DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O →
      ∀ u : V n → ℂ, ContinuousOn u O →
        ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ →
        u p = 0 := by
  intro n hn1 p O Z lam hO hpO hZ hZ0 hdet hlam u hu hint
  have hn : 0 < n := hn1
  by_contra hne
  have hOn : O ∈ 𝓝 p := hO.mem_nhds hpO

  have htr : Tendsto (fun z : V n => z + p) (𝓝 0) (𝓝 p) := by
    have := (continuous_add_right p).tendsto (0 : V n)
    simpa using this
  set a := ‖u p‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have ev1 : ∀ᶠ z in 𝓝 (0 : V n), a / 2 < ‖u (z + p)‖ := by
    have hc : Tendsto (fun v => ‖u v‖) (𝓝 p) (𝓝 a) := ((hu.continuousAt hOn).norm)
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev4 : ∀ᶠ z in 𝓝 (0 : V n), lam p - 1 < lam (z + p) := by
    have hc : Tendsto lam (𝓝 p) (𝓝 (lam p)) := hlam.continuousAt hOn
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev5 : ∀ᶠ z in 𝓝 (0 : V n), z + p ∈ O := htr.eventually hOn
  set σ : V n → V n := fun z => Z (z + p) with hσ
  have hσ0 : σ 0 = 0 := by simp [hσ, hZ0]
  have hσd : fderiv ℂ σ 0 = fderiv ℂ Z p := by
    rw [hσ, fderiv_comp_add_right]; simp
  obtain ⟨c, hc, ev2⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det hn hσ0 (hσd ▸ hdet)
  have hdiff : DifferentiableAt ℂ σ 0 := by
    have h1 : DifferentiableAt ℂ Z (0 + p) := by simpa using hZ.differentiableAt hOn
    exact h1.comp (0 : V n) ((differentiableAt_id).add_const p)
  obtain ⟨C, ev3⟩ : ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖σ z‖ ≤ C * ‖z‖ := by
    have h := hdiff.hasFDerivAt.isBigO_sub
    simp only [hσ0, sub_zero] at h
    obtain ⟨C, hC⟩ := h.bound
    exact ⟨C, hC⟩
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp
    (ev1.and (ev2.and (ev3.and (ev4.and ev5))))
  set Eb : ℝ := Real.exp (1 - lam p) with hEb
  set B : ℝ := C ^ 2 * Eb + 1 with hB
  have hB0 : 0 < B := by positivity
  set K : ℝ := (a / 2) ^ 2 * B ^ (-(n : ℝ)) with hK
  have hK0 : 0 < K := by positivity
  have hp : -(n : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
  set F : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (‖u v‖ ^ 2 *
    Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) with hF
  have hpt : ∀ z ∈ ball (0 : V n) δ0, z ≠ 0 →
      ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ F (z + p) := by
    intro z hz hz0
    obtain ⟨h1, h2, h3, h4, -⟩ := hall (by simpa using hz)
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set X := ‖Z (z + p)‖ ^ 2 * Real.exp (-lam (z + p)) with hX
    have hZpos : 0 < ‖Z (z + p)‖ := lt_of_lt_of_le (by positivity) h2
    have hXpos : 0 < X := by positivity
    have hexle : Real.exp (-lam (z + p)) ≤ Eb := Real.exp_le_exp.mpr (by linarith)
    have hXle : X ≤ B * ‖z‖ ^ 2 := by
      have hZle : ‖Z (z + p)‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ 2 := by
        have h0 : 0 ≤ C * ‖z‖ := le_trans (norm_nonneg _) h3
        calc ‖Z (z + p)‖ ^ 2 ≤ (C * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          _ = C ^ 2 * ‖z‖ ^ 2 := by ring
      calc X ≤ (C ^ 2 * ‖z‖ ^ 2) * Eb :=
            mul_le_mul hZle hexle (Real.exp_pos _).le (by positivity)
        _ ≤ B * ‖z‖ ^ 2 := by rw [hB]; nlinarith [sq_nonneg ‖z‖, sq_nonneg C, Real.exp_pos (1 - lam p)]
    have hw : Real.exp (-((n : ℝ) * Real.log X)) = X ^ (-(n : ℝ)) := by
      rw [Real.rpow_def_of_pos hXpos]; ring_nf
    show ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ENNReal.ofReal (‖u (z + p)‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log X)))
    rw [hw, ← ENNReal.ofReal_mul hK0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) ≤ X ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_nonpos hXpos hXle hp
    have hexp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) = B ^ (-(n : ℝ)) * ‖z‖ ^ (-2 * (n : ℝ)) := by
      rw [Real.mul_rpow hB0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      ring_nf
    have hu2 : (a / 2) ^ 2 ≤ ‖u (z + p)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    calc K * ‖z‖ ^ (-2 * (n : ℝ)) = (a / 2) ^ 2 * (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) := by rw [hexp, hK]; ring
      _ ≤ ‖u (z + p)‖ ^ 2 * X ^ (-(n : ℝ)) :=
        mul_le_mul hu2 hSp (by positivity) (by positivity)
  have hne0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)

  have hsubO : ∀ z ∈ ball (0 : V n) δ0, z + p ∈ O := fun z hz => (hall (by simpa using hz)).2.2.2.2
  have htrans : ∫⁻ z in ball (0 : V n) δ0, F (z + p) ≤ ∫⁻ v in O, F v := by
    have hind : ∀ z : V n, (ball p δ0).indicator F (z + p) = (ball (0 : V n) δ0).indicator (fun z => F (z + p)) z := by
      intro z
      have hm : z + p ∈ ball p δ0 ↔ z ∈ ball (0 : V n) δ0 := by
        simp [mem_ball, dist_eq_norm]
      by_cases hz : z ∈ ball (0 : V n) δ0
      · rw [Set.indicator_of_mem (hm.mpr hz), Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)), Set.indicator_of_notMem hz]
    have e1 : ∫⁻ z in ball (0 : V n) δ0, F (z + p) = ∫⁻ v in ball p δ0, F v := by
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
      simp_rw [← hind]
      exact lintegral_add_right_eq_self (μ := volume) ((ball p δ0).indicator F) p
    have hsb : ball p δ0 ⊆ O := by
      intro v hv
      have h1 : v - p ∈ ball (0 : V n) δ0 := by simpa [mem_ball, dist_eq_norm] using hv
      simpa using hsubO (v - p) h1
    rw [e1]
    exact lintegral_mono_set hsb
  have hlow : ENNReal.ofReal K * ∫⁻ z in ball (0 : V n) δ0, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ∫⁻ v in O, F v := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ htrans
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with z hz hz0
    exact hpt z hz hz0
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδ0, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK0).ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyFromFibres
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.Wedge

def alt2 {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

theorem alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl

theorem bijective_of_fibres {R B C : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup C]
    [Module R C] [Module.Finite R B] [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ q : PrimeSpectrum R, Function.Bijective (l.baseChange q.asIdeal.ResidueField)) :
    Function.Bijective l := by
  have hlt : ∀ q : PrimeSpectrum R, Function.Bijective (l.lTensor q.asIdeal.ResidueField) := by
    intro q
    have e : ⇑(l.lTensor q.asIdeal.ResidueField) = ⇑(l.baseChange q.asIdeal.ResidueField) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [e]; exact h q
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective l
      (fun m hm => (hlt ⟨m, hm.isPrime⟩).1)
    exact Function.LeftInverse.injective (g := r) fun x => LinearMap.congr_fun hr x
  · have hQ : Subsingleton (C ⧸ LinearMap.range l) := by
      apply GlobalTheory.subsingleton_of_residueField_fibres R
      intro q
      have h2 := (hlt q).2
      have h3 : Function.Surjective ((LinearMap.range l).mkQ.lTensor q.asIdeal.ResidueField) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun a b => ?_⟩
      have key : ∀ a : q.asIdeal.ResidueField ⊗[R] (C ⧸ LinearMap.range l), a = 0 := by
        intro a
        obtain ⟨x, rfl⟩ := h3 a
        obtain ⟨y, rfl⟩ := h2 x
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp]
        simp
      rw [key a, key b]
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hQ

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def wedgeMap (hsq : ∀ x : HO1 s, cup _ x x = 0) : ⋀[R]^2 (HO1 s) →ₗ[R] HO2 s :=
  exteriorPower.alternatingMapLinearEquiv (alt2 (cup _) hsq)

theorem wedgeMap_ιMulti (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by
  simp only [wedgeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alt2_apply]

theorem baseChange_wedgeMap_bijective (hsq : ∀ x : HO1 s, cup _ x x = 0) (k : Type) [CommRing k]
    [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X)
    (hpb : φ ≫ s = s' ≫ spMap (algebraMap R k))
    (e1 : k ⊗[R] HO1 s ≃ₗ[k] HO1 s') (he1 : ∀ c, e1 (1 ⊗ₜ c) = pullHO1 hpb c)
    (e2 : k ⊗[R] HO2 s ≃ₗ[k] HO2 s') (he2 : ∀ c, e2 (1 ⊗ₜ c) = pullHO2 hpb c)
    (w : ⋀[k]^2 (CatCoh.H1 (OAff s')) ≃ₗ[k] CatCoh.H2 (OAff s'))
    (hw : ∀ a b, w (exteriorPower.ιMulti k 2 ![a, b]) = cup _ a b) :
    Function.Bijective ((wedgeMap s hsq).baseChange k) := by
  have hcup := ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 R k X X' s s' (algebraMap R k) φ hpb).1
  let β := (GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange R (HO1 s) k) 2).equiv
  let T : k ⊗[R] ⋀[R]^2 (HO1 s) →ₗ[k] k ⊗[R] HO2 s :=
    e2.symm.toLinearMap ∘ₗ w.toLinearMap ∘ₗ exteriorPower.map 2 e1.toLinearMap ∘ₗ β.toLinearMap
  have hT : T = (wedgeMap s hsq).baseChange k := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hl : (T.restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 =
        (((wedgeMap s hsq).baseChange k).restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        wedgeMap_ιMulti, T, LinearEquiv.coe_coe, β, IsBaseChange.equiv_tmul, one_smul,
        GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.map_apply_ιMulti]
      have hv : (⇑e1 ∘ fun i => (1 : k) ⊗ₜ[R] v i) = ![pullHO1 hpb (v 0), pullHO1 hpb (v 1)] := by
        funext i; fin_cases i <;> simp [he1]
      rw [hv, hw, LinearEquiv.symm_apply_eq, he2, hcup]
    exact LinearMap.congr_fun hl x
  rw [← hT]
  have hm : Function.Bijective (exteriorPower.map 2 e1.toLinearMap) := by
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map 2 e1.symm.toLinearMap, ?_, ?_⟩
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
  exact e2.symm.bijective.comp (w.bijective.comp (hm.comp β.bijective))

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

theorem wedgeO_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  intro R _ X s hF1 hP1 hF2 hP2 hB1 hB2 hsq hfib
  have hbij : Function.Bijective (wedgeMap s hsq) := by
    refine bijective_of_fibres _ fun q => ?_
    obtain ⟨X', s', φ, hpb⟩ : ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp q.asIdeal.ResidueField) (φ : X' ⟶ X),
        IsPullback φ s' s (spMap (algebraMap R q.asIdeal.ResidueField)) :=
      ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    obtain ⟨e1, he1⟩ := hB1 _ _ _ _ hpb
    obtain ⟨e2, he2⟩ := hB2 _ _ _ _ hpb
    obtain ⟨w, hw⟩ := hfib _ _ _ _ hpb
    exact baseChange_wedgeMap_bijective s hsq _ X' s' φ hpb.w e1 he1 e2 he2 w hw
  exact ⟨LinearEquiv.ofBijective _ hbij, fun a b => by
    rw [LinearEquiv.ofBijective_apply, wedgeMap_ιMulti]; rfl⟩

end GlobalTheory.AbCoh.Wedge
end
end

