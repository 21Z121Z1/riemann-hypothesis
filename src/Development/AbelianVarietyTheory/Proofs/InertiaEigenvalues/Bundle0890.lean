import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Pointwise

namespace GlobalTheory.ConjTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem symm_alg (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (x : E) :
    c.symm (algebraMap E Ω x) = algebraMap E Ω (τ.symm x) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

def conjG (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) :
    G E Ω →* G E Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := c.symm.trans (g.toRingEquiv.trans c)) (fun x => by
    simp only [RingEquiv.trans_apply, symm_alg c τ hτ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem conjG_apply (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g y = c (g (c.symm y)) := rfl

theorem conjG_apply_c (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g (c y) = c (g y) := by
  rw [conjG_apply, RingEquiv.symm_apply_apply]

theorem conjG_conjG_symm (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) : conjG c τ hτ (conjG c.symm τ.symm (symm_alg c τ hτ) g) = g := by
  ext y; simp [conjG_apply]

theorem conjG_continuous [Algebra.IsAlgebraic E Ω] (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) : Continuous (conjG c τ hτ) := by
  classical
  apply continuous_of_continuousAt_one (conjG c τ hτ)
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨S, hS, hSU⟩ := hU
  let b := Module.finBasis E S
  let s : Finset Ω := Finset.univ.image (fun i => c.symm (b i : Ω))
  have hfin : FiniteDimensional E (IntermediateField.adjoin E (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  show _ ∈ nhds (1 : G E Ω)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨_, hfin, fun g hg => hSU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hb : ∀ i, conjG c τ hτ g (b i : Ω) = b i := by
    intro i
    rw [conjG_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simp [s])), RingEquiv.apply_symm_apply]
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
    have := congrArg (fun z : S => (z : Ω)) (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, IntermediateField.coe_smul] at this
    exact this.symm
  rw [hx', map_sum]
  simp [map_smul, hb]

theorem mem_Dec_iff' {A : ValuationSubring Ω} {σ : G E Ω} :
    σ ∈ Dec (F := E) A ↔ ∀ y, σ y ∈ A ↔ y ∈ A := by
  constructor
  · exact fun h y => apply_mem_iff_of_mem_Dec h y
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem lt_one_transport {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hc, ← hc, map_eq_zero_iff _ c.injective]

theorem conjG_mem_Ine {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : g ∈ Ine (F := E) A) : conjG c τ hτ g ∈ Ine (F := E) A' := by
  have hsurj : ∀ y', ∃ y, y' = c y := fun y' => ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  refine ⟨?_, ?_⟩
  · have hD : g ∈ Dec (F := E) A := hg.1
    show conjG c τ hτ g ∈ Dec (F := E) A'
    rw [mem_Dec_iff'] at hD ⊢
    intro y'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← hc, ← hc, hD]
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← map_sub, ← lt_one_transport c hc]
    rw [ValuationSubring.valuation_le_one_iff, ← hc, ← ValuationSubring.valuation_le_one_iff] at hy'
    exact hg.2 y hy'

theorem conjG_mem_wild {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : ∀ y : Ω, y ≠ 0 → A.valuation (g y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A'.valuation (conjG c τ hτ g y / y - 1) < 1 := by
  intro y' hy'
  obtain ⟨y, rfl⟩ : ∃ y, y' = c y := ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  have hy : y ≠ 0 := fun h => hy' (by rw [h, map_zero])
  rw [conjG_apply_c, ← map_div₀, ← map_one c, ← map_sub, ← lt_one_transport c hc]
  exact hg y hy

end GlobalTheory.ConjTransport

namespace GlobalTheory

open GlobalTheory.ConjTransport

theorem conjGen_transport_exists : ∀ (D : D7) (w w' : PlE D.host) (γ : GE D.nd), IsConjPl D.host w w' →
    TameGenAt (D.nd.plOm.1 w) γ → ∃ γ' : GE D.nd, IsConjGen D w w' γ γ' ∧ TameGenAt (D.nd.plOm.1 w') γ' := by
  intro D w w' γ hww hγ
  let τ : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E)
  let c₀ : D.nd.Om ≃+* D.nd.Om := IsAlgClosure.equivOfEquiv D.nd.Om D.nd.Om τ
  have hc₀ : ∀ x, c₀ (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap D.nd.Om D.nd.Om τ
  set A := D.nd.plOm.1 w with hAdef
  set A' := D.nd.plOm.1 w' with hA'def
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have hA' : IsPlaceOver A' w' := D.nd.plOm.2 w'
  let B : ValuationSubring D.nd.Om := A.comap (c₀.symm : D.nd.Om →+* D.nd.Om)
  have hAB : ∀ y, y ∈ A ↔ c₀ y ∈ B := fun y => by
    show y ∈ A ↔ c₀.symm (c₀ y) ∈ A
    rw [RingEquiv.symm_apply_apply]
  have hB : IsPlaceOver B w' := by
    intro x
    let x'' : 𝓞 D.host.E := ⟨τ.symm x, (x.isIntegral_coe).map (τ.symm : D.host.E →+* D.host.E).toIntAlgHom⟩
    have h1 : algebraMap D.host.E D.nd.Om (x : D.host.E) = c₀ (algebraMap D.host.E D.nd.Om (x'' : D.host.E)) := by
      rw [hc₀]; congr 1
      show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm
    rw [h1, ← lt_one_transport c₀ hAB, hA x'']
    exact hww x'' x (by show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hA'
  let c : D.nd.Om ≃+* D.nd.Om := c₀.trans σ.toRingEquiv
  have hcE : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) := by
    intro x
    show σ (c₀ _) = _
    rw [hc₀, AlgEquiv.commutes]
  have hcA : ∀ y, y ∈ A ↔ c y ∈ A' := by
    intro y
    rw [hAB, ← hσ, ← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ), AlgEquiv.smul_def]
    rfl
  have hcA' : ∀ y, y ∈ A' ↔ c.symm y ∈ A := by
    intro y
    rw [hcA, RingEquiv.apply_symm_apply]
  refine ⟨conjG c τ hcE γ, ⟨c, fun x => hcE x, hcA, fun y => conjG_apply_c c τ hcE γ y⟩, ?_⟩
  refine ⟨conjG_mem_Ine c τ hcE hcA hγ.1, ?_⟩
  intro h hh
  have h1 := hγ.2 (conjG_mem_Ine c.symm τ.symm (symm_alg c τ hcE) hcA' hh)
  rw [← conjG_conjG_symm c τ hcE h]
  refine closure_mono ?_ (image_closure_subset_closure_image (conjG_continuous c τ hcE) ⟨_, h1, rfl⟩)
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  refine SetLike.coe_subset_coe.mpr (Subgroup.closure_mono ?_)
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | hg
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjG_mem_wild c τ hcE hcA hg)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
section
noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.ThetaPoisson GroundTheory.Global GlobalTheory.RSThetaLow
open GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.RSResidue

theorem continuous_integral_of_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] {K : Set Y} (hK : IsCompact K)
    {F : X → Y → ℂ} (hF : Continuous fun p : X × Y => F p.1 p.2) (h0 : ∀ x, ∀ y ∉ K, F x y = 0) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hI : (fun x => ∫ y, F x y ∂ν) = fun x => ∫ y in K, F x y ∂ν :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [hI]
  have hc : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (F x) K ν := fun x => (hc x).continuousOn.integrableOn_compact hK
  set m : ℝ := ν.real K with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hδ : 0 < ε / (m + 1) := by positivity
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, dist (F x y) (F x₀ y) < ε / (m + 1) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := Metric.tendsto_nhds.1 (hF.continuousAt (x := (x₀, y))) (ε / (m + 1) / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.1 ((hc x₀).comp continuous_snd |>.continuousAt (x := (x₀, y)))
      (ε / (m + 1) / 2) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F z.1 z.2) (F x₀ z.2) ≤ dist (F z.1 z.2) (F x₀ y) + dist (F x₀ z.2) (F x₀ y) :=
          dist_triangle_right _ _ _
      _ < ε / (m + 1) / 2 + ε / (m + 1) / 2 := add_lt_add hz1 hz2
      _ = ε / (m + 1) := by ring
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have h3 : ‖∫ y in K, (F x y - F x₀ y) ∂ν‖ ≤ ε / (m + 1) * m :=
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y hy => by
      rw [← dist_eq_norm]; exact (hx y hy).le
  refine h3.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero_eq {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) : ∃ c : ℂ, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 = (∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a) * c := by
  refine ⟨(finiteAdelicChar E (∑ i, η i * pFin E ((0 : Fin a → Ad E) i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E ((0 : Fin a → Ad E) i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ), fun g => ?_⟩
  have h := rsHat_eq (ℓ := ℓ) J η F F' hΦ g 0
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have hF : infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E ((0 : Fin a → Ad E) i)) =
      ∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a := by
    rw [e, infFourier]
    simp
  change rsHat ℓ F.1 F'.1 Φ J η g 0 = _
  rw [h, hF]
  ring

variable {ω : HChar E}

theorem rsHat_zero_props (hω : ω.IsUnitary) {φ φ' : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : φ'.1 ∈ bddForms E a ω)
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) :
    Continuous (fun g : GA E a => adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0) ∧
    (∃ C : ℝ, ∀ g : GA E a, ‖adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0‖ ≤ C) ∧
    ∀ γ ∈ latticeGL E a, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g)) 0 = adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 := by
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hc]
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc, norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ hγ g
    have hL : ∀ x, φ.1 (γ * x) * conj (φ'.1 (γ * x)) = φ.1 x * conj (φ'.1 x) := fun x =>
      leftInv_mul_conj hω h h' γ hγ x
    have e : rsInf ℓ φ.1 φ'.1 Φ (γ * g) = rsInf ℓ φ.1 φ'.1 Φ g := funext fun u => by
      rw [rsInf, rsInf, mul_assoc γ g, hL]
    have e' : rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y => by
      rw [rsPsi, rsPsi, e]
    rw [e']

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

end GlobalTheory.RSResidue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuUnrTie

theorem eq_of_over_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, h⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem unrAt_inv {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := fun x hx => by
  rw [HChar.loc_inv, h x hx, inv_one]

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    GlobalTheory.HubX.MuUnr D := by
  intro _ hL D P i hl w hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  rw [P.chr.unr_iff, P.chr.tw, P.chr.muC i j hjj, P.chr.etaTinv]
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ (unrAt_inv (P.cf.isEta.unr w))
  unfold TupTied.tup
  refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
  · refine (P.cf.isMu0 j).unr w fun k hk => ?_
    have e := eq_of_over_two hlp (D.host.g_prime k) w hw hk
    apply hl
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  · rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
    refine GlobalTheory.MuTameQS.unrAt_mul ?_ ?_
    · unfold CharFrame.delAt
      split_ifs with h
      · refine P.cf.isDel'.unr w fun ho => D.host.pde_ne ?_
        rw [← h]
        exact eq_of_over_two hlp D.host.pde'_prime w hw ho
      · refine P.cf.isDel.unr w fun ho => h ?_
        exact eq_of_over_two hlp D.host.pde_prime w hw ho
    · have hpsi := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
      rw [D.nd.w_l i, ← P.Q_eq i] at hpsi
      exact (hpsi.ram w).2 fun hq => D.nd.SQ_l i w (Or.inr hq) hw

end GlobalTheory.MuUnrTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositiveStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cellPart_unfoldedIntegral_positive : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (φ : GA E (m + 1) → ℂ)
    (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    0 < N → (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ (Pi.single (Fin.last m) 1) ≠ 0 →
    Continuous (GlobalTheory.JSW.whit φ) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    b 1 = 1 → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) →
    (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
  first | exact @GlobalTheory.CellBump.exists_cellPart_unfoldedIntegral_positive_alt | exact GlobalTheory.CellBump.exists_cellPart_unfoldedIntegral_positive_alt | (intros; apply GlobalTheory.CellBump.exists_cellPart_unfoldedIntegral_positive_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVector
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w
    rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCellStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  first | exact @GlobalTheory.RSParams.exists_level_nat_bump | exact GlobalTheory.RSParams.exists_level_nat_bump | (intros; apply GlobalTheory.RSParams.exists_level_nat_bump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMulStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  first | exact @GlobalTheory.CellEvalDet.detPow_tl_mul | exact GlobalTheory.CellEvalDet.detPow_tl_mul | (intros; apply GlobalTheory.CellEvalDet.detPow_tl_mul <;> assumption)
end

