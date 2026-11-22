import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrandAestronglyMeasurable
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  first | exact @GlobalTheory.BesselPsi.psi_character | exact GlobalTheory.BesselPsi.psi_character | (intros; apply GlobalTheory.BesselPsi.psi_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : Mx k r), γ ∈ GG k r → (∀ F F' : Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ GG k r, F g = F' g) → B.JF D F γ = B.JF D F' γ ∧ (Integrable (JF.integrand D F γ) D.μSS → Integrable (JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : Mx k r → ℂ) (F : Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (B.sgs p γ) = φ γ) → B.JF D (fun g => φ g • F g) γ = φ γ • B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (JF.integrand D (F i) γ) D.μSS) → B.JF D (fun g => ∑ i, F i g) γ = ∑ i, B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  first | exact @GlobalTheory.BesselFunctionBasic.JF_basic | exact GlobalTheory.BesselFunctionBasic.JF_basic | (intros; apply GlobalTheory.BesselFunctionBasic.JF_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowthStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_side_growth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  first | exact @GlobalTheory.BesselLine.bessel_line | exact GlobalTheory.BesselLine.bessel_line | (intros; apply GlobalTheory.BesselLine.bessel_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SParamMeas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

noncomputable def conjInvM (a : B.Mat k r) (x : Mt k r) : Mt k r := a⁻¹ * Matrix.of x * a

theorem meas_mul {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.mulM (f x) (g x)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => Formalism.FourierDecayAlt.P.B7.invM (f x)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_lmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (lmulM a) μ μ :=
  ⟨meas_mul (f := fun _ => a) measurable_const measurable_id, h.left a ha⟩

theorem mp_rmul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {a : B.Mat k r} (ha : a ∈ U) :
    MeasurePreserving (B.rmulF a) μ μ :=
  ⟨meas_mul (g := fun _ => a) measurable_id measurable_const, h.right a ha⟩

theorem mp_inv {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (hU : B2.IsClosedSubgroup U) (h : B.IsHaarOn U μ) :
    MeasurePreserving (B2.invM (k := k) (r := r)) μ μ :=
  ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r U μ hU h⟩

theorem mp_conj {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjM a) μ μ :=
  ⟨meas_mul (g := fun _ => (a⁻¹ : B.Mat k r)) (meas_mul (f := fun _ => a) measurable_const measurable_id)
    measurable_const, Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μ hz hT h a ha⟩

theorem mp_conj_inv {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (h : B.IsHaarOn (Nset k r) μ) {a : B.Mat k r} (ha : a ∈ UWset k r z) :
    MeasurePreserving (conjInvM a) μ μ := by
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have := mp_conj hz hT h (hW.inv_mem a ha)
  have e : conjM (a⁻¹) = conjInvM a := by
    funext x
    unfold conjM conjInvM
    rw [Matrix.nonsing_inv_nonsing_inv _ (hW.unit a ha)]
  rwa [e] at this

end GlobalTheory.SParamMeas

open GlobalTheory.SParamMeas in

theorem GlobalTheory.sParam_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r z μW μN hk hz hT hW0 hN0
  have hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW0
  have hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN0
  have := hW0.1
  have := hN0.1
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have aW := Formalism.FourierDecayAlt.P.B7.ae_mem hW
  have aN := Formalism.FourierDecayAlt.P.B7.ae_mem hN
  have m1 : Measurable (Prod.fst : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_fst
  have m2 : Measurable (Prod.snd : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → _) := measurable_snd
  refine ⟨fun h₀ hh n₀ hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mp_rmul hW hh).prod ((mp_rmul hN hn).comp (mp_conj_inv hz hT hN hh))
  · have m3 : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm n₀ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    refine (mp_lmul hW hh).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.lmulM ((Matrix.of a)⁻¹ * n₀ * Matrix.of a) x)
      (meas_mul (meas_mul (meas_mul (meas_inv m1) m3) m1) m2) ?_
    filter_upwards [aW] with a ha
    refine hN.left _ ?_
    have := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (cW.inv_mem _ ha) n₀ hn).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha)] at this
  · refine (mp_inv cW hW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) (B2.invM x))
      (meas_mul (meas_mul m1 (meas_inv m2)) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact ((mp_conj hz hT hN ha).comp (mp_inv cN hN)).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) => Formalism.QuantumDeterminants.conjM (Matrix.of a) x)
      (meas_mul (meas_mul m1 m2) (meas_inv m1)) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj hz hT hN ha).map_eq
  · refine (MeasurePreserving.id μW).skew_product
      (g := fun (a x : Formalism.QuantumDeterminants.Mt k r) =>
        conjInvM (Matrix.of a) x)
      (meas_mul (meas_mul (meas_inv m1) m2) m1) ?_
    filter_upwards [aW] with a ha
    exact (mp_conj_inv hz hT hN ha).map_eq
  · exact (mp_inv cW hW).prod (mp_inv cN hN)
  · exact (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
section
noncomputable section

namespace GlobalTheory.RegularisedIntegral

section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dilate_subst (D : RealPlaceData k r Wp Wq) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SS k r → E} (hf : Integrable f D.μSS) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    Integrable (fun p => f (dilation₂ t p)) D.μSS ∧
      (∫ p, f (dilation₂ t p) ∂D.μSS) = ((t.1 * t.2) ^ kap k r)⁻¹ • ∫ p, f p ∂D.μSS := by
  have hm := map_measure_dilation_pair_eq_smul (dilation_jacobian_every_setting k r Wp Wq D) h1 h2
  have hf' : Integrable f (D.μSS.map (dilation₂ t)) := by
    rw [hm]
    exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine ⟨hf'.comp_measurable (dilation_action_measurable t), ?_⟩
  rw [← integral_map (dilation_action_measurable t).aemeasurable hf'.1, hm, integral_smul_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), mul_pow, mul_inv]

def kernel (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * Complex.exp (Complex.I * (phase D τ q.1 q.2 : ℂ))

variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

theorem betaInfTau_eq_kernel (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, (∫ t : ℝ × ℝ, kernel D F F' τ (p, t)) ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  have key := (bracket_calculus H hF hF' hp).2.2.2 (τ.1 * lam k r D.z (Matrix.of p.1.2))
    (-(τ.2 * lam k r D.z' (Matrix.of p.2.2)))
  have e : ∀ t : ℝ × ℝ, τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2) =
      τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := fun t => by ring
  simp only [kernel, phase, Bt_eq D F F' hp, e]
  rw [key, ← mul_assoc, ← Complex.ofReal_mul]
  have : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ *
      ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
    have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
    have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [this]
  simp

theorem kernel_slice (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (fun p => kernel D F F' τ (p, t)) =ᵐ[D.μSS] fun p =>
      (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) • (xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)) := by
  filter_upwards [ae_inSS D] with p hp
  obtain ⟨l1, l2⟩ := lam_dil dilation_unipotent_measure D hp h1 h2
  have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
  have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
  unfold kernel xiTau phase
  rw [Bt_eq D F F' hp, l1', l2', Complex.real_smul]
  unfold regBracket
  simp only [mul_assoc]
  ring

theorem kernel_slice_integral (D : RealPlaceData k r Wp Wq) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (τ : ℝ × ℝ)
    (hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS) (t : ℝ × ℝ) :
    Integrable (fun p => kernel D F F' τ (p, t)) D.μSS ∧
      (∫ p, kernel D F F' τ (p, t) ∂D.μSS) =
        ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS ∧
      (∫ p, ‖kernel D F F' τ (p, t)‖ ∂D.μSS) =
        |D.χ t.1| * |D.χ t.2| * ∫ p, ‖xiTau D τ p * Ph D F F' p‖ ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e := kernel_slice D F F' τ h1 h2
    obtain ⟨i1, s1⟩ := dilate_subst D hf h1 h2
    obtain ⟨-, s2⟩ := dilate_subst D hf.norm h1 h2
    have hpos : 0 < (t.1 * t.2) ^ kap k r := by positivity
    refine ⟨(i1.smul (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ)).congr e.symm, ?_, ?_⟩
    · rw [integral_congr_ae e, integral_smul, s1, smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one,
        Complex.real_smul]
    · have e' : (fun p => ‖kernel D F F' τ (p, t)‖) =ᵐ[D.μSS] fun p =>
          (|D.χ t.1| * |D.χ t.2| * (t.1 * t.2) ^ kap k r) * ‖xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)‖ := by
        filter_upwards [e] with p hp
        rw [hp, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpos]
      rw [integral_congr_ae e', integral_const_mul, s2, smul_eq_mul, ← mul_assoc, mul_assoc _ _ (_⁻¹),
        mul_inv_cancel₀ hpos.ne', mul_one]
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, kernel D F F' τ (p, t) = 0 := fun p => by
      unfold kernel
      rw [Bt_zero D F F' p ht, zero_mul]
    rw [← abs_mul, hz]
    simp [e]

theorem betaInfTau_eq_integral (hα : AB k r ≤ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F)
    (hcF' : InCC α 4 F') (hΦ : Integrable (Ph D F F') D.μSS) (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have H := sqIntegrable_of_threshold D hα
  have := sigmaFinite_μSS D
  have hξ : Continuous (xiTau D τ) := by
    unfold xiTau
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul (first_eigenvalue_continuous D)).sub (continuous_const.mul (continuous_lambda_second_coordinate D)))))
  have hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS := by
    refine hΦ.norm.mono' (hξ.aestronglyMeasurable.mul hΦ.1) (Eventually.of_forall fun p => ?_)
    unfold xiTau
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hs := kernel_slice_integral D τ hf
  have hmeas : AEStronglyMeasurable (kernel D F F' τ) (D.μSS.prod volume) := by
    unfold kernel
    refine ((cutBracket_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    have hp : Continuous fun q : SS k r × (ℝ × ℝ) => phase D τ q.1 q.2 :=
      (phase_continuous D).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hp))
  have hχ : Integrable D.χ := by
    by_contra h
    have := D.χ_int
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hK : Integrable (kernel D F F' τ) (D.μSS.prod volume) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun t => (hs t).1, ?_⟩
    simp only [fun t => (hs t).2.2]
    refine Integrable.mul_const ?_ _
    rw [Measure.volume_eq_prod]
    exact hχ.abs.mul_prod hχ.abs
  rw [betaInfTau_eq_kernel H hF hF', integral_integral_swap (f := fun p t => kernel D F F' τ (p, t)) hK]
  simp only [fun t => (hs t).2.1]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]

end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem betaInf_eq_integral :
    ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
      [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
      [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)),
      B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS →
      B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF hΦ => betaInfTau_eq_integral hA hF hF hΦ (1, 1)

end GlobalTheory.RegularisedIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimir
section
open Formalism.REAL

namespace GlobalTheory

theorem comatrix_last_row_inverts_casimir
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ)
    (hE : GlRel E) (hdet : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v)
    (hOm : ∀ y b, Om y b = ∑ c, E c b (y c)) :
    ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V),
      (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧
      ∀ u v, K u (PiLp.single 2 (Fin.last n) v) =
        qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by
  let Q : ℂ → Fin (n + 1) → Module.End ℂ V := fun u l =>
    (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : Module.End ℂ V) *
      qminor E Fin.castSucc (Fin.succAbove l) (u - 1)
  let K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V) := fun u =>
    ∑ l, (Q u l) ∘ₗ (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) l)
  have hK : ∀ u x, K u x = ∑ l, Q u l (x l) := by
    intro u x
    simp only [K, LinearMap.sum_apply, LinearMap.comp_apply, PiLp.projₗ_apply]
  refine ⟨K, fun u x => ?_, fun u v => ?_⟩
  · have h1 : ∀ l, ((u - 0) • x + Om x) l = ∑ c, Tm E u c l (x c) := by
      intro l
      simp only [Tm, sub_zero, PiLp.add_apply, PiLp.smul_apply, hOm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hK]
    simp only [h1, map_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ c, ∑ l, Q u l (Tm E u c l (x c)) =
        (if c = Fin.last n then qdet E u else 0 : Module.End ℂ V) (x c) := by
      intro c
      rw [← capelli_comatrix_last_row _ n E hE u c, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Q, Module.End.mul_apply]
    simp only [h2]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [hdet]
    · intro c _ hc
      simp [hc]
    · simp
  · rw [hK, Finset.sum_eq_single (Fin.last n)]
    · have h3 : qminor E Fin.castSucc Fin.castSucc (u - 1) =
          qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) := by
        simp only [qdet, qminor, Tm, id, Fin.castSucc_inj]
      have h4 : ((-1 : ℤ) ^ (n + n)) = 1 := by
        rw [← two_mul, pow_mul]; simp
      simp only [Q, Fin.succAbove_last, h3, Fin.val_last, h4, Int.cast_one, one_mul,
        PiLp.single_eq_same]
    · intro c _ hc
      simp [PiLp.single_eq_of_ne, hc]
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  first | exact @GlobalTheory.comatrix_picks_eigencomponent | exact GlobalTheory.comatrix_picks_eigencomponent | (intros; apply GlobalTheory.comatrix_picks_eigencomponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalueStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  first | exact @GlobalTheory.CapelliCasimir.cas_of_capelli | exact GlobalTheory.CapelliCasimir.cas_of_capelli | (intros; apply GlobalTheory.CapelliCasimir.cas_of_capelli <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetPropertiesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compoundMatrix_cauchyBinet_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ), cmp l (g * h) = cmp l g * cmp l h ∧ cmp l gᴴ = (cmp l g)ᴴ ∧ cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧ ∀ f : Fin l → Fin n → ℂ, cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  first | exact @GlobalTheory.compound_properties | exact GlobalTheory.compound_properties | (intros; apply GlobalTheory.compound_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapConditionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decayThresholds_of_spectralGapCondition : ∀ (k r : ℕ) (h : ℝ), GapOK k r h → JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  first | exact @GlobalTheory.thresholds_of_gapOK | exact GlobalTheory.thresholds_of_gapOK | (intros; apply GlobalTheory.thresholds_of_gapOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionBracket
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedBracket

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig GlobalTheory.DerivedAction

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem lie_bracket {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) :
    InLieHpk k r (X * Y - Y * X) := by
  have hLX : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  have e1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

theorem dsig_dsig (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) {F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (h1 : (1 : Mx k r) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH (Hpk k r) h → σ h v = F h) (L : Mx k r →L[ℝ] Mx k r) (hL : ∀ x, L x = x * Y) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) =
      fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, inUH (Hpk k r) g → σ g (dsig (k := k) (r := r) σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgH
    have h1 := hasDerivAt_local hY hU hg hF hfF hgH
    have h2 := hasDerivAt_apply hY hv (σ g)
    have e : (fun u : ℝ => σ (g * NormedSpace.exp ((u : ℂ) • Y)) v) =
        fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
      funext t
      rw [Hecke_multiplication k r ε mu H σ hσ g hgH _ (exp_mem hY t)]
      rfl
    rw [e] at h1
    simp only [hL]
    exact h2.unique h1
  have h := hasDerivAt_local (f := fun g => σ g (dsig (k := k) (r := r) σ Y v)) hX hU h1 hG hGe one_mem
  simp only [Matrix.one_mul] at h
  exact h.deriv

theorem dsig_bracket (hσ : IsDSHpk k r ε mu σ) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (dsig (k := k) (r := r) σ Y v) -
      dsig (k := k) (r := r) σ Y (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 one_mem
  have h := hasDerivAt_local (lie_bracket hX hY) hU h1 hF hfF one_mem
  simp only [Matrix.one_mul] at h
  have e : dsig (k := k) (r := r) σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h.deriv
  let L : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [dsig_dsig hσ hX hY hv hU h1 hF hfF L hL, dsig_dsig hσ hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem derived_action_bracket : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X Y, PI.UpqRep.InLieHpk k r X → PI.UpqRep.InLieHpk k r Y → ∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsig (k := k) (r := r) R.σ Y v) - PI.UpqRep.dsig (k := k) (r := r) R.σ Y (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (X * Y - Y * X) v :=
  fun _ _ _ _ _ _ hR _ _ hX hY _ hv => dsig_bracket hR.2 hX hY hv

end GlobalTheory.DerivedBracket
end
end

