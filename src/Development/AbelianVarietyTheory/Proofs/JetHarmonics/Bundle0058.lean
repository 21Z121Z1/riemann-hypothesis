import Mathlib
import Formalism.HermitianCurvature.Bundle0005
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleCapelli
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ _ V₂ _ _ _ n E₁ E₂ m g₁ g₂ i₁ i₂ c₁ c₂
  haveI := i₁.1
  haveI := i₂.1
  obtain ⟨ν₁, v₁, -, hv₁, hw₁, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₁ n E₁ g₁ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨ν₂, v₂, -, hv₂, hw₂, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₂ n E₂ g₂ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have p₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₁ (mem_CapSp.2 fun w => c₁ w v₁) hv₁ hw₁
  have p₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₂ (mem_CapSp.2 fun w => c₂ w v₂) hv₂ hw₂
  have s₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₁ n E₁ ν₁ v₁ g₁ hw₁ hv₁)
  have s₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₂ n E₂ ν₂ v₂ g₂ hw₂ hv₂)
  have h := (Formalism.FourierDecayAlt.P.separating_polynomials n _ _ (fun w => (p₁ w).symm.trans (p₂ w)) s₂).2 s₁
  have hν : ν₁ = ν₂ := by
    funext j
    exact sub_left_injective (congrFun h j)
  subst hν
  exact exists_linearEquiv_of_irreducible_isHW V₁ V₂ n E₁ E₂ ν₁ v₁ v₂ g₁ g₂ i₁.2 i₂.2 hw₁ hw₂ hv₁ hv₂

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoff
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory
namespace QuotCutoff

def mulM {m : ℕ} (a b : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a * Matrix.of b) i j

lemma continuous_mulM {m : ℕ} : Continuous (fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma mulM_assoc {m : ℕ} (a b c : PI.MtM m) : mulM (mulM a b) c = mulM a (mulM b c) :=
  Matrix.mul_assoc (Matrix.of a) (Matrix.of b) (Matrix.of c)

lemma continuous_mulM_left {m : ℕ} (x : PI.MtM m) : Continuous (fun s => mulM s x) :=
  continuous_mulM.comp (continuous_id.prodMk continuous_const)

def invM {m : ℕ} (a : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of a)⁻¹ i j

lemma continuousAt_invM {m : ℕ} (a : PI.MtM m) (h : Matrix.of a * (Matrix.of a)⁻¹ = 1) :
    ContinuousAt invM a := by
  have hu : IsUnit (Matrix.of a).det := Matrix.isUnit_det_of_right_inverse h
  have h1 : ContinuousAt Ring.inverse (Matrix.of a).det := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact continuousAt_matrix_inv (Matrix.of a) h1

def piece {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (j : ℕ) : Set (PI.MtM m) :=
  {x | Matrix.of x ∈ G} ∩ Metric.closedBall 0 (j : ℝ)

lemma isClosed_of {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) :
    IsClosed {x : PI.MtM m | Matrix.of x ∈ G} := hG

lemma isCompact_piece {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsClosed G) (j : ℕ) :
    IsCompact (piece G j) :=
  (isCompact_closedBall _ _).inter_left (isClosed_of hG)

lemma exists_bound {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) (j : ℕ) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ x : PI.MtM m, μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ c := by
  have hC := isCompact_piece hG.1 j
  set K : Set (PI.MtM m) :=
    (fun p : PI.MtM m × PI.MtM m => mulM p.1 (invM p.2)) '' (piece G j ×ˢ piece G j) with hK
  have hKc : IsCompact K := by
    refine (hC.prod hC).image_of_continuousOn ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun p : PI.MtM m × PI.MtM m => invM p.2) (a, b) :=
      ContinuousAt.comp (g := invM) (f := fun p : PI.MtM m × PI.MtM m => p.2) (x := (a, b))
        (continuousAt_invM b (hG.2.2.2 (Matrix.of b) hb.1).2) continuousAt_snd
    exact ContinuousAt.comp (g := fun p : PI.MtM m × PI.MtM m => mulM p.1 p.2)
      (f := fun p : PI.MtM m × PI.MtM m => (p.1, invM p.2))
      continuous_mulM.continuousAt (continuousAt_fst.prodMk h1)
  have hKS : IsCompact (K ∩ {x | Matrix.of x ∈ S}) := hKc.inter_right (isClosed_of hS.1)
  refine ⟨μ (K ∩ {x | Matrix.of x ∈ S}),
    (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.1 _ hKS (fun x hx => hx.2), fun x => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hA : MeasurableSet ((fun s => mulM s x) ⁻¹' piece G j) :=
    (hC.isClosed.preimage (continuous_mulM_left x)).measurableSet
  by_cases h : ∃ s₀ : PI.MtM m, Matrix.of s₀ ∈ S ∧ mulM s₀ x ∈ piece G j
  · obtain ⟨s₀, hs₀, hx⟩ := h
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    rw [← h1, Measure.map_apply (continuous_mulM_left s₀).measurable hA, h1]
    refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    refine ⟨⟨(mulM t (mulM s₀ x), mulM s₀ x), ⟨?_, hx⟩, ?_⟩, ht⟩
    · rw [← mulM_assoc]; exact hti
    · have h2 := (hG.2.2.2 (Matrix.of (mulM s₀ x)) hx.1).2
      change Matrix.of t * Matrix.of (mulM s₀ x) * (Matrix.of (mulM s₀ x))⁻¹ = Matrix.of t
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  · refine measure_mono_ae ?_
    filter_upwards [hae] with t ht hti
    exact absurd ⟨t, ht, hti⟩ h

lemma exists_pos {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (x : PI.MtM m) (hx : Matrix.of x ∈ G) :
    ∃ j : ℕ, 0 < μ ((fun s => mulM s x) ⁻¹' piece G j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
  refine ⟨j, ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  have hU : IsOpen ((fun s => mulM s x) ⁻¹' Metric.ball 0 (j : ℝ)) :=
    Metric.isOpen_ball.preimage (continuous_mulM_left x)
  have h1 : mulM (Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ)) x = x :=
    Matrix.one_mul (Matrix.of x)
  have := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos m S μ hS hμ).2.2 _ hU
    ⟨Matrix.of.symm (1 : Matrix (Fin m) (Fin m) ℂ), by
      rw [Set.mem_preimage, h1]; simpa using hj, hS.2.1⟩
  refine this.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with t ht hti
  exact ⟨hG.2.2.1 _ (hSG ht) _ hx, Metric.ball_subset_closedBall hti⟩

lemma exists_precutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (PI.MtM m)}
    (hG : PI.IsMatGroup G) (hS : PI.IsMatGroup S) (hSG : S ⊆ G) (hμ : PI.IsHaarOnM S μ)
    (hR : PI.IsRightInvM S μ) :
    ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (mulM s x) ∂μ ≠ 0 ∧ ∫⁻ s, φ (mulM s x) ∂μ ≠ ⊤ := by
  choose c hc hb using exists_bound hG hS hμ hR
  have hP : ∀ j, MeasurableSet (piece G j) := fun j => (isCompact_piece hG.1 j).measurableSet
  set w : ℕ → ℝ≥0∞ := fun j => (2⁻¹ : ℝ≥0∞) ^ j * (1 + c j)⁻¹ with hw
  have hmeas : ∀ j, Measurable ((piece G j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hP j)
  have hI : ∀ x : PI.MtM m, ∫⁻ s, (∑' j, (piece G j).indicator (fun _ => w j) (mulM s x)) ∂μ
      = ∑' j, w j * μ ((fun s => mulM s x) ⁻¹' piece G j) := by
    intro x
    rw [lintegral_tsum (f := fun j s => (piece G j).indicator (fun _ => w j) (mulM s x))
      (fun j => ((hmeas j).comp (continuous_mulM_left x).measurable).aemeasurable)]
    congr 1
    ext j
    rw [← lintegral_indicator_const ((continuous_mulM_left x).measurable (hP j))]
    rfl
  refine ⟨fun y => ∑' j, (piece G j).indicator (fun _ => w j) y,
    Measurable.ennreal_tsum hmeas, fun x hx => ?_⟩
  rw [hI x]
  constructor
  · obtain ⟨j, hj⟩ := exists_pos hG hS hSG hμ x hx
    intro h
    rw [ENNReal.tsum_eq_zero] at h
    have hwj : w j ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by simp)) ?_
      rw [ENNReal.inv_ne_zero]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, (hc j).ne⟩
    exact mul_ne_zero hwj hj.ne' (h j)
  · refine ne_top_of_le_ne_top (b := ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ?_
      (ENNReal.tsum_le_tsum fun j => ?_)
    · rw [ENNReal.tsum_geometric]
      simp
    · have h1 : (1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j) ≤ 1 := by
        calc _ ≤ (1 + c j)⁻¹ * (1 + c j) := by
              gcongr
              exact (hb j x).trans le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
      calc w j * _ = (2⁻¹ : ℝ≥0∞) ^ j * ((1 + c j)⁻¹ * μ ((fun s => mulM s x) ⁻¹' piece G j)) :=
            mul_assoc _ _ _
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ j * 1 := by gcongr
        _ = _ := mul_one _

end QuotCutoff

open QuotCutoff in

theorem exists_normalised_cutoff : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  intro m G S μ hG hS hSG hμ hR
  obtain ⟨φ, hφ, hI⟩ := exists_precutoff hG hS hSG hμ hR
  haveI := hμ.1
  set I : PI.MtM m → ℝ≥0∞ := fun x => ∫⁻ s, φ (mulM s x) ∂μ with hIdef
  have hIm : Measurable I :=
    Measurable.lintegral_prod_left' (f := fun p : PI.MtM m × PI.MtM m => φ (mulM p.1 p.2))
      (hφ.comp continuous_mulM.measurable)
  have hinv : ∀ s₀ x : PI.MtM m, Matrix.of s₀ ∈ S → I (mulM s₀ x) = I x := by
    intro s₀ x hs₀
    have h1 : μ.map (fun s => mulM s s₀) = μ := hR _ hs₀
    have h2 := lintegral_map (μ := μ) (f := fun s => φ (mulM s x))
      (hφ.comp (continuous_mulM_left x).measurable) (continuous_mulM_left s₀).measurable
    rw [h1] at h2
    simp only [hIdef]
    rw [h2]
    simp only [mulM_assoc]
  refine ⟨fun y => φ y * (I y)⁻¹, hφ.mul hIm.inv, fun x hx => ?_⟩
  have hae : ∀ᵐ s ∂μ, Matrix.of s ∈ S := hμ.2.2.1
  calc ∫⁻ s, φ (mulM s x) * (I (mulM s x))⁻¹ ∂μ = ∫⁻ s, φ (mulM s x) * (I x)⁻¹ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        rw [hinv s x hs]
    _ = I x * (I x)⁻¹ := lintegral_mul_const _ (hφ.comp (continuous_mulM_left x).measurable)
    _ = 1 := ENNReal.mul_inv_cancel (hI x hx).1 (hI x hx).2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem family_through_discreteSeries : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r), Num k r lam u b bv ga h q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 k r) lam →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R 0 = R0 := by
  intro hH k r lam u b bv ga h q0 R0 hN hR0
  classical
  have hex : DSExist := hH.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have hfam := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = 0 → R = R0) := by
    intro ν
    by_cases h0 : ν = 0
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      simpa using hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR 0).2 rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagFix

open Formalism.QuantumDeterminants

theorem wedge_eq_of_mul {n l : ℕ} (f f' : Fin l → Fin n → ℂ) (U : Matrix (Fin l) (Fin l) ℂ)
    (hU0 : ∀ c a, a < c → U c a = 0) (hU1 : ∀ c, U c c = 1)
    (h : ∀ i a, f' a i = ∑ c, f c i * U c a) : wedge f' = wedge f := by
  have dU : U.det = 1 := by
    have ht : U.IsUpperTriangular := fun i j hij => hU0 i j hij
    rw [det_of_isUpperTriangular ht]
    exact Finset.prod_eq_one (fun i _ => hU1 i)
  funext I
  have e : (Matrix.of fun a b : Fin l => f' b (I.1.orderEmbOfFin I.2 a)) =
      (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a)) * U := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, h]
  simp only [wedge]
  rw [e, det_mul, dU, mul_one]

theorem flat_eq (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : flat k r f = star f ᵥ* Hpk k r := by
  funext c
  simp only [flat, herm]
  rw [dotProduct_mulVec, dotProduct_single, mul_one]

theorem dual_fix (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : sᴴ * Hpk k r * s = Hpk k r)
    (hf : s *ᵥ f = f) : dualM s *ᵥ flat k r f = flat k r f := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have hl : (Hpk k r * sᴴ * Hpk k r) * s = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, h2]
  rw [flat_eq, dualM, mulVec_transpose, Matrix.inv_eq_left_inv hl, vecMul_vecMul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, ← vecMul_vecMul, ← star_mulVec, hf]

theorem fixes_wedge_and_form : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z,
      cmp (r + 1) s *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (wedge (Formalism.QuantumDeterminants.fvec k r z)) ∧
      dualM s *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) := by
  intro k r z hz s hs
  obtain ⟨U, hU0, hU1, hF⟩ := S_F hz hs
  have key : ∀ i a, (s *ᵥ fvec k r z a) i = ∑ c, fvec k r z c i * U c a := by
    intro i a
    have := congrFun (congrFun hF i) a
    simpa [Matrix.mul_apply, Fm, mulVec, dotProduct] using this
  refine ⟨?_, dual_fix k r _ s (Sset_UH hs) ?_⟩
  · rw [(GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ (r + 1) s s).2.2.2]
    exact wedge_eq_of_mul _ _ U hU0 hU1 key
  · funext i
    rw [key, Finset.sum_eq_single 0, hU1, mul_one]
    · intro c _ hc
      rw [hU0 c 0 (Fin.pos_of_ne_zero hc), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlowProgrammeBoundsAndLowLevelOptimumStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flow_programme_bounds_and_low_level_optimum : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
  rho l * ∑ a, D a ≤ Fnum l d D ∧ (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧ Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
  ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧ gam l * ∑ a, D a - flowVal d x ≤ Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  first | exact @GlobalTheory.FlowProgrammeFacts.main | exact GlobalTheory.FlowProgrammeFacts.main | (intros; apply GlobalTheory.FlowProgrammeFacts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.gN_rpow_neg_integrable_haar : _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG
  intro k r μG A hμ hA
  have hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG :=
    (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ
  have hvol := _root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
  unfold _root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol
  obtain ⟨C, hC⟩ := hvol k r μG hW
  have hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := by
    unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hμ
    exact ae_iff.2 hμ.2.2.1
  set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef
  have hNcont : Continuous N := by
    simp only [hNdef]
    unfold _root_.Formalism.FourierDecayAlt.B.gN
    fun_prop
  have hNm : Measurable N := hNcont.measurable
  have h1 : ∀ᵐ x ∂μG, 1 ≤ N x := hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1) := by positivity
  have hAd : 2 * ((k:ℝ) + r) * (r + 1) < A := by
    have : _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring
    rw [this] at hA
    linarith
  set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := (2:ℝ) ^ (d - A) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)} := fun n ↦
    measurableSet_le hNm measurable_const
  have hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)}
      ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d) := by
    intro n
    refine (hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d)
      = C' * 2 ^ d * q ^ n := by
    intro n
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq,
      ← Real.rpow_mul_natCast (by norm_num)]
    have e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)
        = 2 ^ d * 2 ^ ((d - A) * n) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc ((2:ℝ) ^ ((n:ℝ) * -A)) * (C' * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d))
        = C' * ((2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)) := by ring
      _ = C' * 2 ^ d * 2 ^ ((d - A) * n) := by rw [e]; ring
  have hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ,
      {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))
  refine ⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖_root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)‖ₑ ∂μG
      = ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μG := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.enorm_eq_ofReal
          (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]
    _ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator
          (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← hkey n, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hvolS n
    _ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeFRep

theorem entry_le_hs {k r : ℕ} (g : Mx k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem isFRep_cmp (k r l : ℕ) :
    IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  have hm : ∀ g h : Mx k r, cmp l (g * h) = cmp l g * cmp l h := fun g h => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g h).1
  have hc : ∀ g : Mx k r, cmp l gᴴ = (cmp l g)ᴴ := fun g => (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l g g).2.1
  have h1 : cmp l (1 : Mx k r) = 1 := (GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ l 1 1).2.2.1
  refine ⟨?_, ?_, h1, fun g _ h _ => hm g h, ?_, ?_, ⟨(l.factorial : ℝ), ?_⟩, ?_⟩
  · rw [← hc, PI.StabPairsW.hpk_conjTranspose]
  · rw [← hm, PI.StabPairsW.hpk_mul_self, h1]
  · intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [← hc, ← hm, ← hm, hg']
  · intro I J
    apply Continuous.continuousOn
    unfold BranchingSupport.cmp
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · intro g _ I J
    have := Matrix.det_le (A := g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2))
      (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (x := B.gN g) (fun i j => entry_le_hs g _ _)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · intro g _ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← hc, ← hm, hu, h1]

end GlobalTheory.WedgeFRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLeStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_level_tail_mul_log_primes_le : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  first | exact @GlobalTheory.TailPrimeSum.main | exact GlobalTheory.TailPrimeSum.main | (intros; apply GlobalTheory.TailPrimeSum.main <;> assumption)
end

