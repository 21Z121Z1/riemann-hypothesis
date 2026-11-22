import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0005
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModel
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hDS hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hm : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    simpa [Set.compl_setOf] using this
  have key : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := hφ
    have := hc.aestronglyMeasurable (μ := νq) hm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}) hae] at this
  refine ⟨hae, key, fun a => ?_, fun l hl w hw => ?_⟩
  · exact (key ℝ (fun g => lenA k r z g a) (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · haveI : SecondCountableTopology Wp := by
      haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp
      infer_instance
    exact key Wp (fun g => l (R.σ g w))
      (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hDS Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModule
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * (X * Y) * Q := by
    intro X Y
    calc (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * X * (Q * Q⁻¹) * Y * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (X * Y) * Q := by
          rw [hQQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key, key, ← Matrix.sub_mul, ← Matrix.mul_sub]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp [Matrix.single_mul_single_same, Matrix.mul_sub, Matrix.sub_mul]
  · subst hbc
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Matrix.mul_sub, Matrix.sub_mul]
  · subst hda
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Matrix.mul_sub, Matrix.sub_mul]
  · simp [Matrix.single_mul_single_of_ne, hbc, hda]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hR Q hQ
  obtain ⟨hsm, hlinv, hlinY, -, hcomm, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hzero : ∀ Y : Mx k r, R.dC Y 0 = 0 := by
    intro Y
    have h := hlinv Y 1 0 R.smSub.zero_mem 0 R.smSub.zero_mem
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := by
    intro v hv
    have h := hlinY 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z : Mx k r, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := by
    intro Y Z v hv
    have h := hlinY Z Y (-1) v hv
    rw [neg_one_smul, neg_add_eq_sub, neg_one_smul, neg_add_eq_sub] at h
    exact h
  let Em : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hsm _ v v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) 1 v v.2 w w.2
        simpa using h
      map_smul' := fun c v => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) c v v.2 0 R.smSub.zero_mem
        simpa [hzero] using h }
  have hE : ∀ a b (v : R.smSub), ((Em a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v :=
    fun _ _ _ => rfl
  refine ⟨Em, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hv : (v : R.H) ∈ R.sm := v.2
  have key := hcomm (Q⁻¹ * Matrix.single a b 1 * Q) (Q⁻¹ * Matrix.single c d 1 * Q) v hv
  rw [conj_single_comm Q hQ a b c d, hsub _ _ _ hv] at key
  split_ifs at key ⊢ <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE, LinearMap.zero_apply,
      Submodule.coe_zero, sub_zero, zero_sub, hY0 _ hv] at key ⊢ <;>
    exact key

end GlobalTheory
end Gp91
end

