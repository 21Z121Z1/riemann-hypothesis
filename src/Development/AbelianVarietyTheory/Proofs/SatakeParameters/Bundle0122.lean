import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatIntFacts

theorem intValuation_uniformiser {R : Type} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R) {ϖ : R}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem exists_left_inverse {R : Type} [CommRing R] {n : ℕ} (ε : R) (B C : Matrix (Fin n) (Fin n) R)
    (hε : ε * ε = ε) (h : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) :
    ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) R,
      (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
        ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    intro X Y
    have e1 : ε * (1 - ε) = 0 := by linear_combination -hε
    have e2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    simp only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]
  have h1 := key B C
  rw [h, ← add_smul, add_sub_cancel, one_smul] at h1
  have h2 := mul_eq_one_comm.1 h1
  rw [key] at h2
  rw [eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]

set_option maxHeartbeats 1000000 in

theorem int_facts : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V
  refine ⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩
  · intro P e ϖ ϖ' he h1 h2 h1' h2' n
    have hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1 := by
      have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)
      have v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')
      rw [map_div₀, map_zpow₀, map_zpow₀, v1, v2]
      exact div_self_le_one _
    obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
    have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
    have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
    have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
    have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact hb ((he.2 _ hb0).2 hc)
    have hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb1]
      exact hab
    have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
    have hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
      intro x y hx hy
      refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
        refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
        · rw [map_mul]; exact mul_mem (ha w) (hb w)
        · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · intro x _; rw [zero_mul]; exact zero_mem _
      · intro x _; rw [mul_zero]; exact zero_mem _
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
      · intro x y _ _ h; rw [mul_neg]; exact neg_mem h
    have := hm ha hi
    rw [RingHom.map_mul, mul_left_comm] at this
    rw [hq, RingHom.map_mul, RingHom.map_mul]
    exact this
  · intro ε B hε h
    obtain ⟨-, -, -, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
    have hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a,
        ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a := by
      intro x
      have hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz⟩ := h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by
          rw [GlobalTheory.LatDual.lamHat_eq_hat]
          exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)
        exact ⟨z, congrFun hz⟩
      | zero => exact ⟨0, fun a => by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z, hz⟩ := hu
        obtain ⟨z', hz'⟩ := hw
        exact ⟨z + z', fun a => by
          rw [Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩
      | smul c u _ hu =>
        obtain ⟨z, hz⟩ := hu
        refine ⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz,
          mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    choose z hz using hx
    have hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) =
        ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
      refine Matrix.ext fun a i => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (hz (Pi.single i 1) a).symm.trans ?_
      congr 1
      by_cases hai : a = i
      · subst hai
        rw [Pi.single_eq_same, Matrix.one_apply_eq]; rfl
      · rw [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]
    exact ⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩

end GlobalTheory.LatIntFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDualLat

variable {D : D7}

theorem ringHom_sum {A B ι : Type} [Semiring A] [Semiring B] [Fintype ι] (f : A →+* B) (g : ι → A) :
    f (∑ i, g i) = ∑ i, f (g i) := map_sum f g _

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

theorem finPart_surjective : Function.Surjective (finPart D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

def form (V : HSp D) (x z : Fin V.rank → AE D) : AE D := ∑ i, ∑ j, cA D (x i) * incA D (V.gram i j) * z j

theorem finPart_form (V : HSp D) (x z : Fin V.rank → AE D) :
    finPart D (form V x z) =
      hR (Af D.host.F) D.sp.cm.sig V.gram (fun i => finPart D (x i)) fun i => finPart D (z i) := by
  simp only [form, ringHom_sum, RingHom.map_mul, finPart_cA]
  rfl

theorem cA_form (V : HSp D) (x z : Fin V.rank → AE D) : cA D (form V x z) = form V z x := by
  simp only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_mul (V : HSp D) (a b : AE D) (x z : Fin V.rank → AE D) :
    form V (fun i => a * x i) (fun i => b * z i) = cA D a * b * form V x z := by
  simp only [form, RingHom.map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff (V : HSp D) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ LamHat V ↔
      ∀ z : Fin V.rank → AE D, (fun i => finPart D (z i)) ∈ LamHat V → finPart D (form V x z) ∈ intAE D := by
  rw [(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]
  constructor
  · intro h z hz
    rw [← cA_form, finPart_cA, finPart_form]
    exact sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← finPart_form, ← cA_form, finPart_cA]
    exact sigR_mem_intAE (h _ hz)

theorem map_form (V : HSp D) {K : Type} [CommRing K] (π : AE D →+* K) (x z : Fin V.rank → AE D) :
    π (form V x z) =
      ((fun i => π (cA D (x i))) ᵥ* (V.gram.map fun a => π (incA D a))) ⬝ᵥ fun k => π (z k) := by
  simp only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_comm

theorem conj_mem_lamHat_iff : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  intro D e v π he hπ V β hβ y
  rw [mem_iff]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hβ fun k => s (β.1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; exact ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hi]; exact ⟨0, map_zero _⟩)
    rw [form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      dotProduct_single, mul_one] at h2
    exact h2
  · intro h z hz
    have h1 := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hβ z).1 h1
    have h3 := form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, cA_cA] at h3
    have h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]
    exact sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))

end GlobalTheory.SplitDualLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectors
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem frameM_coef_eq_chgB : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D p _ lm ι hι X s n N N' a r cκ c0 P P' σ σ' hσ hσ' hdet hsum i x
  unfold frameM
  have hJ : ∀ f : GlobalTheory.DFrame.JJ D n N N' → ℂ_[p], ∑ j, f j = ∑ α, ∑ l, ∑ l', f (α, l, l') := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hJ, Fintype.sum_sigma]
  simp only [GlobalTheory.DFrame.coef, GlobalTheory.DFrame.gc, GlobalTheory.DFrame.pc]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Finset.sum_eq_single x.1 (fun z _ hz => by simp [hz]) (by simp)]
  simp only [if_true, GlobalTheory.DFrame.vecF, GlobalTheory.DFrame.mat, GlobalTheory.DFrame.colR, GlobalTheory.DFrame.rowL, Matrix.of_apply, map_mul, RingEquiv.coe_toRingHom]
  have hsum' := hsum x.1 (s.iT i.1)
  simp only [hι] at hsum'
  have e : ∀ k, ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k)) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (cκ x.1 * r x.1 k * (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) =
      (cκ x.1 * (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) *
      (r x.1 k * ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k))) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hsum']
  by_cases h : s.iT i.1 = tauPl D x.1
  · rw [if_pos h, TaylorLogMetric.chgB, if_pos h.symm]
    simp only [h]
    set tp := tauPl D x.1 with htp
    have hm : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin m) D.host.E),
        Q.map (TaylorLogMetric.tauEmb D lm tp) = Q.map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      intro m Q; ext u v; simp [hι]
    have hinv : ((P tp).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)))⁻¹ =
        ((P tp)⁻¹).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x.1)), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hm, hm, hinv]
    clear e hsum' hJ hsum hm hinv
    have h1 := hσ x.1
    have h2 := hσ' x.1
    simp only [GlobalTheory.DFrame.rho, RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1 h2 ⊢
    simp only [Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← htp] at h1 h2 ⊢
    field_simp
    try ring
  · rw [if_neg h, TaylorLogMetric.chgB, if_neg (fun e => h e.symm)]
    simp

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem hOK_vecF : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  intro D X s L Λ hΛ hbij N N' A B p _ ι
  subst hΛ
  have hA : (0 : ℝ) < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L
  have hconj : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) := fun τ x =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) x
  have hL : Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area L.lattice.toAddSubgroup)⁻¹)
      (vecF D s A) (vecF D s B) =
      ∑ τ : X.Tau, TaylorLogMetric.embT D (s.iT τ) (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
    rw [GlobalTheory.FourthRootStd.area_eq]
    unfold Formalism.L2.Th1.GD.hOK Formalism.L2.AlgTh.hSc
    show ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i, ∑ j, _ = _
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [map_sum, map_mul, hconj, vecF]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have h0 : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast
    field_simp
  rw [hL, map_sum]
  rw [← Equiv.sum_comp s.iT.symm]
  simp only [Equiv.apply_symm_apply]
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  rfl

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRoot
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem GlobalTheory.DFrame.pairedBlock_diag : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  intro D p _ ι X s L sc n N N' a cκ r P P' σ σ' th hth hOK hvan hu hL hR t ab ab'
  obtain ⟨e, he, hE⟩ := Formalism.L2.Th1.GD.tripleTensorAlmostOrthonormal ℂ_[p] D.host.E (HH D) (GlobalTheory.DFrame.rho D ι)
    (Σ z : Bool × HH D, Fin (n z)) ((Bool × HH D) × Fin N) ((Bool × HH D) × Fin N')
    (fun α α' => a α.1 α.2 * D.host.conj (a α'.1 α'.2))
    (fun (l l₂ : (Bool × HH D) × Fin N) => ∑ j : Fin N, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j))
    (fun (q q₂ : (Bool × HH D) × Fin N') => ∑ i : Fin N', GlobalTheory.DFrame.colR D P' σ' q i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' q₂ i))
    N N' (GlobalTheory.DFrame.gc D cκ r) (GlobalTheory.DFrame.pc D ι σ) (GlobalTheory.DFrame.pc D ι σ') th
    (GlobalTheory.DFrame.uu D ι cκ r a) hth hvan (fun _ => rfl) hu hL hR t ab ab'
  refine ⟨e, he, ?_⟩
  rw [← hE]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hOK]
  unfold GlobalTheory.DFrame.coef
  congr 2
  refine Finset.sum_congr rfl (fun z _ => ?_)
  congr 1
  simp only [GlobalTheory.DFrame.mat, Matrix.of_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.LogExist

variable {l : ℕ} [Fact l.Prime]

def logSum (w : Per.AinfP l) (n : ℕ) : Per.AinfP l :=
  ∑ k ∈ Finset.range n, (-1) ^ k * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) * w ^ (k + 1)

theorem logSum_succ (w : Per.AinfP l) (n : ℕ) :
    logSum w (n + 1) = logSum w n + (-1) ^ n * Ring.inverse (((n + 1 : ℕ) : Per.AinfP l)) * w ^ (n + 1) := by
  simp only [logSum, Finset.sum_range_succ]

theorem logSum_cauchy {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    logSum w n ≡ logSum w (n + 1) [SMOD (Per.kerP l ^ n • ⊤ : Submodule (Per.AinfP l) (Per.AinfP l))] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, logSum_succ, sub_add_cancel_left]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hw _)

def logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : Per.BdRp l :=
  (GlobalTheory.RingIface.exists_bdRp_equiv l).choose.symm (AdicCompletion.mk (Per.kerP l) (Per.AinfP l)
    (AdicCompletion.AdicCauchySequence.mk (Per.kerP l) (Per.AinfP l) (logSum w) (logSum_cauchy hw)))

theorem ev_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    Per.ev l n (logP hw) = Ideal.Quotient.mk _ (logSum w n) := by
  rw [← (GlobalTheory.RingIface.exists_bdRp_equiv l).choose_spec.2, logP, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk]
  rfl

theorem factorial_mul_logSum (w : Per.AinfP l) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l) * logSum w n =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) := by
  rw [logSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : n.factorial / (k + 1) * (k + 1) = n.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (Nat.succ_pos k) hkn)
  have hu : ((k + 1 : ℕ) : Per.AinfP l) * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) = 1 :=
    Ring.mul_inverse_cancel _ (GlobalTheory.RingBasics.isUnit_nat l _ (Nat.succ_ne_zero k))
  have hc : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * ((k + 1 : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, hd]
  rw [hc]
  linear_combination (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) * hu

theorem isLogP_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : IsLogP w (logP hw) := by
  intro n
  rw [ev_logP, ← factorial_mul_logSum, map_mul, map_natCast]

theorem exists_isLogP : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u :=
  fun _ _ _ hw => ⟨logP hw, isLogP_logP hw⟩

end GlobalTheory.Pst.LogExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbitsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
end

