import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  first | exact @GlobalTheory.CoverDS.unitEquiv_of_dsUnique | exact GlobalTheory.CoverDS.unitEquiv_of_dsUnique | (intros; apply GlobalTheory.CoverDS.unitEquiv_of_dsUnique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBases
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')
      rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeriesStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_param_coverDiscreteSeries : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  first | exact @GlobalTheory.CoverExhaust.exists_param | exact GlobalTheory.CoverExhaust.exists_param | (intros; apply GlobalTheory.CoverExhaust.exists_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPoint
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo

open FirstMinPos in

theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanCoefficients
section
namespace GlobalTheory.CoefficientSpanFinite

theorem finiteDimensional_span_coefficients {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let Φ : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range Φ := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ∘ₗ LinearMap.applyₗ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CoefficientSpanFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwistStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist : ∀ (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), HasTypes (Cover.twist R) lam → HasTypes R fun a => lam a + 1 / 2 := by
  first | exact @GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | exact GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | (intros; apply GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOneStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightLine_of_kTypeMultiplicityOne : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  first | exact @GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | exact GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one | (intros; apply GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentFiniteAdelesIffFrameUnipotentRadi
section
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnipFin

open Formalism.L2.SG.HidaSetting

theorem mem_span_image_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (v : ι → M) (s : Set ι) (w : M) :
    w ∈ Submodule.span R (v '' s) ↔ ∃ f : ι → R, (∀ i, i ∉ s → f i = 0) ∧ ∑ i, f i • v i = w := by
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun i hi => (Finsupp.mem_supported' R l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul R _
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm f, (Finsupp.mem_supported' R _).2 fun i hi => hf i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; exact zero_smul R _

variable (I : Formalism.MainNotions.S.AutInst)

theorem sigR_inclE (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F)) (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hA_incl_incl (p q : Fin I.n → I.E) :
    hA I (incl I p) (incl I q) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, sigR_inclE]

variable {I} {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)

theorem mulVec_flag (v : Fin ρ → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ v =
      ∑ a, (v a * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (c a)) • incl I (x a) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, incl, map_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem mulVec_dual (y : VA I) (a : Fin ρ) :
    ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map
      (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ y) a =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.of_apply, map_sum, map_mul, hA, Formalism.UG.hform, incl, sigR_inclE, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem unip_flag_iff_Nfin : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  intro I ρ x c z hc hz N

  let EA := (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F))
  let w : Fin ρ → VA I := fun a => incl I (x a)
  have hcol : ∀ a, (fun k => EA k a) = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) • w a := by
    intro a; funext k
    simp only [EA, w, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, incl, map_mul]
  have hinv : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) = 1 := fun a => by
    rw [← map_mul, inv_mul_cancel₀ (hc a), map_one]
  have hinv' : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ = 1 := fun a => by
    rw [← map_mul, mul_inv_cancel₀ (hc a), map_one]

  have hK : ∀ y : VA I, (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F)) *ᵥ y = 0 ↔
      ∀ a, hA I (incl I (x a)) y = 0 := by
    intro y
    constructor
    · intro h a
      have hs : starRingEnd I.E (c a) ≠ 0 := (map_ne_zero _).2 (hc a)
      have h1 := congrFun h a
      rw [mulVec_dual] at h1
      calc hA I (incl I (x a)) y
          = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a))⁻¹ * (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
        _ = 0 := by rw [h1, Pi.zero_apply, mul_zero]
    · intro h
      funext a
      rw [mulVec_dual, h a, mul_zero, Pi.zero_apply]

  have hspan : ∀ y : VA I, (∃ v, N *ᵥ y = y + EA *ᵥ v) ↔
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) := by
    intro y
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨fun a => v a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a), ?_⟩
      rw [← mulVec_flag, Matrix.sub_mulVec, hv, Matrix.one_mulVec]
      abel
    · rintro ⟨f, hf⟩
      refine ⟨fun a => f a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹, ?_⟩
      rw [mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      rw [hf, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
  constructor
  · rintro ⟨⟨T, hT, hNT⟩, h2⟩
    have hdual : ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
        (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) :=
      fun y hy => (hspan y).1 (h2 y ((hK y).2 hy))
    refine ⟨fun a => ?_, hdual _ fun a => by rw [hA_incl_incl, hz a, map_zero], hdual⟩
    have hv : N *ᵥ (fun k => EA k a) = (fun k => EA k a) + EA *ᵥ (fun b => T b a) :=
      funext fun k => congrFun (congrFun hNT k) a
    rw [hcol, Matrix.mulVec_smul, mulVec_flag] at hv
    have hw : (N - 1) *ᵥ w a = ∑ b, (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b))) • w b := by
      have := congrArg (fun v => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ • v) hv
      simp only [smul_add, smul_smul, hinv, one_smul, Finset.smul_sum] at this
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, this]
      abel
    refine (mem_span_image_iff w _ _).2 ⟨fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)), fun b hb => ?_, hw.symm⟩
    show _ * (T b a * _) = 0
    rw [hT b a (not_lt.1 hb), zero_mul, mul_zero]
  · rintro ⟨h1, -, h3⟩
    choose f hf0 hfs using fun a => (mem_span_image_iff w _ _).1 (h1 a)
    refine ⟨⟨fun b a => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
    · show _ * f i j * _ = 0
      rw [hf0 i j (not_lt.2 hij), mul_zero, zero_mul]
    · ext k a
      suffices hv : N *ᵥ (fun k => EA k a) =
          (fun k => EA k a) + EA *ᵥ (fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹) from congrFun hv k
      rw [hcol, Matrix.mulVec_smul, mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      have hN : N *ᵥ w a = w a + (N - 1) *ᵥ w a := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [hN, ← hfs a, smul_add, Finset.smul_sum]
      simp_rw [smul_smul]
      rfl
    · exact (hspan y).2 (h3 y ((hK y).1 hy))

end GlobalTheory.UnipFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixIffJointlyBijectivePair
section
open Matrix

namespace GlobalTheory.BesselChar.JointSplit

variable {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂]

theorem fwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) (h : GlobalTheory.BesselChar.Unip E K M) :
    GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) := by
  obtain ⟨⟨T, hT, hMT⟩, h2⟩ := h
  refine ⟨⟨T.map f, fun j i hij => by simp [hT j i hij], ?_⟩, fun y₁ hy₁ => ?_⟩
  · rw [← Matrix.map_mul, hMT, Matrix.map_add _ (map_add f), Matrix.map_mul]
  · choose l hl1 hl2 using hsurj
    obtain ⟨y, hfy, hgy⟩ : ∃ y : Fin n → A, (fun i => f (y i)) = y₁ ∧ (fun i => g (y i)) = 0 :=
      ⟨fun i => l (y₁ i) 0, funext fun i => hl1 _ _, funext fun i => hl2 _ _⟩
    have hKy : K *ᵥ y = 0 := by
      funext i
      apply hinj
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map f K y) i
        rw [hfy, hy₁] at this
        exact this.symm
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map g K y) i
        rw [hgy, Matrix.mulVec_zero] at this
        exact this.symm
    obtain ⟨a, ha⟩ := h2 y hKy
    refine ⟨fun i => f (a i), ?_⟩
    subst hfy
    rw [GlobalTheory.BesselChar.mulVec_map, GlobalTheory.BesselChar.mulVec_map, ha]
    funext i
    simp only [Pi.add_apply, map_add]

theorem bwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A)
    (h1 : GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f))
    (h2 : GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g)) : GlobalTheory.BesselChar.Unip E K M := by
  choose l hl1 hl2 using hsurj
  have l00 : l 0 0 = 0 := hinj _ (hl1 0 0) (hl2 0 0)
  have extM : ∀ {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A), X.map f = Y.map f → X.map g = Y.map g → X = Y := by
    intro p q X Y hf hg
    ext i j
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hf i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hg i) j
  have extV : ∀ {p : ℕ} (x z : Fin p → A), (fun i => f (x i)) = (fun i => f (z i)) →
      (fun i => g (x i)) = (fun i => g (z i)) → x = z := by
    intro p x z hf hg
    funext i
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun hf i
    · rw [map_sub, sub_eq_zero]; exact congrFun hg i
  obtain ⟨⟨T₁, hT₁, e₁⟩, k₁⟩ := h1
  obtain ⟨⟨T₂, hT₂, e₂⟩, k₂⟩ := h2
  let T : Matrix (Fin ρ) (Fin ρ) A := Matrix.of fun i j => l (T₁ i j) (T₂ i j)
  have hTf : T.map f = T₁ := by ext i j; exact hl1 _ _
  have hTg : T.map g = T₂ := by ext i j; exact hl2 _ _
  refine ⟨⟨T, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
  · show l (T₁ j i) (T₂ j i) = 0
    rw [hT₁ j i hij, hT₂ j i hij, l00]
  · apply extM
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add f), Matrix.map_mul, hTf, e₁]
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add g), Matrix.map_mul, hTg, e₂]
  · have hy₁ : K.map f *ᵥ (fun i => f (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero f
    have hy₂ : K.map g *ᵥ (fun i => g (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero g
    obtain ⟨a₁, ha₁⟩ := k₁ _ hy₁
    obtain ⟨a₂, ha₂⟩ := k₂ _ hy₂
    have ea₁ : (fun i => f (l (a₁ i) (a₂ i))) = a₁ := funext fun i => hl1 _ _
    have ea₂ : (fun i => g (l (a₁ i) (a₂ i))) = a₂ := funext fun i => hl2 _ _
    refine ⟨fun i => l (a₁ i) (a₂ i), extV _ _ ?_ ?_⟩
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₁]
      conv_lhs => rw [← ea₁, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add]
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₂]
      conv_lhs => rw [← ea₂, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add]

theorem unip_iff_of_joint : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  intro A R₁ R₂ _ _ _ f g hinj hsurj n ρ E K M
  refine ⟨fun h => ⟨fwd f g hinj hsurj E K M h, fwd g f (fun y hg hf => hinj y hf hg)
    (fun a b => (hsurj b a).imp fun _ h => h.symm) E K M h⟩, fun h => bwd f g hinj hsurj E K M h.1 h.2⟩

end GlobalTheory.BesselChar.JointSplit
end

