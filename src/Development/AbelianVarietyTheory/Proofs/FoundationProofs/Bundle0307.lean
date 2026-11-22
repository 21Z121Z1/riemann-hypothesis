import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebraStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  first | exact @GlobalTheory.TranslLin.transl_lin | exact GlobalTheory.TranslLin.transl_lin | (intros; apply GlobalTheory.TranslLin.transl_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.FrobStick

open PowerSeries

def colA (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := sgStar Λ z ^ 3

def colB (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)

def colC (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z

def tay (F : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 F)

def defect {R : Type*} [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) :
    MvPowerSeries (Fin 3) R :=
  Matrix.det (Matrix.of fun i j =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) : MvPowerSeries (Fin 3) R)) -
    2 * PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 1 - MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) s *
      PowerSeries.subst (MvPowerSeries.X 2 - MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) s

end GlobalTheory.FrobStick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminantStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 → ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 := by
  first | exact @GlobalTheory.DupNorm.max_norm_eq_padicComplex | exact GlobalTheory.DupNorm.max_norm_eq_padicComplex | (intros; apply GlobalTheory.DupNorm.max_norm_eq_padicComplex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemPrime

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
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

theorem isIntegral_star {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd D.host.E) hx

theorem evalV_algebraMap_mem (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.F) (ht : IsIntegral ℤ t) :
    evalV D.host.F v (algebraMap D.host.F (Af D.host.F) t) ∈ v.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes]
  have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) t) = v.valuation D.host.F t :=
    v.valuedAdicCompletion_eq_valuation' _
  show Valued.v (algebraMap D.host.F (Fv D.host.F v) t) ≤ 1
  rw [h2]
  exact v.valuation_le_one (K := D.host.F) (⟨t, ht⟩ : 𝓞 D.host.F)

theorem exists_trace {z : Formalism.L2.Theta.AE D} (hz : z ∈ intL D) :
    ∃ β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, z + cA D z = fj D β := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    obtain ⟨t, ht⟩ := exists_of_star_eq D (x := (o : D.host.E) + star (o : D.host.E))
      (by rw [star_add, star_star, add_comm])
    have hti : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ht]
      exact o.2.add (isIntegral_star o.2)
    refine ⟨algebraMap D.host.F (Af D.host.F) t * α, fun v => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (evalV_algebraMap_mem v t hti) (hα v)
    · rw [cA_tmul, ← TensorProduct.tmul_add, ← ht, tmul_algebraMap_eq, fj_eq]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => exact ⟨0, fun v => by rw [map_zero]; exact zero_mem _, by rw [map_zero, map_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, fun v => by rw [map_add]; exact add_mem (ha v) (hb v), by
      rw [RingHom.map_add, map_add (fj D), ← h1, ← h2, add_add_add_comm]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, h1⟩ := hx
    exact ⟨-a, fun v => by rw [map_neg]; exact neg_mem (ha v), by
      rw [RingHom.map_neg, map_neg (fj D), ← h1, neg_add]⟩

theorem finPart_mem {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])

theorem mem_iff {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) (y : Fv D.host.F v) :
    finPart D (fj D (singleV D.host.F v y) * e) ∈ intAE D ↔ Valued.v y ≤ 1 := by
  constructor
  · intro h
    have h1 := inF_mem h
    rw [inF_finPart, ← mul_assoc, ← map_mul, one_mul] at h1
    obtain ⟨β, hβ, h2⟩ := exists_trace h1
    rw [map_mul, cA_fj, ← mul_add, he.2.2, ← map_mul] at h2
    have h3 := congrArg (evalV D.host.F v) (fj_inj D h2)
    rw [map_mul, evalV_singleV_same, evalV_singleV_same, mul_one] at h3
    rw [h3]
    exact hβ v
  · intro h
    rw [RingHom.map_mul]
    exact mul_mem_int (AddSubgroup.subset_closure
      ⟨singleV D.host.F v y, singleV_mem_intAf D.host.F v ⟨y, h⟩, 1, rfl⟩) (finPart_mem he)

theorem singleV_add (v : HeightOneSpectrum (𝓞 D.host.F)) (x y : Fv D.host.F v) :
    singleV D.host.F v (x + y) = singleV D.host.F v x + singleV D.host.F v y := by
  rw [← sub_eq_iff_eq_add, ← singleV_sub, add_sub_cancel_right]

theorem scalar_eq {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {a b : Fv D.host.F v}
    (h : fj D (singleV D.host.F v a) * e = fj D (singleV D.host.F v b) * e) : a = b := by
  have := he.scalar_inj h
  rwa [evalV_singleV_same, evalV_singleV_same] at this

theorem exists_hom {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) :
    ∃ φ : D.host.E →+* Fv D.host.F v, ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e := by
  choose f hf using fun x => he.exists_scalar (incA D x)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := fun x y => ?_, map_zero' := ?_, map_add' := fun x y => ?_ }, hf⟩
  · refine scalar_eq he ?_
    rw [← hf, map_one, mul_one, he.pl_mul]
  · refine scalar_eq he ?_
    have h : singleV D.host.F v (f x * f y) = singleV D.host.F v (f x) * singleV D.host.F v (f y) := by
      rw [singleV_mul, evalV_singleV_same]
    rw [← hf, map_mul, h, map_mul, ← mul_assoc, hf, mul_assoc, hf, mul_assoc]
  · refine scalar_eq he ?_
    rw [← hf, map_zero, mul_zero, ← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self, map_zero, zero_mul]
  · refine scalar_eq he ?_
    rw [← hf, map_add, singleV_add, map_add, mul_add, add_mul, hf, hf]

theorem hom_algebraMap {v} {e : Formalism.L2.Theta.AE D} (he : SplitAt D v e) {φ : D.host.E →+* Fv D.host.F v}
    (hφ : ∀ x, e * incA D x = fj D (singleV D.host.F v (φ x)) * e) (t : D.host.F) :
    φ (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (Fv D.host.F v) t := by
  refine scalar_eq he ?_
  have h1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (algebraMap D.host.F (AF D.host.F) t * 1) :=
    tmul_algebraMap_eq (1 : AF D.host.F) t
  have h2 : evalV D.host.F v (algebraMap D.host.F (AF D.host.F) t * 1).2 * 1 =
      algebraMap D.host.F (Fv D.host.F v) t := by
    rw [mul_one, mul_one]
    exact (evalV D.host.F v).commutes t
  rw [← hφ, h1, ← h2, ← singleV_mul, ← algebraMap_mul_fj, mul_assoc, he.pl_mul, mul_comm]

theorem exists_isIdemAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : Formalism.L2.Theta.AE D), GlobalTheory.IdemModTwo.SplitAt D v e → ∃ PP : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
  intro D v e he
  obtain ⟨φ, hφ⟩ := exists_hom he
  have hint : ∀ x : 𝓞 D.host.E, Valued.v (φ x) ≤ 1 := fun x => by
    rw [← mem_iff he, ← hφ, RingHom.map_mul]
    exact mul_mem_int (finPart_mem he) (AddSubgroup.subset_closure
      ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩)
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {x | Valued.v (φ x) < 1}
      add_mem' := fun {a b} ha hb => by
        show Valued.v (φ ((a : D.host.E) + b)) < 1
        rw [map_add]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        show Valued.v (φ 0) < 1
        rw [map_zero, map_zero]; exact zero_lt_one
      smul_mem' := fun c x hx => by
        show Valued.v (φ ((c : D.host.E) * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hI : ∀ x, x ∈ I ↔ Valued.v (φ x) < 1 := fun x => Iff.rfl
  have hcomap : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := by
    ext t
    rw [Ideal.mem_comap, hI]
    have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) := rfl
    have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F v) (algebraMap (𝓞 D.host.F) D.host.F t)) =
        v.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [h1, hom_algebraMap he hφ, h2]
    exact v.valuation_lt_one_iff_mem _
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : 𝓞 D.host.E) ∈ I := by rw [h]; trivial
      have h2 : Valued.v (φ 1) < 1 := h1
      rw [map_one, map_one] at h2
      exact lt_irrefl _ h2
    · have h2 : Valued.v (φ ((a : D.host.E) * b)) < 1 := hab
      rw [map_mul, map_mul] at h2
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h2 (not_lt.2 (one_le_mul hn.1 hn.2))
  have hne : I ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hcomap, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨⟨I, hprime, hne⟩, ⟨(isSplitIdem_iff e).2 ⟨v, he⟩, fun x hx => ?_⟩, hcomap⟩
  have hx0 : Valued.v (φ x) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]
    exact fun h => hx (Subtype.ext h)
  show x ∈ I ↔ _
  rw [hI, hφ, mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

end GlobalTheory.IdemPrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquivStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  first | exact @GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | exact GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv | (intros; apply GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdelesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) := by
  first | exact @GlobalTheory.PlaceIdem.exists_isPlIdem | exact GlobalTheory.PlaceIdem.exists_isPlIdem | (intros; apply GlobalTheory.PlaceIdem.exists_isPlIdem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficientsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  first | exact @GlobalTheory.FN.tower_exists | exact GlobalTheory.FN.tower_exists | (intros; apply GlobalTheory.FN.tower_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
section
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
open scoped TensorProduct

namespace GlobalTheory.OddRoot

theorem finite_root_odd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (hn : Odd n) (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = n • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x ∈ intHat F E ∧ y ∈ intHat F E ∧ x * y = 1 ∧
      x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧ ∃ p ∈ intHat F E, x - 1 = n • p := by
  have hu1 : u = 1 + n * z := by
    rw [nsmul_eq_mul] at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ n) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨h, hh⟩ : ∃ h, e = 2 * h := by
    obtain ⟨g, hg⟩ := (hun (-1)).exists_right_inv
    obtain ⟨k, hk⟩ := hn
    refine ⟨-(k * e * g), ?_⟩
    rw [hk] at hg
    push_cast at hg
    linear_combination (-e) * hg - (2 * k + 1) * g * hee
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun
    (inclHat F E h * ⟨z, hz⟩)).exists_right_inv
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hh' : (inclHat F E e : RA F E) = 2 * inclHat F E h := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hh
    simp only [map_mul, map_ofNat] at this
    exact this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * (inclHat F E h * z)) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hhO := (inclHat F E h).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (inclHat F E h : RA F E) = h' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  obtain ⟨w, hw⟩ : ∃ w, w = 1 + e' * n * (h' * z) := ⟨_, rfl⟩
  rw [← hw] at hy₀'
  have hwO : w ∈ intHat F E := by
    rw [hw]
    exact add_mem (one_mem _) (mul_mem (mul_mem heO (natCast_mem _ n)) (mul_mem hhO hz))
  have h2w : 2 * (e' * w) = e' * (1 + u) := by
    rw [hw, hu1]
    linear_combination (-(e' * e' * n * z)) * hh' + (n * z * (e' + 1)) * hee'
  have hr₀ : e' * w = u * sg (FiniteAdeleRing (𝓞 F) F) c (e' * w) := by
    have htwo : IsUnit (2 : RA F E) := by
      have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (RA F E))
      rwa [map_ofNat] at this
    apply htwo.mul_left_cancel
    have := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) h2w
    rw [map_mul _ 2, map_ofNat, map_mul _ e' (1 + u), map_add, map_one, hse] at this
    linear_combination h2w - u * this - e' * hu
  have he1 := sub_mem (one_mem (intHat F E)) heO
  refine ⟨e' * w + (1 - e') * x₁, e' * y' + (1 - e') * y₁, add_mem (mul_mem heO hwO) (mul_mem he1 hx₁'),
    add_mem (mul_mem heO hy₀O) (mul_mem he1 hy₁'), ?_, ?_, e' * e' * (h' * z) + f' * (x₁ - 1),
    add_mem (mul_mem (mul_mem heO heO) (mul_mem hhO hz)) (mul_mem hfO (sub_mem hx₁' (one_mem _))), ?_⟩
  · linear_combination e' * hy₀' + (1 - e') * hxy₁ + (w * y' - w * y₁ - x₁ * y' + x₁ * y₁) * hee'
  · rw [map_add, map_mul _ (1 - e'), map_sub, map_one, hse]
    linear_combination hr₀ + (1 - e') * hr₁
  · rw [nsmul_eq_mul, hw]
    linear_combination (x₁ - 1) * hef'

end GlobalTheory.OddRoot
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OddRoot
open GlobalTheory.Member

theorem exists_root_odd : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  intro D N hN u z hz huz hu
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hz ⊢
  exact finite_root_odd D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP N hN u z hz huz hu

end GlobalTheory.OddRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOtherHalfPeriod
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriod

theorem half_comb_not_mem (w₁ w₂ : ℂ) (hind : LinearIndependent ℝ ![w₁, w₂]) (a b : ℤ)
    (hab : ¬ (2 ∣ a ∧ 2 ∣ b)) :
    ((a : ℂ) * w₁ + (b : ℂ) * w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  intro h
  rw [AddSubgroup.mem_closure_pair] at h
  obtain ⟨m, n, hmn⟩ := h
  rw [LinearIndependent.pair_iff] at hind
  have key : ((a - 2 * m : ℤ) : ℝ) • w₁ + ((b - 2 * n : ℤ) : ℝ) • w₂ = 0 := by
    rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-2 : ℂ) * hmn
  obtain ⟨h1, h2⟩ := hind _ _ key
  have h1' : a - 2 * m = 0 := by exact_mod_cast h1
  have h2' : b - 2 * n = 0 := by exact_mod_cast h2
  exact hab ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩

theorem exists_other_half_period : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ,
    2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  rintro Λ ⟨w₁, w₂, hind, rfl⟩ P _ _
  have hw₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have hw₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) :=
    AddSubgroup.subset_closure (by simp)
  have n₁ : w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 0 (by decide)
    simpa using this
  have n₂ : w₂ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 0 1 (by decide)
    simpa using this
  have n₃ : (w₁ - w₂) / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    have := half_comb_not_mem w₁ w₂ hind 1 (-1) (by decide)
    convert this using 2
    push_cast; ring
  by_cases hP : P - w₁ / 2 ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)
  · refine ⟨w₂ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₂, n₂, ?_⟩
    intro h
    apply n₃
    have := AddSubgroup.sub_mem _ h hP
    convert this using 1
    ring
  · exact ⟨w₁ / 2, by rw [mul_div_cancel₀ _ two_ne_zero]; exact hw₁, n₁, hP⟩

end GlobalTheory.HalfPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApproxStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdele_exists_local_approx' : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  first | exact @GlobalTheory.finiteIdele_exists_local_approx | exact GlobalTheory.finiteIdele_exists_local_approx | (intros; apply GlobalTheory.finiteIdele_exists_local_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslatesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates : ∀ (D : D7), Inp D → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → 0 < Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∃ (b : Fin (fF D * P.a * P.d) → Matrix (Fin P.d) (Fin P.a) D.host.E) (k M : ℕ) (r : Fin k → Qbar) (s : Fin k → VC D P.a P.d), OnB D b ∧ LocBasis D p (YYl D (stdL D P.a) (stdL D P.d)) b ∧ 0 < M ∧ Nat.Coprime M p ∧ (∀ i, (M * Q) • s i ∈ LaB D (tor0 D ⊤ δ) b) ∧ (∀ i, ‖lam (r i)‖ ≤ (‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) ∧ P.W.Om g g' P.F = fun z => ∑ i, (r i : ℂ) * U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z := by
  first | exact @GlobalTheory.NormSum.kernel_eq_sum_translates | exact GlobalTheory.NormSum.kernel_eq_sum_translates | (intros; apply GlobalTheory.NormSum.kernel_eq_sum_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerEqNormalisedAdelicSumStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → SelfDual γ ((latA D cc N N').map (actA D N N' (g, g'))) → ∀ F : TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') F → Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') F = ((Real.sqrt (idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) : ℝ))⁻¹ : ℂ) • ((sumOp WA (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := by
  first | exact @GlobalTheory.FinWeil.iop_eq_sumOp | exact GlobalTheory.FinWeil.iop_eq_sumOp | (intros; apply GlobalTheory.FinWeil.iop_eq_sumOp <;> assumption)
end

