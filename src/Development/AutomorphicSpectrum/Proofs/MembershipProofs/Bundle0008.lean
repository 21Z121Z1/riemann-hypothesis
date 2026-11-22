import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStd
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStdStatement
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_selfDual_lattice : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.StdLattice.exists_std | exact GlobalTheory.CompanionTheory.StdLattice.exists_std | (intros; apply GlobalTheory.CompanionTheory.StdLattice.exists_std <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain GlobalTheory.CompanionTheory.IdxAd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.IdxAd.Unif

theorem resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by
  intro F _ _ v
  have hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) =
      (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr hS
  have hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F] := fun hx =>
    (GroundTheory.Global.mem_valuationInteger_iff v _).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)
  refine ⟨?_, ?_⟩
  · have h := GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
    rw [← h]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  · obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
    have hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      GroundTheory.Global.valued_of_irreducible v hq
    have hq0 : (q : v.adicCompletion F) ≠ 0 := fun h => hq.ne_zero (Subtype.ext h)
    have hp : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff e.symm).2 hq
    refine ⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩
    have ht : Valued.v (t : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.2 t.ne_zero
    set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha
    have hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) :
        v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval,
        ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]
      simp
    refine ⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · simp [mul_assoc]
    · rw [ha, Int.natAbs_neg]

end GlobalTheory.CompanionTheory.IdxAd.Unif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissibleStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_distribution_heisenberg_invariant : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → (∀ w, ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ) ∧ ∀ (w : (κ → F) × (κ → F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ), thetaSum F (schr ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum | exact GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum | (intros; apply GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum <;> assumption)
end

