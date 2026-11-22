import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.FormalGroupWitt.WeightInvariance
import Formalism.TorsionNormIteration.LubinTateExample
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.BehrendSets.TranslateMean
import Formalism.BehrendSets.FinalE

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.CocycleIsCoboundary
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem norm_for_all_alpha : NormAllAlpha := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm tr hinj hnm htr hadd hlin hadj h2 α α' u hu2 hα hα'
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have add2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have e1 : φ ((α + α') • u) = φ (α • u) + φ (α' • u) + cob φ (α • u) (α' • u) := by
    unfold cob; rw [add_smul]; abel
  have e2 : cob φ (α • u) (α' • u) = cob φ u ((star α * α') • u) := by rw [hadj, smul_smul]
  have e3 : cob φ u ((star α * α') • u) + cob φ u ((star α * α') • u)
      = (tr (star α * α')) • cob φ u u := by
    have h : cob φ u ((star α * α') • u) = cob φ u (star (star α * α') • u) := by
      rw [symm, hadj]
    nth_rewrite 1 [h]; rw [← add2, ← add_smul, ← htr, hlin]
  have e4 : cob φ u u = φ u + φ u := by
    unfold cob; rw [← two_smul O u, hu2]
    have : (4 : Z) • φ u = φ u + φ u + φ u + φ u := by
      rw [show (4 : Z) = 1 + 1 + 1 + 1 by norm_num]; simp [add_smul]
    rw [this]; abel
  have e5 : cob φ u ((star α * α') • u) = tr (star α * α') • φ u := by
    apply sub_eq_zero.1; apply h2
    have : ∀ x y : Q, (x - y) + (x - y) = (x + x) - (y + y) := by intro x y; abel
    rw [this, e3, e4, smul_add, sub_self]
  have e6 : nm (α + α') = nm α + nm α' + tr (star α * α') := by
    apply hinj; simp only [map_add, hnm, htr, star_add, star_mul, star_star]; ring
  rw [e1, e2, e5, hα, hα', e6, add_smul, add_smul]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.DifferenceStableUnderAction
section
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

namespace PfM

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

theorem orbitsInt : OrbitsInt := by
  intro e φ hφ
  have hp : ∀ g : GG e, (placeOf g).2 = g.2 ∧ (placeOf g).1 = (g.1.1 * g.1.2, 1) := by
    intro g
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨by simp [placeOf, hg], ?_⟩
      ext <;> simp [placeOf, hg]
    · refine ⟨by simp [placeOf, hg, cc], ?_⟩
      ext <;> simp [placeOf, hg, cc, c0]
  have hsq : ∀ x : ℤˣ, ∀ i : ℤ, x ^ i = if Even i then 1 else x := by
    intro x i
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · simp [zpow_mul, Int.units_sq]
    · have : ¬ Even (2 * k + 1) := by simp
      simp [zpow_add, zpow_mul, Int.units_sq]
  refine ⟨⟨?_, rfl, ?_, orderOf_inv φ⟩, ?_⟩
  · rcases hφ with h | h <;> rw [Prod.fst_inv, h] <;> ext <;> simp [c0]
  · rw [Prod.snd_inv, orderOf_inv]
  · intro τ i
    have h2 : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_Psi_iff, mem_Psi_iff]
      have : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [this, h2, hsq]
      rcases Int.units_eq_one_or τ.1.2 with ht | ht <;> by_cases hi : Even i <;> simp [ht, hi]
    · rw [(hp _).1]; simp
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, c0]
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, sg]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField Ideal

theorem congruencePowers : CongruencePowers := by
  intro R _ I g k hg A hA m

  have hmul : ∀ (a b : ℕ) (X Y : Matrix (Fin k) (Fin k) R), (∀ i j, X i j ∈ I ^ a) →
      (∀ i j, Y i j ∈ I ^ b) → ∀ i j, (X * Y) i j ∈ I ^ (a + b) := by
    intro a b X Y hX hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => by rw [pow_add]; exact Ideal.mul_mem_mul (hX i l) (hY l j)
  induction m with
  | zero => simpa using hA
  | succ m ih =>
    set B := A ^ g ^ m with hB
    have hBI : ∀ i j, (B - 1) i j ∈ I := fun i j => Ideal.pow_le_self (by omega) (ih i j)
    have hpow : ∀ n : ℕ, ∀ i j, (B ^ n - 1) i j ∈ I := by
      intro n
      induction n with
      | zero => intro i j; simp
      | succ n ihn =>
        intro i j
        have : B ^ (n + 1) - 1 = (B ^ n - 1) * (B - 1) + (B ^ n - 1) + (B - 1) := by
          rw [pow_succ]; noncomm_ring
        rw [this]
        refine I.add_mem (I.add_mem ?_ (ihn i j)) (hBI i j)
        have := hmul 1 1 _ _ (by simpa using ihn) (by simpa using hBI) i j
        exact Ideal.pow_le_self (by omega) this
    have hgeom : B ^ g - 1 = (B - 1) * ∑ n ∈ Finset.range g, B ^ n := by
      have := (Commute.one_right B).mul_geom_sum₂ g
      simpa using this.symm
    have hsum : ∀ i j, (∑ n ∈ Finset.range g, B ^ n) i j ∈ I ^ 1 := by
      intro i j
      have : (∑ n ∈ Finset.range g, B ^ n) = (∑ n ∈ Finset.range g, (B ^ n - 1)) + (g : R) • 1 := by
        rw [Finset.sum_sub_distrib]; simp [Matrix.smul_one_eq_diagonal, nsmul_eq_mul]
        ext i j; simp [Matrix.natCast_apply, Matrix.diagonal_apply]
      rw [this, pow_one, Matrix.add_apply, Matrix.sum_apply]
      refine I.add_mem (Ideal.sum_mem _ fun n _ => hpow n i j) ?_
      rw [Matrix.smul_apply]
      exact I.mul_mem_right _ hg
    intro i j
    have e1 : A ^ g ^ (m + 1) = B ^ g := by rw [hB, ← pow_mul, pow_succ]
    rw [e1, hgeom]
    exact hmul (m + 1) 1 _ _ ih hsum i j

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

theorem coord {e : ℕ} (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (φ τ : GG e)
    (hφ : φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (i : ℤ) :
    Multiplicative.toAdd (ι (placeOf (φ ^ i * τ)).2) =
      Multiplicative.toAdd (ι τ.2) + i • Multiplicative.toAdd (ι φ.2) := by
  rw [((orbitsInt e φ hφ).2 τ i).2.1, map_mul, map_zpow, toAdd_mul, toAdd_zpow, add_comm]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped TensorProduct

theorem bc_pr_incl {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (γ₀ : Matrix.GeneralLinearGroup (Fin k) E) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀) =
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ := by
  ext i l
  simp [Formalism.UG.bc, Formalism.UG.prV, Formalism.UG.inclE]

end

end PfM

open Formalism.FrobeniusOrbits

theorem congruence_powers : CongruencePowers := PfM.congruencePowers

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
end

