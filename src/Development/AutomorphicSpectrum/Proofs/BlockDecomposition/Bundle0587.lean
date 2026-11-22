import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfBound
section
open Ad3 Ad3.S
open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegralWeight

lemma exp_split (c x y : ℝ) :
    cexp (2 * π * I * c * ((x : ℂ) + y * I)) =
      cexp (((2 * π * c * x : ℝ) : ℂ) * I) * (Real.exp (-(2 * π * c * y)) : ℂ) := by
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  have h : I * I = -1 := I_mul_I
  linear_combination (2 * π * c * y : ℂ) * h

lemma norm_exp_height (c x y : ℝ) :
    ‖cexp (2 * π * I * c * ((x : ℂ) + y * I))‖ = Real.exp (-(2 * π * c * y)) := by
  rw [exp_split, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma integral_exp_int (j : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1, cexp (2 * π * I * j * x) = if j = 0 then 1 else 0 :=
  _root_.UpperTheory.Reformulated.B.Yra2.main j

lemma coeff_integral (F : ℝ → ℂ) (a : ℕ → ℂ) (y : ℝ)
    (hs : ∀ x : ℝ, HasSum (fun m : ℕ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))) (F x))
    (hsum : Summable fun m : ℕ => ‖a m‖ * Real.exp (-(2 * π * m * y))) (q : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, F x * cexp (-(2 * π * I * q * x)) =
      a q * (Real.exp (-(2 * π * q * y)) : ℂ) := by
  have key : HasSum (fun m : ℕ => ∫ x : ℝ in (0 : ℝ)..1,
      a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) * cexp (-(2 * π * I * q * x)))
      (∫ x : ℝ in (0 : ℝ)..1, F x * cexp (-(2 * π * I * q * x))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ‖a m‖ * Real.exp (-(2 * π * m * y))) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · intro m
      refine Eventually.of_forall fun x _ => ?_
      have h2 : ‖cexp (-(2 * π * I * q * x))‖ = 1 := by
        have : -(2 * π * I * q * x) = (((-(2 * π * q * x)) : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, norm_exp_ofReal_mul_I]
      have h3 := norm_exp_height (m : ℝ) x y
      push_cast at h3
      rw [norm_mul, norm_mul, h2, h3, mul_one]
    · exact Eventually.of_forall fun x _ => hsum
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x _ => ?_
      exact (hs x).mul_right _
  have hval : ∀ m : ℕ, (∫ x : ℝ in (0 : ℝ)..1,
      a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) * cexp (-(2 * π * I * q * x))) =
      if m = q then a q * (Real.exp (-(2 * π * q * y)) : ℂ) else 0 := by
    intro m
    have hfun : (fun x : ℝ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) *
        cexp (-(2 * π * I * q * x))) = fun x : ℝ =>
        (a m * (Real.exp (-(2 * π * m * y)) : ℂ)) *
          cexp (2 * π * I * (((m : ℤ) - (q : ℤ) : ℤ) : ℂ) * x) := by
      funext x
      have h3 := exp_split (m : ℝ) x y
      rw [ofReal_natCast] at h3
      have h4 : cexp (2 * π * I * (((m : ℤ) - (q : ℤ) : ℤ) : ℂ) * x) =
          cexp (((2 * π * m * x : ℝ) : ℂ) * I) * cexp (-(2 * π * I * q * x)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [h3, h4]; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_int]
    by_cases h : m = q
    · subst h; simp
    · have : ((m : ℤ) - (q : ℤ)) ≠ 0 := by omega
      simp [h, this]
  simp_rw [hval] at key
  exact key.unique (hasSum_ite_eq q _)

lemma conj_inv_apply {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (u : ZMod M) :
    conj (ψ⁻¹ u) = ψ u := by
  have h := MulChar.star_apply' ψ⁻¹ u
  simpa using h

theorem unfolding_of_bound : B2 → HorizontalIntegralTwisted := by
  intro hB k N M ν _ _ hM χ f a hf ψ hν hψ y hy
  have : Fact (1 < M) := ⟨hM⟩
  have hz : ∀ x : ℝ, 0 < ((x : ℂ) + y * I).im := fun x => by simpa using hy
  let z : ℝ → UpperHalfPlane := fun x => ⟨(x : ℂ) + y * I, hz x⟩
  let F : ℝ → ℂ := fun x => f (z x)
  let P : ℤ → ℂ := fun n => ψ⁻¹ (n : ZMod M)
  have hψ0 : ∀ φ : DirichletCharacter ℂ M, φ 0 = 0 := fun φ =>
    MulChar.map_nonunit φ not_isUnit_zero
  have hP0 : P 0 = 0 := by simp [P, hψ0]
  have hP1 : ∀ n, ‖P n‖ ≤ 1 := fun n => DirichletCharacter.norm_le_one _ _
  obtain ⟨-, -, hsum, -⟩ := hB P ν hν hP0 hP1
  have hs : ∀ x : ℝ, HasSum (fun m : ℕ => a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))) (F x) :=
    fun x => hf.exp (z x)
  have hnA : ∀ (m : ℕ) (x : ℝ), ‖a m * cexp (2 * π * I * m * ((x : ℂ) + y * I))‖ =
      ‖a m‖ * Real.exp (-(2 * π * m * y)) := by
    intro m x
    have h3 := norm_exp_height (m : ℝ) x y
    push_cast at h3
    rw [norm_mul, h3]
  have hsumA : Summable fun m : ℕ => ‖a m‖ * Real.exp (-(2 * π * m * y)) := by
    have := summable_norm_iff.mpr (hs 0).summable
    simpa only [hnA] using this
  have hFc : Continuous F := by
    have : F = fun x : ℝ => ∑' m : ℕ, a m * cexp (2 * π * I * m * ((x : ℂ) + y * I)) :=
      funext fun x => (hs x).tsum_eq.symm
    rw [this]
    exact continuous_tsum (fun m => by fun_prop) hsumA (fun m x => (hnA m x).le)
  have hC : ∀ x, ‖F x‖ ≤ ∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * m * y)) := fun x =>
    (hs x).norm_le_of_bounded hsumA.hasSum (fun m => (hnA m x).le)
  set C := ∑' m : ℕ, ‖a m‖ * Real.exp (-(2 * π * m * y)) with hCdef
  let t : ℤ → ℝ → ℂ := fun n x => P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * ((x : ℂ) + y * I))
  have htc : ∀ n, Continuous (t n) := fun n => by
    simp only [t, ee]; fun_prop
  have hee : ∀ (n : ℤ) (x : ℝ), ee ((n : ℂ) ^ 2 * ((x : ℂ) + y * I)) =
      cexp (((2 * π * ((n : ℝ) ^ 2) * x : ℝ) : ℂ) * I) * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) := by
    intro n x
    rw [← exp_split, ee]; congr 1; push_cast; ring
  have hnt : ∀ n x, ‖t n x‖ = ‖t n 0‖ := by
    intro n x
    simp only [t, norm_mul, hee, norm_exp_ofReal_mul_I]
  have hsum0 : Summable fun n => ‖t n 0‖ := hsum (z 0)
  have hHS : ∀ x : ℝ, HasSum (fun n => t n x) (th P ν ((x : ℂ) + y * I)) := fun x =>
    ((hsum (z x)).of_norm).hasSum
  have key : HasSum (fun n : ℤ => ∫ x : ℝ in (0 : ℝ)..1, F x * conj (t n x))
      (∫ x : ℝ in (0 : ℝ)..1, F x * conj (th P ν ((x : ℂ) + y * I))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => C * ‖t n 0‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (hFc.mul (continuous_conj.comp (htc n))).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x _ => ?_
      rw [norm_mul, RCLike.norm_conj, hnt n x]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
    · exact Eventually.of_forall fun x _ => hsum0.mul_left C
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x _ => ?_
      exact ((hHS x).map (starRingEnd ℂ) continuous_conj).mul_left (F x)
  let h : ℤ → ℂ := fun n => ψ (n : ZMod M) * (n : ℂ) ^ ν *
    (a (n.natAbs ^ 2) * (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ))
  have hval : ∀ n : ℤ, (∫ x : ℝ in (0 : ℝ)..1, F x * conj (t n x)) = h n := by
    intro n
    have hqZ : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by simp
    have hqR : ((n.natAbs ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
      rw [← Int.cast_natCast (R := ℝ), hqZ, Int.cast_pow]
    have hqC : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
      rw [← Int.cast_natCast (R := ℂ), hqZ, Int.cast_pow]
    have hco := coeff_integral F a y hs hsumA (n.natAbs ^ 2)
    rw [hqC, hqR] at hco
    have hfun : (fun x : ℝ => F x * conj (t n x)) = fun x : ℝ =>
        (ψ (n : ZMod M) * (n : ℂ) ^ ν * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ)) *
          (F x * cexp (-(2 * π * I * (n : ℂ) ^ 2 * x))) := by
      funext x
      have hc : conj (cexp (((2 * π * ((n : ℝ) ^ 2) * x : ℝ) : ℂ) * I)) =
          cexp (-(2 * π * I * (n : ℂ) ^ 2 * x)) := by
        rw [← Complex.exp_conj]; congr 1
        simp only [map_mul, conj_ofReal, conj_I]
        push_cast; ring
      simp only [t, hee, map_mul, map_pow, conj_ofReal, map_intCast, P, conj_inv_apply, hc]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hco]
    simp only [h]
    have hR : (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ) =
        (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) * (Real.exp (-(2 * π * ((n : ℝ) ^ 2) * y)) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [hR]; ring
  simp_rw [hval] at key
  have h0 : h 0 = 0 := by simp [h, hψ0]
  have hfold := key.nat_add_neg
  rw [h0, add_zero] at hfold
  convert hfold using 1
  funext n
  have hneg : ψ (-(n : ZMod M)) = (-1) ^ ν * ψ (n : ZMod M) := by
    rw [← hψ, ← map_mul]; congr 1; ring
  have h1 : ((-1 : ℂ) ^ ν) * (-1) ^ ν = 1 := by
    rw [← mul_pow]; simp
  simp only [h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_natCast, Int.cast_neg, hneg,
    even_two, Even.neg_pow]
  rw [neg_pow (n : ℂ) ν]
  linear_combination (-(ψ (n : ZMod M) * (n : ℂ) ^ ν * a (n ^ 2) *
    (Real.exp (-(4 * π * (n : ℝ) ^ 2 * y)) : ℂ))) * h1

end GlobalTheory.CompanionTheory.HalfIntegralWeight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitAEPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eventually_one (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E)
    (hP : (δ * thE E n δ).val.charpoly.Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w n ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w n →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w n) ∧
      ∀ t ∈ twCent (thL n w) (locEl n w δ),
        IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) → t ∈ GlobalTheory.LFun.KGL w n := by
  filter_upwards [GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers E _ hP, GlobalTheory.BCT.GoodInt.eventually_mem_KGL δ,
    GlobalTheory.BCT.GoodInt.eventually_mem_KGL (δ * thE E n δ)] with w hgood hd hN
  obtain ⟨-, hinv, hKθ, -, -, -, -, -, hchar, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w n := by
    unfold locEl
    split_ifs
    · exact hN
    · exact hd
  have hgood' : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    rw [hchar δ]; exact hgood
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := by
    unfold nrmL
    split_ifs with hs
    · exact hy
    · have h2 : thetaGL n (cj w) (locEl n w δ) = thL n w (locEl n w δ) := by
        unfold thL; rw [if_neg hs]
      rw [h2]; exact mul_mem hy (hKθ _ hy)
  refine ⟨hy, fun g hg => ?_, fun t ht hc => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood'
      rw [hθ1] at hg ⊢
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
    · obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs _ g hy hgood' hg
      exact ⟨t, ht, by simpa using hk⟩
  · refine GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w (locEl n w δ)) t hNK hgood' ?_ hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w (locEl n w δ) = locEl n w δ * thL n w (locEl n w δ) := by
        unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
      rw [hn1]
      calc t * (locEl n w δ * thL n w (locEl n w δ))
          = locEl n w δ * thL n w t * thL n w (locEl n w δ) := by rw [← mul_assoc, ht']
        _ = locEl n w δ * thL n w (t * locEl n w δ) := by simp only [map_mul, mul_assoc]
        _ = locEl n w δ * thL n w (locEl n w δ * thL n w t) := by rw [ht']
        _ = locEl n w δ * thL n w (locEl n w δ) * t := by simp only [map_mul, hinv, mul_assoc]

theorem isCompact_fst {A B : Type} [Group A] [TopologicalSpace A] [T2Space A] [Group B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  refine (h.image continuous_fst).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem isCompact_snd {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] [T2Space B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] (t : A × B)
    (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  refine (h.image continuous_snd).closure_of_subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem main : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have e₁ := eventually_one hU a δ₁ h₁.2.2.1
  have e₂ := eventually_one hU b δ₂ h₂.2.2.1
  have hT : Tendsto (Subtype.val : {w : Pl E // w ∈ S} → Pl E) cofinite cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [hT.eventually e₁, hT.eventually e₂] with w hw₁ hw₂ y hy
  subst hy
  obtain ⟨i₁, u₁, c₁⟩ := hw₁
  obtain ⟨i₂, u₂, c₂⟩ := hw₂
  refine ⟨⟨i₁, i₂⟩, fun g hg => ?_, (Subgroup.closure_le _).2 ?_⟩
  · obtain ⟨t₁, ht₁, k₁⟩ := u₁ g.1 hg.1
    obtain ⟨t₂, ht₂, k₂⟩ := u₂ g.2 hg.2
    refine ⟨(t₁, t₂), ?_, ⟨k₁, k₂⟩⟩
    exact Prod.ext ht₁ ht₂
  · rintro t ⟨ht, hc⟩
    have ht' : t * _ = _ * _ := ht
    exact ⟨c₁ t.1 (congrArg Prod.fst ht') (isCompact_fst t hc), c₂ t.2 (congrArg Prod.snd ht') (isCompact_snd t hc)⟩

end GlobalTheory.CompanionTheory.UnitAEPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSet
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil

def dilHomeo {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (M : ℕ) (u : Aˣ) :
    (Fin 1 → Fin M → A) ≃ₜ (Fin 1 → Fin M → A) where
  toFun X p k := (u : A) * X p k
  invFun X p k := ((u⁻¹ : Aˣ) : A) * X p k
  left_inv X := by
    funext p k
    simp
  right_inv X := by
    funext p k
    simp
  continuous_toFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))

theorem linearIndependent_dil {A : Type} [CommRing A] {M : ℕ} (u : Aˣ) (X : Fin 1 → Fin M → A)
    (hX : LinearIndependent A X) :
    LinearIndependent A (fun (p : Fin 1) (k : Fin M) => (u : A) * X p k) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  have h0 : ∑ i, (g i * (u : A)) • X i = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := hX (fun i => g i * (u : A)) h0 i
  exact (Units.mul_left_eq_zero u).1 h1

theorem dil_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ M v u P hc ho hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := TopK.isTopRing (Fv F v)
  refine ⟨hc.image (dilHomeo M u).continuous, (dilHomeo M u).isOpenMap _ ho, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact linearIndependent_dil u X (hP hX)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagCoset

theorem v_eq_of_ne {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h0]
  simp

theorem diagT_mem_iwGL {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (τ : Fin n → (w.adicCompletion E)ˣ) (hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ ∈ iwGL n w := by
  have hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1 := by
    intro i
    have : (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹ := by
      simp
    rw [this, map_inv₀, hτ, inv_one]
  have hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1 := by
    intro ρ hρ i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hρ]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩
  · rw [← map_inv]
    exact hle _ hinv
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem fU_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz
  obtain ⟨hUL, hiw, -, hdiag⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hrev := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2

  set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef
  have hvϖ : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [v_eq_of_ne ϖ.ne_zero, hϖ.1]
  have hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  have hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1 := by
    intro i
    have e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      simp [hτdef]
    rw [e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u =
      tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
    rw [tdiag, ← map_mul]
    congr 1
    funext i
    simp [hτdef]

  have hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1 := by
    have h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w := hγ ▸ γ.2
    exact (hdiag u).1 ((hUL _).1 h1)
  have hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]
  have hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1 := by
    intro i
    have e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      intro j
      simp [hτdef]
    rw [e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]
    have h2 := hu1 i
    have hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    calc _ = (cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E)) *
          ((((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ *
            (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hp, one_mul]
  have hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w :=
    (hUL _).2 ((hdiag τ).2 hτ1)
  let κ : UL n w := ⟨_, hκU⟩
  have hκ : κ ∈ iwU n w b := by
    rw [hiw]
    have : b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
      change b⁻¹ * (b * _ * b⁻¹) * b = _
      group
    rw [this]
    exact diagT_mem_iwGL w n τ hτ
  unfold fU
  refine if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩
  change x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)
  rw [hγ, hfac]
  group

end GlobalTheory.CompanionTheory.DiagCoset
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFiniteStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_points_height_bound_finite : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | exact GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Mahler.exists_isCompact_of_le_hgt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightEx
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.WeightExist

theorem weightEx : PositivityTheory.Rg.BcB.F.WeightEx :=
  fun E _ _ _ n π hπ τ => (GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) τ).exists

end GlobalTheory.CompanionTheory.WeightExist
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitoneStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_exponent_strictly_antitone : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l → StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  first | exact @GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | exact GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | (intros; apply GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev <;> assumption)
end

