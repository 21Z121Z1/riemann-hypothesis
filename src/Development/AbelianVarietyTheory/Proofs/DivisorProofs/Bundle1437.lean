import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNeg
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw
  exact GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.NormOneProper

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  intro E _ _ _ hU n w y hy C hC
  by_cases hs : IsSplitAt w
  · refine ⟨{1}, isCompact_singleton, fun z hz _ => ⟨z, ?_, 1, rfl, (mul_one z).symm⟩⟩
    have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    have h2 : nrmL n w y = y := by rw [nrmL, if_pos hs]
    rw [h2] at hz
    change z * y = y * thL n w z
    rw [h1, MonoidHom.id_apply, hz]
  · set K := w.adicCompletion E
    obtain ⟨-, hinv, hv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    letI : StarRing K :=
      { star := cj w
        star_involutive := hinv
        star_mul := fun a b => by rw [map_mul, mul_comm]
        star_add := map_add (cj w) }
    have hse : starRingEnd K = cj w := RingHom.ext fun _ => rfl
    have hθ : thL n w = thetaGL n (starRingEnd K) := by rw [thL, if_neg hs, hse]
    have hθv : ∀ g : GLw n w, (thL n w g).val = GlobalTheory.Tw.theta g.val := fun g => by
      rw [hθ]; exact thetaGL_val g
    have hN : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
      rw [nrmL, if_neg hs, ← hse, Units.val_mul, thetaGL_val]; rfl
    have hReg : GlobalTheory.Tw.Reg (y.val) := ⟨y.isUnit, by rw [← hN]; exact hy⟩
    have TC := GlobalTheory.Tw.twisted_centraliser n K y.val hReg
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    have hnorm : ∀ x : K, ‖star x‖ = ‖x‖ := fun x => by
      simp only [Valued.toNormedField.norm_def]
      have h1 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (star x)
      have h2 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x
      have h3 : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict (star x) =
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x :=
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans ((hv x).trans h2.symm))
      rw [h3]
    set C' : Set (GLw n w) := (fun c : GLw n w => y * c⁻¹) '' C
    have hC' : IsCompact C' := hC.image (by fun_prop)
    obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact K hnorm n y.val hReg C' hC'
    refine ⟨D, hD, fun z hz hzC => ?_⟩
    have hzv : z.val * GlobalTheory.Tw.nrm y.val = GlobalTheory.Tw.nrm y.val * z.val := by
      rw [← hN, ← Units.val_mul, hz, Units.val_mul]
    have hzA : z.val ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} := (TC.2.2.2.2.1 z.val).1 hzv
    have hcomm : ∀ x ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}, z.val * x = x * z.val := by
      intro x hx
      have hle : Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} ≤ Subalgebra.centralizer K {z.val} := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hzv
      exact hle hx z.val (Set.mem_singleton _)
    have hadj : GlobalTheory.Tw.adj y.val z.val = (y * (thL n w z)⁻¹ * y⁻¹).val := by
      rw [Units.val_mul, Units.val_mul, ← map_inv, hθv, GlobalTheory.Tw.theta, GlobalTheory.Tw.adj]
      have hzi : ((z⁻¹ : GLw n w).val)⁻¹ = z.val := by
        rw [Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit)]
      rw [hzi, Matrix.coe_units_inv y]
      simp only [Matrix.mul_assoc]
    have hu : (y * (z⁻¹ * y * thL n w z)⁻¹).val = z.val * GlobalTheory.Tw.adj y.val z.val := by
      rw [hcomm _ (TC.2.2.2.1 _ hzA).1, hadj]
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    obtain ⟨t, htA, ht1, d, hd, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
    refine ⟨t, ?_, d, hd, rfl⟩
    have htc : t.val ∈ GlobalTheory.Tw.cent y.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
    change t * y = y * thL n w t
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hθv]; exact htc.2)

end GlobalTheory.NormOneProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfSumSqLtOne
section
namespace GlobalTheory.NormBoundSumSquares

theorem norm_le_one_of_sum_sq_lt_one :
    (let d1 : {E : Type} → [inst : Field E] → [NumberField E] → {a : ℕ} → GlobalTheory.CuspRep.Lie E a → ℝ := @(fun {E : Type} [Field E] [NumberField E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a) ↦ ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ)); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a), d1 x < (1 : ℝ) → ‖x‖ ≤ (1 : ℝ)) := by
  intro d1 E _ _ _ a x hx
  have hsum : ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ) < 1 := hx
  have entry : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E), ‖x i j w‖ ≤ 1 := by
    intro i j w
    by_contra hcon
    have hgt : 1 < ‖x i j w‖ := lt_of_not_ge hcon
    have hsq : 1 < ‖x i j w‖ ^ (2 : ℕ) := one_lt_pow₀ hgt (by norm_num)
    have h₃ : ‖x i j w‖ ^ (2 : ℕ) ≤ ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun j' => ‖x i j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h₂ : ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ)
        ≤ ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₁ : ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ)
        ≤ ∑ w' : NumberField.InfinitePlace E, ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun w' => ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ w)
    linarith
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => entry i j w

end GlobalTheory.NormBoundSumSquares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegment
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem norm_sub_le_of_lieD_unipotent_segment (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ)
    (hn : n * n = 0) (hu : ∀ τ : ℝ, (u τ).val = 1 + τ • n)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) :
    ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  have h0 : u 0 = 1 := Units.ext (by rw [hu]; simp)
  have hadd : ∀ τ s : ℝ, u (τ + s) = u τ * u s := by
    intro τ s
    refine Units.ext ?_
    rw [Units.val_mul, hu, hu, hu]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hn, smul_zero, add_zero, add_smul]
    abel
  have hc : HasDerivAt (fun t => toL (u t).val) (toL n) 0 := by
    have e : (fun t : ℝ => toL (u t).val) = fun t : ℝ => oneL E a + t • toL n := by
      funext t; rw [hu]; rfl
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL n)).const_add (oneL E a)
  have hd : ∀ τ : ℝ, HasDerivAt (fun t => ψ.1 (g * infGL E a (u t)))
      (lieD (toL n) ψ.1 (g * infGL E a (u τ))) τ := by
    intro τ
    have h1 := hasDerivAt_curve ψ (g * infGL E a (u τ)) u (toL n) h0 hc
    have h2 : HasDerivAt (fun s => ψ.1 (g * infGL E a (u τ) * infGL E a (u s)))
        (lieD (toL n) ψ.1 (g * infGL E a (u τ))) (τ - τ) := by rwa [sub_self]
    have h3 := h2.comp_sub_const τ τ
    have e : (fun t => ψ.1 (g * infGL E a (u τ) * infGL E a (u (t - τ)))) =
        fun t => ψ.1 (g * infGL E a (u t)) := by
      funext t
      rw [mul_assoc, ← map_mul, ← hadd, add_sub_cancel]
    rwa [e] at h3
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => ψ.1 (g * infGL E a (u t)))
    (fun τ _ => (hd τ).hasDerivWithinAt) (fun τ hτ => hM τ (Set.Ico_subset_Icc_self hτ))
  simpa [h0] using h

end GlobalTheory.CuspRapid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  first | exact @GlobalTheory.LeviDesc.hint_comp_linear | exact GlobalTheory.LeviDesc.hint_comp_linear | (intros; apply GlobalTheory.LeviDesc.hint_comp_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_eq_of_mem (e : G ≃ₜ* H) (A : Subgroup G) (A' : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ A') :
    A' = A.map (e : G →* H) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg

theorem cptPart_map_equiv (e : G ≃ₜ* H) (T : Subgroup G) :
    cptPart (T.map (e : G →* H)) = (cptPart T).map (e : G →* H) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hz : ∀ t, (Subgroup.zpowers ((e : G →* H) t) : Set H) = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    rfl
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((e : G →* H) t) : Set H)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem twCent_mem (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (he : ∀ g, e (θ g) = θ' (e g)) (δ g : G) :
    g ∈ twCent θ δ ↔ e g ∈ twCent θ' (e δ) := by
  rw [mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem summand_map (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G)
    (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g)) (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    (hf : ∀ g, f' (e g) = f g) (y : G) :
    summand θ' K' (e δ) f' (e y) = summand θ K δ f y := by
  have hT : twCent θ' (e δ) = (twCent θ δ).map (e : G →* H) :=
    map_eq_of_mem e _ _ (twCent_mem e θ θ' he δ)
  have hK' : K' = K.map (e : G →* H) := map_eq_of_mem e _ _ hK
  subst hK'
  unfold summand
  congr 1
  · have h1 : (K.map (e : G →* H)).map (MulAut.conj (e y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map (e : G →* H) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [h1, hT, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  · let ψ : K ≃* (K.map (e : G →* H)) := e.toMulEquiv.subgroupMap K
    rw [← GlobalTheory.BCT.OrbProd.avg_comp_equiv ψ]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [← hf]
    congr 1
    show (e y * e k.1)⁻¹ * e δ * θ' (e y * e k.1) = _
    rw [← map_mul, ← he, ← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

def dcMap (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) :
    DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set H) (K' : Set H) :=
  fun q => DoubleCoset.mk T' K' (e (Quotient.out q))

theorem dcMap_bij (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') : Function.Bijective (dcMap e T K T' K') := by
  constructor
  · intro q1 q2 h
    obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ _ _).1 h
    rw [← DoubleCoset.out_eq' T K q1, ← DoubleCoset.out_eq' T K q2, DoubleCoset.eq]
    refine ⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hab
  · intro q'
    refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))
    unfold dcMap
    rw [hab]
    conv_rhs => rw [← DoubleCoset.out_eq' T' K' q']
    rw [DoubleCoset.eq]
    refine ⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    group

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

theorem twOrb_transport : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G) (f : G → ℂ) (f' : H → ℂ), (∀ g, e (θ g) = θ' (e g)) → (∀ g, g ∈ K ↔ e g ∈ K') → (∀ g, f' (e g) = f g) → twOrb θ K δ f = twOrb θ' K' (e δ) f' := by
  intro G H _ _ _ _ _ _ e θ θ' K K' δ f f' he hK hf
  have hT := twCent_mem e θ θ' he δ
  rw [twOrb_eq, twOrb_eq,
    ← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK))]
  refine finsum_congr fun q => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e δ)) K' (e (Quotient.out q))
  have e2 : Quotient.out (Equiv.ofBijective _ (dcMap_bij e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK) q) =
      a * e (Quotient.out q) * b := hab
  rw [e2, summand_rep θ' K' (e δ) f' _ ha hb, summand_map e θ θ' K K' δ f f' he hK hf]

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cPl_eq {u : Pl E} (hu : ¬ IsSplitAt u) : cPl E u = u :=
  (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 hu

theorem orb_eq {u : Pl E} (hu : ¬ IsSplitAt u) : orb E u = {u} := by
  simp [orb, cPl_eq hu]

theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG_of_mem (T : Finset (Pl E)) (w : Pl E) (hw : w ∈ T) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = GeneralLinearGroup.map (pLoc E w) x := by
  ext i j
  simp [prjG, prjM, pLoc_idem, hw, Matrix.one_apply]
  split_ifs <;> simp [map_sub, pLoc_idem, hw]

theorem pLoc_prjG_of_not_mem (T : Finset (Pl E)) (w : Pl E) (hw : w ∉ T) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = 1 := by
  ext i j
  simp [prjG, prjM, pLoc_idem, hw, Matrix.one_apply]
  split_ifs <;> simp [map_sub, pLoc_idem, hw]

end GlobalTheory.EulerTw.Inert

namespace GlobalTheory.EulerTw.Inert

open GlobalTheory.EulerTw

theorem gam_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (u w : Pl E) (hw : w ∉ orb E u)
    (g : Gam E n u) : GeneralLinearGroup.map (pLoc E w) g.1 = 1 := by
  obtain ⟨x, hx⟩ := g.2
  rw [← hx]
  exact pLoc_prjG_of_not_mem _ _ hw x

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ δ : GL (Fin n) E, (δ * thE E n δ).val.charpoly.Separable → ∀ u ∈ S, ¬ IsSplitAt u → twOrb (GlobalTheory.EulerTw.thU E n u) (GlobalTheory.EulerTw.KU E n u) (GlobalTheory.EulerTw.pfU E n u (ratF E n δ)) (GlobalTheory.EulerTw.FU E n S φ u) = twOrb (thL n u) (GlobalTheory.LFun.KGL u n) (locEl n u δ) (φ u) := by
  intro E _ _ _ hU n S hS K' hK' φ hφ δ hδ u huS hu
  obtain ⟨e, he⟩ := GlobalTheory.T.nonsplit_unitary_group_iso_gl E n u hu
  have hcj := ((GlobalTheory.ConjAtPlace.main E hU u).2.2.2.1 hu).2.2.1
  have hmem : u ∈ orb E u := by simp [orb]
  rw [GlobalTheory.EulerTw.Transport.twOrb_transport (Gam E n u) (GLw n u) e (thU E n u) (thL n u) (KU E n u) (GlobalTheory.LFun.KGL u n) _
    (FU E n S φ u) (φ u) ?_ ?_ ?_]
  · congr 1
    rw [he]
    show GeneralLinearGroup.map (pLoc E u) (prjG E n (orb E u) (ratF E n δ)) = locEl n u δ
    rw [pLoc_prjG_of_mem _ _ hmem]
    simp only [locEl, if_neg hu, ratF]
    ext i j
    rfl
  · intro g
    rw [he, he]
    show GeneralLinearGroup.map (pLoc E u) (prjG E n (orb E u) (thF E n g.1)) = _
    rw [pLoc_prjG_of_mem _ _ hmem, thL, if_neg hu, thF]
    exact GlobalTheory.ThetaPull.map_thetaGL (pLoc E u) _ (cj u) hcj g.1
  · intro g
    rw [he, KU, Subgroup.mem_subgroupOf, Kglob, Subgroup.mem_iInf]
    constructor
    · intro h
      exact h u
    · intro h w
      rw [Subgroup.mem_comap]
      by_cases hw : w = u
      · subst hw
        exact h
      · rw [gam_one u w (by rw [orb_eq hu]; simpa using hw) g]
        exact one_mem _
  · intro g
    have h1 : S ∩ ↑(orb E u) = {u} := by
      rw [orb_eq hu]
      ext w
      simp only [Set.mem_inter_iff, Finset.coe_singleton, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨huS, rfl⟩
    have h2 : Sᶜ ∩ ↑(orb E u) = ∅ := by
      rw [orb_eq hu]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.coe_singleton, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro hw rfl
      exact hw huS
    rw [FU, h1, h2, finprod_mem_singleton, finprod_mem_empty, mul_one, he]

end GlobalTheory.EulerTw.Inert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeLStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  first | exact @GlobalTheory.RallisEuler.trivPar_euler | exact GlobalTheory.RallisEuler.trivPar_euler | (intros; apply GlobalTheory.RallisEuler.trivPar_euler <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuumStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVac.sumPl_heisOp_vacuum | exact GlobalTheory.FockVac.sumPl_heisOp_vacuum | (intros; apply GlobalTheory.FockVac.sumPl_heisOp_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusConeStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone : ∀ (r m e : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤ C * ∏ i, t i ^ e := by
  first | exact @GlobalTheory.ConeMax.prod_max_le_prod | exact GlobalTheory.ConeMax.prod_max_le_prod | (intros; apply GlobalTheory.ConeMax.prod_max_le_prod <;> assumption)
end

