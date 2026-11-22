import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorWedgeEqOfLocalizedSpan
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.WedgeDen

theorem alternatingMap_sum_smul_eq_det_smul' {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    f (fun i => ∑ l, a i l • g l) = (Matrix.of a).det • f g := by
  first
  | exact @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | (apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination ..)

theorem exists_smul_ιMulti_eq_smul_ιMulti : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  intro R L M _ _ _ _ _ S n g w h
  classical
  choose r hr c hc using h
  refine ⟨∏ i, r i, prod_mem fun i _ => hr i, (Matrix.of c).det, ?_⟩
  rw [map_prod, ← AlternatingMap.map_smul_univ]
  simp_rw [hc]
  rw [alternatingMap_sum_smul_eq_det_smul', RingHom.map_det]
  rfl

end GlobalTheory.WedgeDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedUnitsModRatNorms
section
open scoped TensorProduct Classical

namespace GlobalTheory.EtaleCls

theorem classes_mod_rat_norms : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ j : E, IsUnit j → τ j = -j → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  intro E _ _ _ _ τ hτ _j _ _ S
  obtain ⟨A, hA⟩ := GlobalTheory.T.normClassFinite_of_reduced_rat_algebra GlobalTheory.T.exists_finite_classes_modulo_involutionNorms E τ hτ S
  exact ⟨A, GlobalTheory.T.involution_norm_class_remove_rational_factor E τ S A hA⟩

end GlobalTheory.EtaleCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOverGenericFibreOfEtaleStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.finite_closure) | (exact GlobalTheory.KeyOriginNoeth.finite_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.finite_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosure
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem projective_of_isScalarTower_projective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Projective R A]
    [Module.Projective A M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  have : Module.Projective R (M →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R : (M →₀ A) ≃ₗ[R] Π₀ _ : M, A).symm
  exact Module.Projective.of_split ((s.restrictScalars R))
    ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun m => LinearMap.congr_fun hs m)

open KaehlerDifferential in

theorem _root_.GlobalTheory.finite_projective_span_of_integralClosure :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  intro k F K _ _ _ _ _ _ _ A B hB hfin hproj W _ _ _ _ S hS hfinB hprojB
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a =>
    (hB _).2 ((integralClosure A K).algebraMap_mem a)
  letI : Algebra A B := ((algebraMap A K).codRestrict B hAB).toAlgebra
  have hcoe : ∀ (a : A) (b : B), ((a • b : B) : K) = algebraMap F K (a : F) * (b : K) := by
    intro a b
    rw [Algebra.smul_def]
    rfl
  haveI : IsScalarTower A B W := ⟨fun a b w => by
    rw [Subalgebra.smul_def, hcoe, mul_smul, algebraMap_smul, Subalgebra.smul_def,
      Subalgebra.smul_def]⟩
  let ψ : B ≃ₗ[A] integralClosure A K :=
    { toFun := fun b => ⟨b, (hB b).1 b.2⟩
      invFun := fun c => ⟨c, (hB c).2 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => Subtype.ext <| by
        rw [hcoe, RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite A B := Module.Finite.equiv ψ.symm
  haveI : Module.Projective A B := Module.Projective.of_equiv ψ.symm
  haveI : Module.Finite A (Submodule.span B S) := Module.Finite.trans B _
  haveI : Module.Projective A (Submodule.span B S) := projective_of_isScalarTower_projective A B _
  have hclosed : ∀ c : B, ∀ w ∈ Submodule.span A S, c • w ∈ Submodule.span A S := by
    intro c w hw
    induction hw using Submodule.span_induction with
    | mem s hs =>
      rw [Subalgebra.smul_def]
      exact Submodule.subset_span (hS c c.2 s hs)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
    | smul a v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ a hv
  let SB : Submodule B W :=
    { carrier := Submodule.span A S
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c w hw => hclosed c w hw }
  have hsets : ∀ w, w ∈ Submodule.span A S ↔ w ∈ Submodule.span B S := by
    intro w
    constructor
    · intro hw
      have hle : Submodule.span A S ≤ (Submodule.span B S).restrictScalars A :=
        Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
      exact hle hw
    · intro hw
      have hle : Submodule.span B S ≤ SB :=
        Submodule.span_le.mpr fun s hs => (Submodule.subset_span hs : s ∈ Submodule.span A S)
      exact hle hw
  let χ : Submodule.span A S ≃ₗ[A] Submodule.span B S :=
    { toFun := fun w => ⟨w, (hsets w).1 w.2⟩
      invFun := fun w => ⟨w, (hsets w).2 w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.equiv χ.symm, Module.Projective.of_equiv χ.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMaximalMinorLocallyConstantStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_maximal_minor_locally_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  first | exact @GlobalTheory.RankFibreKer.isFirstMax_eventually | exact GlobalTheory.RankFibreKer.isFirstMax_eventually | (intros; apply GlobalTheory.RankFibreKer.isFirstMax_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  first | exact @GlobalTheory.DiagVol.colE_mem_symN_KO | exact GlobalTheory.DiagVol.colE_mem_symN_KO | (intros; apply GlobalTheory.DiagVol.colE_mem_symN_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGramDensityInequalityComplex
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.FlagGram

theorem cube_cbrt (t : ℝ) (ht : 0 ≤ t) : (t ^ (1/3:ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem rpow_neg_four_thirds (t : ℝ) (ht : 0 ≤ t) :
    t ^ (-(4/3:ℝ)) = ((t ^ (1/3:ℝ)) ^ 4)⁻¹ := by
  rw [Real.rpow_neg ht, ← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem sq_mul_le_cubes (a w : ℝ) (ha : 1 ≤ a) (hw : 1 ≤ w) :
    a ^ 2 * w ≤ a ^ 3 + w ^ 3 - 1 := by
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  rcases le_total a w with h | h
  · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ w) (sub_nonneg.2 h)) (by linarith : (0:ℝ) ≤ w + a)]
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h)]

theorem key (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hBD : B ≤ D) :
    ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤
      (1 + A) ^ (-(4 / 3 : ℝ)) * (1 + C) ^ (-(4 / 3 : ℝ)) *
        ((1 + B) ^ (-(4 / 3 : ℝ)) + (1 + D) ^ (-(4 / 3 : ℝ))) := by
  rw [rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith),
    rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith)]
  have eA := cube_cbrt (1 + A) (by linarith)
  have eB := cube_cbrt (1 + B) (by linarith)
  have eC := cube_cbrt (1 + C) (by linarith)
  have hα : 1 ≤ (1 + A) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hβ : 1 ≤ (1 + B) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hγ : 1 ≤ (1 + C) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hδ : 0 < (1 + D) ^ (1/3:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  generalize (1 + A) ^ (1/3:ℝ) = α at *
  generalize (1 + B) ^ (1/3:ℝ) = β at *
  generalize (1 + C) ^ (1/3:ℝ) = γ at *
  generalize (1 + D) ^ (1/3:ℝ) = δ at *
  have hx : α ^ 2 * β ≤ 1 + A + B := by have := sq_mul_le_cubes α β hα hβ; linarith
  have hy : γ ^ 2 * β ≤ 1 + C + D := by have := sq_mul_le_cubes γ β hγ hβ; linarith
  have hp1 : 0 < α ^ 2 * β := by positivity
  have hp2 : 0 < γ ^ 2 * β := by positivity
  have hprod : (α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2 ≤ (1 + A + B) ^ 2 * (1 + C + D) ^ 2 := by
    gcongr
  have hδ4 : 0 < (δ ^ 4)⁻¹ := by positivity
  calc ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤ ((α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hprod
    _ = (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * (β ^ 4)⁻¹ := by
        rw [← mul_inv, ← mul_inv]; congr 1; ring
    _ ≤ (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * ((β ^ 4)⁻¹ + (δ ^ 4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end GlobalTheory.FlagGram

namespace GlobalTheory

theorem flagGram_density_ineq : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  intro a b c
  rcases le_total (‖b‖ ^ 2) (‖a * c - b‖ ^ 2) with h | h
  · exact FlagGram.key _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) h
  · have := FlagGram.key (‖c‖ ^ 2) (‖a * c - b‖ ^ 2) (‖a‖ ^ 2) (‖b‖ ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity) h
    calc _ = ((1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2 * (1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2)⁻¹ := by
          rw [mul_comm]
      _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelExistsOfGiven
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

theorem GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow : ∀ (k K : Type) [Field k] [CharZero k] [Field K] [Algebra k K] (B : Subalgebra k K) (Q : Ideal B), Q.IsPrime → ∀ (s : B) (m : ℕ) (y : Fin m → K) (T : K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, (r : K) • D k K (v : K) = ∑ l, (c l : K) • (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) l) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * T = a * s ^ e) → ∃ N Dn : B, N ∉ Q ∧ Dn ∉ Q ∧ (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K T) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) = ((N : K) * (s : K) ^ (e - 1)) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) := by
  intro k K _ _ _ _ B Q hQ s m y T e he hs hgen ⟨a, r, ha, hr, hT⟩
  classical
  let g : Fin m → Ω[K⁄k] := fun j => D k K (y j)
  let f : Ω[K⁄k] →ₗ[K] ExteriorAlgebra K Ω[K⁄k] :=
    (ExteriorAlgebra.ιMulti K (m+1)).toMultilinearMap.toLinearMap (Fin.cons 0 g) 0
  have hf : ∀ v, f v = ExteriorAlgebra.ιMulti K (m+1) (Fin.cons v g : Fin (m+1) → Ω[K⁄k]) := by
    intro v; simp only [f, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]; rfl
  have hg0 : ∀ j, f (g j) = 0 := by
    intro j; rw [hf]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm
  have key : ∀ v : B, ∃ ρ : B, ρ ∉ Q ∧ ∃ c0 : B, (ρ : K) • f (D k K (v:K)) = (c0 : K) • f (D k K (s:K)) := by
    intro v
    obtain ⟨ρ, hρ, c, hc⟩ := hgen v
    refine ⟨ρ, hρ, c 0, ?_⟩
    have h2 := congrArg f hc
    rw [map_smul, map_sum, Fin.sum_univ_succ] at h2
    simpa [hg0, g] using h2
  obtain ⟨ρa, hρa, ca, hA⟩ := key a
  obtain ⟨ρr, hρr, cr, hR⟩ := key r
  have hse : (s:K)^e = (s:K) * (s:K)^(e-1) := by
    rw [← pow_succ']; congr 1; omega
  have hX : (r:K) • f (D k K T) + T • f (D k K (r:K)) = ((a:K) * (e:K) * (s:K)^(e-1)) • f (D k K (s:K)) + ((s:K) * (s:K)^(e-1)) • f (D k K (a:K)) := by
    have h1 := congrArg (fun z => f (D k K z)) hT
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_smul, map_nsmul] at h1
    rw [← hse, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul K]; exact h1
  have heB : (e : B) ∉ Q := by
    intro h
    have hu : IsUnit (e : B) := by
      have h3 : (e : B) = algebraMap k B (e : k) := by simp
      rw [h3]
      exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))).map _
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  refine ⟨ρa*ρr*(e:B)*a*r + s*(ρr*r*ca - ρa*a*cr), ρa*ρr*r^2, ?_, ?_, ?_⟩
  · intro h
    have h4 : ρa*ρr*(e:B)*a*r ∈ Q := by
      have := Q.sub_mem h (Q.mul_mem_right (ρr*r*ca - ρa*a*cr) hs)
      simpa using this
    rcases hQ.mem_or_mem h4 with h4 | h4
    · rcases hQ.mem_or_mem h4 with h4 | h4
      · rcases hQ.mem_or_mem h4 with h4 | h4
        · rcases hQ.mem_or_mem h4 with h4 | h4
          · exact hρa h4
          · exact hρr h4
        · exact heB h4
      · exact ha h4
    · exact hr h4
  · intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hρa h
      · exact hρr h
    · exact hr (hQ.mem_of_pow_mem _ h)
  · have hT' : (r:K) * T = (a:K) * ((s:K) * (s:K)^(e-1)) := by rw [hT, hse]
    rw [← hf, ← hf]
    push_cast
    linear_combination (norm := module) ((ρa:K)*ρr*r) • hX + ((ρr:K)*r*s*(s:K)^(e-1)) • hA - ((ρa:K)*r*T) • hR - ((ρa:K)*cr) • hT' • f (D k K (s:K))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  first | exact @GlobalTheory.DiagVol.rowElt_mem | exact GlobalTheory.DiagVol.rowElt_mem | (intros; apply GlobalTheory.DiagVol.rowElt_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProductStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_ferrandPushout_over_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  first | exact @GlobalTheory.FerrandFlat.flat_pushout | exact GlobalTheory.FerrandFlat.flat_pushout | (intros; apply GlobalTheory.FerrandFlat.flat_pushout <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSectionsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧ (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) → ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧ (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), val s V (P.map g.op x) = Sec.res g (val s U x)) ∧ (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x, val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧ (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x, val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧ ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x, val (s + s') U x = val s U x + val s' U x ∧ val (m • s) U x = m • val s U x := by
  first | exact @GlobalTheory.EtC.FreeHom.main | exact GlobalTheory.EtC.FreeHom.main | (intros; apply GlobalTheory.EtC.FreeHom.main <;> assumption)
end

