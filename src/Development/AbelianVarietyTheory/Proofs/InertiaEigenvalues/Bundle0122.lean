import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem intO_lift_of_val_nonneg (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  unfold val at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem intO_val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  have h1 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem intO_val_ne_zero_of_mem (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem intO : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O,
    @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  intro K K' d φ hU hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfr : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure K.O K'.E
  haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S
  haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S
  have hinj : Function.Injective (algebraMap K.O S) :=
    algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1
    (inferInstance : IsDedekindDomain S)

  have hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hU.2.2.1]; exact intO_val_algebraMap_nonneg K a
  choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let ψ : K.O →+* K'.O :=
    { toFun := ψf
      map_one' := hinj' (by rw [hψf]; simp)
      map_mul' := fun a b => hinj' (by simp [hψf])
      map_zero' := hinj' (by rw [hψf]; simp)
      map_add' := fun a b => hinj' (by simp [hψf]) }
  have hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a := fun a => hψf a

  have hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t := by
    intro t ht
    have : IsIntegral K'.O t :=
      IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  set x := algebraMap K'.O K'.E y with hx
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact s.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact isIntegral_zero
  by_cases hsu : IsUnit s
  · have hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1 := by
      have := hsu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
    have e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1 := by
      rw [← map_mul, hu1, map_one]
    have : x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) := by
      rw [eq_inv_of_mul_eq_one_left e, hs, inv_inv]
    rw [this]; exact ((hsu.unit⁻¹ : Sˣ) : S).2
  exfalso
  have hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n := fun n hn => by
    rw [IsLocalRing.eq_maximalIdeal hn]; exact (mem_maximalIdeal s).2 hsu
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨z, hz⟩ := hS _ t.2
  have h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1 := by
    have := congrArg (algebraMap S K'.E) ht
    rw [map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply] at this
    have h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N := this
    rw [map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow]
  have hu : IsUnit (ψ π) := by
    have : y ^ N * (ψ π * z) = 1 := hinj' (by rw [h1, map_one])
    exact IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)
  have h2 := GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu
  rw [hψ] at h2
  have h3 := hU.2.2.1 (algebraMap K.O K.E π)
  change val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2
  rw [h3] at h2
  exact intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunctionStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  first | exact @GlobalTheory.JR.descFn_isTest | exact GlobalTheory.JR.descFn_isTest | (intros; apply GlobalTheory.JR.descFn_isTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperatiStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  first | exact @GlobalTheory.JR.Hyp.isTest_ops | exact GlobalTheory.JR.Hyp.isTest_ops | (intros; apply GlobalTheory.JR.Hyp.isTest_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordinStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  first | exact @GlobalTheory.JR.Hyp.isTest_coord | exact GlobalTheory.JR.Hyp.isTest_coord | (intros; apply GlobalTheory.JR.Hyp.isTest_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportPartialFourierGLBStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isTest | exact GlobalTheory.JR.fourG_isTest | (intros; apply GlobalTheory.JR.fourG_isTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  first | exact @GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | exact GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | (intros; apply GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTestRepresentationTensorProductStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  first | exact @GlobalTheory.JR.WeilProd.isTestRep_tensorRep | exact GlobalTheory.JR.WeilProd.isTestRep_tensorRep | (intros; apply GlobalTheory.JR.WeilProd.isTestRep_tensorRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieReg
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem InvAlg.isReduced_of_lieReg : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A :=
  fun _ B h => GlobalTheory.SepGen.isReduced B.g h.2

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpolyStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniformizerIdempotentFrameProdStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUniformizerIdempotentFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  first | exact @GlobalTheory.UnitLemma.Desc.isFrame_prod | exact GlobalTheory.UnitLemma.Desc.isFrame_prod | (intros; apply GlobalTheory.UnitLemma.Desc.isFrame_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetConjugationMatrixIntegralBasis
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem conj_matrix_det_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
  intro K K' d φ hφ
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
  have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
  have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
    intro m l
    have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
      rw [hw]
      intro k
      rw [w.repr_self]
      by_cases h : l = k
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    obtain ⟨y, hy⟩ := h1
    obtain ⟨y', hy'⟩ := K'.c_int y
    have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
    exact (hw _).1 h2 m
  choose A hA using hint
  have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
    intro x n
    have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
      conv_lhs => rw [← w.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsm, hsm, map_mul, ← hφ]
    rw [hx, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
    ext n l
    have h := hrep (K'.c (w l)) n
    rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
    rw [eq_comm]
    convert h using 1
    · exact if_congr eq_comm rfl rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
    rfl
  have hdet : C.det * K.c C.det = 1 := by
    have h := congrArg Matrix.det hCC
    rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
    exact h
  have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
    rw [RingHom.map_det]
    congr 1
    ext m l
    simp [hA]
  refine ⟨(Matrix.of A).det, ?_, hdetA⟩
  obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
  apply IsUnit.of_mul_eq_one β
  apply IsFractionRing.injective K.O K.E
  rw [map_mul, ← hβ, hdetA, hdet, map_one]

end GlobalTheory.UnitLemma.Unr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitTraceFormDiscrUnramifiedExt
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResDisc

open IsLocalRing

theorem isUnit_discr_of_isMaximal_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field (Ideal.map (algebraMap R S) (maximalIdeal R))
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (basisQuotient b)
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    inferInstance
  have h1 : Ideal.Quotient.mk (maximalIdeal R) (Algebra.discr R b) =
      Algebra.discr (R ⧸ maximalIdeal R) (basisQuotient b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk]
  have h2 := Algebra.discr_not_zero_of_basis (R ⧸ maximalIdeal R) (basisQuotient b)
  rw [← h1] at h2
  by_contra h
  exact h2 (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 h))

theorem discr_trace_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (π : K.O) (π' : K'.O), algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) → IsLocalRing.maximalIdeal K.O = Ideal.span {π} → IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det := by
  intro K K' d φ _ π π' hππ' hm hm'
  letI : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hj : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective K'.O K'.E
  have hi : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  have hφ : ∀ e : K.E, φ e = algebraMap K.E K'.E e := fun _ => rfl

  have hlift : ∀ a : K.O, φ (algebraMap K.O K.E a) ∈ (algebraMap K'.O K'.E).range := by
    intro a
    apply (hw _).2
    intro k
    obtain ⟨c, hc⟩ := (hw 1).1 ⟨1, map_one _⟩ k
    refine ⟨a * c, ?_⟩
    have h1 : φ (algebraMap K.O K.E a) = (algebraMap K.O K.E a) • (1 : K'.E) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hc]
  let e : K'.O ≃+* (algebraMap K'.O K'.E).range :=
    RingEquiv.ofBijective (algebraMap K'.O K'.E).rangeRestrict
      ⟨fun x y h => hj (congrArg Subtype.val h), (algebraMap K'.O K'.E).rangeRestrict_surjective⟩
  let ι : K.O →+* K'.O :=
    e.symm.toRingHom.comp ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift)
  have hι : ∀ a, algebraMap K'.O K'.E (ι a) = φ (algebraMap K.O K.E a) := by
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply ((φ.comp (algebraMap K.O K.E)).codRestrict _ hlift a))
  letI : Algebra K.O K'.O := ι.toAlgebra
  have hsm : ∀ (a : K.O) (y : K'.O),
      algebraMap K'.O K'.E (a • y) = algebraMap K.O K.E a • algebraMap K'.O K'.E y := by
    intro a y
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    exact congrArg (· * _) (hι a)
  have hsum : ∀ (g : Fin d → K.O) (v : Fin d → K'.O),
      algebraMap K'.O K'.E (∑ k, g k • v k) = ∑ k, algebraMap K.O K.E (g k) • algebraMap K'.O K'.E (v k) := by
    intro g v
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsm _ _

  have hw1 : ∀ k, ∃ y : K'.O, algebraMap K'.O K'.E y = w k := by
    intro k
    apply (hw _).2
    intro m
    refine ⟨if m = k then 1 else 0, ?_⟩
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  choose bv hbv using hw1
  have hcoord : ∀ (y : K'.O) (k : Fin d), ∃ a : K.O, algebraMap K.O K.E a = w.repr (algebraMap K'.O K'.E y) k :=
    fun y => (hw _).1 ⟨y, rfl⟩
  choose c hc using hcoord
  have hli : LinearIndependent K.O bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h1 := congrArg (algebraMap K'.O K'.E) hg
    rw [hsum, map_zero] at h1
    simp only [hbv] at h1
    have h2 := (Fintype.linearIndependent_iff.1 w.linearIndependent) _ h1 k
    exact hi (by rw [h2, map_zero])
  have hsp : ⊤ ≤ Submodule.span K.O (Set.range bv) := by
    intro y _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c y, hj ?_⟩
    rw [hsum]
    simp only [hbv, hc]
    exact w.sum_repr _
  let b : Module.Basis (Fin d) K.O K'.O := Module.Basis.mk hli hsp
  have hb : ∀ k, algebraMap K'.O K'.E (b k) = w k := fun k => by
    rw [Module.Basis.mk_apply]; exact hbv k
  have hrep : ∀ y k, algebraMap K.O K.E (b.repr y k) = w.repr (algebraMap K'.O K'.E y) k := by
    intro y k
    conv_rhs => rw [← b.sum_repr y, hsum]
    simp only [hb]
    rw [w.repr_sum_self]

  have hTr : ∀ y, algebraMap K.O K.E (Algebra.trace K.O K'.O y) =
      Algebra.trace K.E K'.E (algebraMap K'.O K'.E y) := by
    intro y
    rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace w, Matrix.trace, Matrix.trace,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hrep, map_mul, hb]

  have hιπ : ι π = π' := hj (by rw [hι, hππ'])
  have hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hm, Ideal.map_span, Set.image_singleton]
    have h1 : algebraMap K.O K'.O π = π' := hιπ
    rw [h1, ← hm']
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨Algebra.discr K.O b, isUnit_discr_of_isMaximal_map b hmax, ?_⟩
  rw [Algebra.discr_def, RingHom.map_det]
  congr 1
  ext k m
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Matrix.of_apply, hTr, map_mul, hb]

end GlobalTheory.UnitLemma.Unr.ResDisc
end
end

