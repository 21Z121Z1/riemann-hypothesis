import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDimTie
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Algebra Cardinal

noncomputable section

universe u w

namespace DimTie

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

abbrev ratioRing (y : Fin (N + 1) → Ω) : Subalgebra k Ω :=
  Algebra.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}

theorem ratio_mem (y : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : y i ≠ 0) (j : Fin (N + 1)) :
    y j / y i ∈ ratioRing (k := k) y :=
  Algebra.subset_adjoin ⟨i, j, hi, rfl⟩

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem trdeg_funField (y : Fin (N + 1) → Ω) :
    trdeg k (funField (k := k) y) = trdeg k (ratioRing (k := k) y) := by
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  show trdeg k (IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}) = _
  rw [← trdeg_add_eq k (ratioRing (k := k) y)
    (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}),
    trdeg_eq_zero (R := ratioRing (k := k) y)
      (A := IntermediateField.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}), add_zero]

theorem trdeg_polynomial (D : Type w) [CommRing D] [IsDomain D] [Algebra k D] [FaithfulSMul k D] :
    trdeg k (Polynomial D) = trdeg k D + 1 := by
  have : FaithfulSMul D (Polynomial D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Polynomial.C_injective
  rw [← trdeg_add_eq k D (A := Polynomial D), Polynomial.trdeg_of_isDomain]

theorem aeval_C_mul_X_injective {c : Ω} (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (R := Ω) (Polynomial.C c * Polynomial.X)) := by
  have h : (Polynomial.aeval (R := Ω) (Polynomial.C c⁻¹ * Polynomial.X)).comp
      (Polynomial.aeval (Polynomial.C c * Polynomial.X)) = AlgHom.id Ω (Polynomial Ω) := by
    refine Polynomial.algHom_ext ?_
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  exact Function.LeftInverse.injective (g := Polynomial.aeval (Polynomial.C c⁻¹ * Polynomial.X))
    fun p => by rw [← AlgHom.comp_apply, h, AlgHom.id_apply]

section Cone

variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)

def ratio (j : Fin (N + 1)) : ratioRing (k := k) y := ⟨y j / y i₀, ratio_mem y hi₀ j⟩

def dehom : Poly k N →ₐ[k] Polynomial (ratioRing (k := k) y) :=
  aeval fun j => Polynomial.C (ratio y hi₀ j) * Polynomial.X

variable (i₀) in

def rehom : Polynomial (ratioRing (k := k) y) →ₐ[k] Polynomial Ω :=
  ((Polynomial.aeval (R := Ω) (Polynomial.C (y i₀) * Polynomial.X)).restrictScalars k).comp
    (Polynomial.mapAlgHom (ratioRing (k := k) y).val)

include hi₀ in
theorem rehom_injective : Function.Injective (rehom (k := k) y i₀) := by
  rw [rehom, AlgHom.coe_comp]
  exact (aeval_C_mul_X_injective hi₀).comp (Polynomial.map_injective _ Subtype.val_injective)

theorem rehom_comp_dehom : (rehom (k := k) y i₀).comp (dehom y hi₀) = cone (S := k) y := by
  refine MvPolynomial.algHom_ext fun j => ?_
  have hc : (cone (S := k) y) (X j) = Polynomial.C (y j) * Polynomial.X := by
    simp [cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  rw [hc]
  simp [rehom, dehom, ratio]
  rw [← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hi₀]

theorem primeOf_eq_ker : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀) := by
  ext f
  rw [primeOf_eq, RingHom.mem_ker, RingHom.mem_ker, ← rehom_comp_dehom (k := k) y hi₀, AlgHom.comp_apply,
    map_eq_zero_iff _ (rehom_injective (k := k) y hi₀)]

theorem isAlgebraic_range :
    Algebra.IsAlgebraic (dehom (k := k) y hi₀).range (Polynomial (ratioRing (k := k) y)) := by
  set R := (dehom (k := k) y hi₀).range
  have hmem : ∀ j, Polynomial.C (ratio (k := k) y hi₀ j) * Polynomial.X ∈ R :=
    fun j => ⟨X j, by simp [dehom]⟩
  have h1 : ratio (k := k) y hi₀ i₀ = 1 := Subtype.ext (div_self hi₀)
  have hX : IsAlgebraic R (Polynomial.X : Polynomial (ratioRing (k := k) y)) := by
    have h := hmem i₀
    rw [h1, Polynomial.C_1, one_mul] at h
    exact isAlgebraic_algebraMap (⟨_, h⟩ : R)
  have hb : ∀ j, IsAlgebraic R (Polynomial.C (ratio (k := k) y hi₀ j)) := fun j =>
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) hX
      (by rw [mul_comm]; exact isAlgebraic_algebraMap (⟨_, hmem j⟩ : R))
  have hgen : ∀ i j (hi : y i ≠ 0),
      IsAlgebraic R (Polynomial.C (⟨y j / y i, ratio_mem y hi j⟩ : ratioRing (k := k) y)) := by
    intro i j hi
    have hne : ratio (k := k) y hi₀ i ≠ 0 := fun h =>
      div_ne_zero hi hi₀ (congrArg Subtype.val h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr hne))
      (hb i) ?_
    have he : ratio (k := k) y hi₀ i * ⟨y j / y i, ratio_mem y hi j⟩ = ratio (k := k) y hi₀ j := by
      apply Subtype.ext
      change y i / y i₀ * (y j / y i) = y j / y i₀
      field_simp
    rw [← Polynomial.C_mul, he]
    exact hb j
  have hCD : ∀ d : ratioRing (k := k) y, IsAlgebraic R (Polynomial.C d) := by
    let M : Subalgebra k (ratioRing (k := k) y) :=
      ((Subalgebra.algebraicClosure R (Polynomial (ratioRing (k := k) y))).restrictScalars k).comap
        (Polynomial.CAlgHom (R := k) (A := ratioRing (k := k) y))
    have hM : ratioRing (k := k) y ≤ M.map (ratioRing (k := k) y).val := Algebra.adjoin_le (by
      rintro _ ⟨i, j, hi, rfl⟩
      exact ⟨⟨y j / y i, ratio_mem y hi j⟩, hgen i j hi, rfl⟩)
    intro d
    obtain ⟨d', hd', he⟩ := hM d.2
    rw [show d = d' from Subtype.ext he.symm]
    exact hd'
  refine ⟨fun p => ?_⟩
  induction p using Polynomial.induction_on with
  | C a => exact hCD a
  | add p q hp hq => exact hp.add hq
  | monomial n a h => rw [pow_succ, ← mul_assoc]; exact h.mul hX

theorem trdeg_range :
    trdeg k (dehom (k := k) y hi₀).range = trdeg k (ratioRing (k := k) y) + 1 := by
  have := isAlgebraic_range (k := k) y hi₀
  have : FaithfulSMul k (dehom (k := k) y hi₀).range :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  have := (faithfulSMul_iff_algebraMap_injective (dehom (k := k) y hi₀).range
    (Polynomial (ratioRing (k := k) y))).2 Subtype.val_injective
  have : FaithfulSMul k (ratioRing (k := k) y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  rw [← trdeg_polynomial (k := k) (ratioRing (k := k) y), ← trdeg_add_eq k (dehom (k := k) y hi₀).range
    (A := Polynomial (ratioRing (k := k) y)),
    trdeg_eq_zero (R := (dehom (k := k) y hi₀).range) (A := Polynomial (ratioRing (k := k) y)),
    add_zero]

end Cone

theorem ringKrullDim_eq (y : Fin (N + 1) → Ω) (hy : y ≠ 0) :
    ringKrullDim (Poly k N ⧸ primeOf (S := k) y) =
      (((trdeg k (funField (k := k) y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have : Algebra.FiniteType k (Poly k N ⧸ primeOf (S := k) y) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k]
  have hk : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀).rangeRestrict := by
    rw [primeOf_eq_ker (k := k) y hi₀]
    ext f
    simp only [RingHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e : (Poly k N ⧸ primeOf (S := k) y) ≃ₐ[k] (dehom (k := k) y hi₀).range :=
    (Ideal.quotientEquivAlgOfEq k hk).trans
      (Ideal.quotientKerAlgEquivOfSurjective (dehom (k := k) y hi₀).rangeRestrict_surjective)
  have h := AlgEquiv.lift_trdeg_eq (R := k) (A := Poly k N ⧸ primeOf (S := k) y)
    (A' := (dehom (k := k) y hi₀).range) e
  rw [trdeg_range (k := k) y hi₀, ← trdeg_funField] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [toENat_lift, map_add, map_one] at h2
  rw [h2]

end DimTie

theorem DimTie.proof : DimTie.Statement := by
  intro k _ Ω _ _ N y hy e
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have hdim := DimTie.ringKrullDim_eq (k := k) y hy
  constructor
  · intro h
    have h' := h.dim
    rw [hdim] at h'
    have h3 : (trdeg k (funField (k := k) y)).toENat + 1 = (e : ℕ∞) + 1 := by exact_mod_cast h'
    exact Cardinal.toENat_eq_natCast.mp ((ENat.add_left_injective_of_ne_top ENat.one_ne_top) h3)
  · intro h
    have h' : trdeg k (funField (k := k) y) = e := h
    refine ⟨inferInstance, fun p hp d => homogeneousComponent_mem_primeOf y hp d, le_rfl, ⟨i₀, ?_⟩, ?_⟩
    · rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i₀), aeval_X]
      exact hi₀
    · rw [hdim, Cardinal.toENat_eq_natCast.mpr h']
      push_cast
      rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

theorem normSq_pow_mul_rpow_neg (a b : ℂ) (ha : a ≠ 0) (n : ℕ) :
    ‖a ^ n * b‖ ^ 2 * (‖a‖ ^ 2) ^ (-(n : ℝ)) = ‖b‖ ^ 2 := by
  have hpos : 0 < ‖a‖ ^ 2 := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, norm_mul, norm_pow]
  have : (‖a‖ ^ 2) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem mem_S_of_s_eq_zero {X : EmbDatum 1} (Z : ZeroDatum X) {j : Fin X.A.n} {x : X.U}
    (hx : x ∈ (X.A.chart j).source) (h0 : Z.s 0 j x = 0) : x ∈ Z.S := by
  show ∀ i, Z.s i (chartIdx X.A x) x = 0
  intro i
  rw [Subsingleton.elim i 0]
  have hc : x ∈ (X.A.chart (chartIdx X.A x)).source := Classical.choose_spec (X.A.cover x)
  have hmem : Z.s 0 ∈ X.L.sections 1 := by
    show lin X.e (Z.c 0) ∈ X.L.sections 1
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
  have key := hmem.2.1 j (chartIdx X.A x) x ⟨hx, hc⟩
  rw [h0, pow_one] at key
  exact (mul_eq_zero.mp key.symm).resolve_left (X.L.ne_zero _ _ x ⟨hx, hc⟩)

theorem DivisionDimOne.proof (hNear : DivisionNearS.Statement)
    (hQuot : DivisionDimOneQuot.Statement) : DivisionDimOne.Statement := by
  intro T X Z φA hT F hF hfil
  obtain ⟨h, hh, rfl⟩ := hQuot T X Z hT _ hF.1 hfil
  refine ⟨h, ⟨hh, ?_⟩, rfl⟩
  have hN := hNear 1 T X Z φA le_rfl hT _ hF hfil ((T : ℝ) - 2) (by linarith)
  refine lt_of_le_of_lt ?_ hN
  have he1 : (T : ℝ) - 1 - ((T : ℝ) - 2) = 1 := by ring
  have he2 : -((T : ℝ) - 2 + 1) = -((T - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hT]; ring
  unfold topNormSq skodaNormSq chartIntegral
  refine Finset.sum_le_sum fun j _ => ?_
  refine lintegral_mono_ae ?_
  have hsub : volume.restrict (piece X.A j) ≪ volume.restrict (X.A.chart j).target :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono (fun y hy => hy.1) le_rfl)
  refine hsub.ae_le ?_
  refine (ae_restrict_iff' (X.A.chart j).open_target.measurableSet).mpr ?_
  have hfin : ((X.A.chart j) '' Z.S).Finite := Z.finite.image _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with y hy hyt
  have hxs : (X.A.chart j).symm y ∈ (X.A.chart j).source := (X.A.chart j).map_target hyt
  have hs0 : Z.s 0 j ((X.A.chart j).symm y) ≠ 0 := fun h0 =>
    hy ⟨_, mem_S_of_s_eq_zero Z hxs h0, (X.A.chart j).right_inv hyt⟩
  apply le_of_eq
  congr 1
  simp only [Fin.sum_univ_one, Pi.mul_apply, Pi.pow_apply, he1, he2, Nat.cast_one, one_mul]
  rw [← normSq_pow_mul_rpow_neg _ (h j ((X.A.chart j).symm y)) hs0 (T - 1)]
  ring

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem JacobianRankGeneric.kaehler_D_aeval {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum, smul_smul, map_add, add_smul,
      Finset.sum_add_distrib, pderiv_X, smul_eq_mul, Pi.single_apply]
    rw [add_left_inj]
    simp [apply_ite, ite_smul]

theorem JacobianRankGeneric.finrank_kaehler_eq_card {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  have hx : AlgebraicIndependent k (fun i : s => (i : K)) := hs.1
  let _ : Algebra (MvPolynomial s k) K := (aeval (fun i : s => (i : K))).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  let _ : Algebra (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    ((hx.aevalEquivField).toRingHom.comp (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)))).toAlgebra
  let e : FractionRing (MvPolynomial s k) ≃ₐ[MvPolynomial s k]
      IntermediateField.adjoin k (Set.range fun i : s => (i : K)) :=
    { hx.aevalEquivField with commutes' := fun q => rfl }
  have : Algebra.FormallyEtale (MvPolynomial s k) (FractionRing (MvPolynomial s k)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    .of_equiv e
  have : IsScalarTower (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change aeval (fun i : s => (i : K)) q =
        ((hx.aevalEquivField (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) q) : _) : K)
      rw [hx.aevalEquivField_algebraMap_apply_coe]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K := by
    convert! H <;> simp
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K
  have : Module.Free (MvPolynomial s k) Ω[MvPolynomial s k⁄k] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k s)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k s),
    Fintype.card_coe]

theorem JacobianRankGeneric.proof : JacobianRankGeneric.Statement := by
  classical
  intro n d J _ hd
  set A := MvPolynomial (Fin n) ℂ ⧸ J
  set K := FractionRing A

  let ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ A K).comp (Ideal.Quotient.mkₐ ℂ J)
  let x : Fin n → K := fun l => ψ (X l)
  have hψ : ∀ f, ψ f = aeval x f := fun f => congrArg (fun φ => φ f) (MvPolynomial.aeval_unique ψ)
  have hgrad : ∀ f l, genericGradient J f l = aeval x (pderiv l f) := fun f l => hψ (pderiv l f)
  let Φ : (Fin n → K) →ₗ[K] Ω[K⁄ℂ] :=
    ∑ l, (LinearMap.proj l : (Fin n → K) →ₗ[K] K).smulRight (KaehlerDifferential.D ℂ K (x l))
  have hΦ : ∀ w, Φ w = ∑ l, w l • KaehlerDifferential.D ℂ K (x l) := fun w => by
    simp [Φ, LinearMap.sum_apply]

  have hker : Submodule.span K (genericGradient J '' (J : Set _)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h0 : aeval x f = 0 := by
      rw [← hψ]
      simp only [ψ, AlgHom.comp_apply]
      rw [show Ideal.Quotient.mkₐ ℂ J f = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hΦ, hgrad]
    rw [← JacobianRankGeneric.kaehler_D_aeval, h0, map_zero]

  have hsurj : LinearMap.range Φ = ⊤ := by
    have hA : ∀ f, KaehlerDifferential.D ℂ K (ψ f) ∈ LinearMap.range Φ := fun f =>
      ⟨fun l => aeval x (pderiv l f), by rw [hΦ, hψ, JacobianRankGeneric.kaehler_D_aeval]⟩
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hf := hA f
    have hg := hA g
    change KaehlerDifferential.D ℂ K (ψ f / ψ g) ∈ _
    rw [Derivation.leibniz_div]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg))

  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℂ K
  have hcard : s.card = d := by
    have h1 := hs.cardinalMk_eq_trdeg
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing ℂ (A := A) K
    rw [hd, ← h1, Cardinal.mk_coe_finset] at h2
    simp at h2
    exact_mod_cast h2.symm
  have hrank : Module.finrank K Ω[K⁄ℂ] = d := by
    rw [JacobianRankGeneric.finrank_kaehler_eq_card s hs H, hcard]

  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, hrank, Module.finrank_fin_fun] at h2
  change Module.finrank K (Submodule.span K (genericGradient J '' (J : Set _))) ≤ n - d
  calc _ ≤ _ := h1
    _ = n - d := by
      generalize Module.finrank K (LinearMap.ker Φ) = m at h2 ⊢
      omega

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubsetDiffConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Finset

noncomputable section

theorem sum_subsets_neg_one_pow_prod_indicator (n : ℕ) (a : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, (if i ∈ T then (1 : ℚ) else 0) ^ a i =
      ∏ i, (1 - (0 : ℚ) ^ a i) := by
  have h := Finset.prod_add (fun _ : Fin n => (1 : ℚ)) (fun i => -((0 : ℚ) ^ a i)) univ
  simp only [← sub_eq_add_neg, powerset_univ, prod_const_one, one_mul] at h
  rw [h]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_neg, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin]
  congr 1
  rw [← prod_mul_prod_compl T]
  rw [prod_congr rfl (fun i hi => by rw [if_pos hi, one_pow]), prod_const_one, one_mul]
  exact prod_congr rfl fun i hi => by rw [if_neg (mem_compl.mp hi)]

theorem prod_snoc_snoc_pow (n : ℕ) (T : Finset (Fin n)) (m : ℕ) (c : ℤ) (e : Fin (n + 1 + 1) → ℕ) :
    ∏ j, (Fin.snoc (α := fun _ => ℚ)
        (fun j => ((Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m j : ℕ) : ℚ))
        (c : ℚ) j) ^ e j =
      (∏ i : Fin n, (if i ∈ T then (1 : ℚ) else 0) ^ e i.castSucc.castSucc) *
        (m : ℚ) ^ e (Fin.last n).castSucc * (c : ℚ) ^ e (Fin.last (n + 1)) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem subsetDiff_eq_sum_support (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ)
    (Q : MvPolynomial (Fin (n + 1 + 1)) ℚ)
    (hf : ∀ (x : Fin (n + 1) → ℕ) (c : ℤ),
      f x c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (x j : ℚ)) (c : ℚ)) Q)
    (m : ℕ) (c : ℤ) :
    subsetDiff n f m c = ∑ e ∈ Q.support, Q.coeff e *
      ((∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) * (m : ℚ) ^ e (Fin.last n).castSucc *
        (c : ℚ) ^ e (Fin.last (n + 1))) := by
  unfold subsetDiff
  simp only [hf, eval_eq', prod_snoc_snoc_pow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  have h := sum_subsets_neg_one_pow_prod_indicator n (fun i => e i.castSucc.castSucc)
  rw [← h, sum_mul, sum_mul, mul_sum]
  exact sum_congr rfl fun T _ => by ring

theorem sum_exponents_lt_of_mem_support {σ : Type*} [Fintype σ] {Q : MvPolynomial σ ℚ} {D : ℕ}
    (h : Q = 0 ∨ Q.totalDegree < D) {e : σ →₀ ℕ} (he : e ∈ Q.support) : ∑ j, e j < D := by
  rcases h with h | h
  · simp [h] at he
  · have := le_totalDegree he
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact lt_of_le_of_lt this h

theorem le_sum_of_prod_ne_zero (n : ℕ) (a : Fin n → ℕ) (h : (∏ i, (1 - (0 : ℚ) ^ a i)) ≠ 0) :
    n ≤ ∑ i, a i := by
  have hpos : ∀ i, 1 ≤ a i := fun i => by
    by_contra h0
    have h1 : a i = 0 := by omega
    exact h (prod_eq_zero (mem_univ i) (by rw [h1, pow_zero, sub_self]))
  calc n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i, a i := sum_le_sum fun i _ => hpos i

theorem SubsetDiffConst.proof : SubsetDiffConst.Statement := by
  intro n f ⟨Q, hQ, hf⟩
  have split : ∀ e : Fin (n + 1 + 1) →₀ ℕ, ∑ j, e j =
      ∑ i : Fin n, e i.castSucc.castSucc + e (Fin.last n).castSucc + e (Fin.last (n + 1)) := fun e => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  refine ⟨fun m m' c c' => ?_, fun ⟨Q', hQ', hf'⟩ m c => ?_⟩
  · rw [subsetDiff_eq_sum_support n f Q hf, subsetDiff_eq_sum_support n f Q hf]
    refine sum_congr rfl fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ he
      rw [split] at h2
      have ha : e (Fin.last n).castSucc = 0 := by omega
      have hb : e (Fin.last (n + 1)) = 0 := by omega
      simp [ha, hb]
  · rw [subsetDiff_eq_sum_support n f Q' hf']
    refine sum_eq_zero fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ' he
      rw [split] at h2
      omega

end

end GroundTheory.Heights₂.Heights.Kleiman
end

