import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityOfPrincipalCongruence
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem inv_small {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by
  obtain ⟨Q, hQm, hQ⟩ := hg
  rw [← aeval_def] at hQ
  set D := algebraMap O A α + algebraMap O A β * g with hD
  set n := Q.natDegree
  let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (X - C α) ^ i * C β ^ (n - i)
  have hR : aeval D R = 0 := by
    have : aeval D R = algebraMap O A β ^ n * aeval g Q := by
      conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
      simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Algebra.smul_def, hD]
      have : algebraMap O A β ^ n = algebraMap O A β ^ i * algebraMap O A β ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hin]
      rw [this]; ring
    rw [this, hQ, mul_zero]
  have hR0 : IsUnit (R.eval 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hb : IsLocalRing.residue O β = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hβ
    have ha : IsLocalRing.residue O α ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hα
    simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_sum, map_mul, map_pow,
      map_sub, map_zero, hb]
    rw [Finset.sum_eq_single n]
    · simp [n, hQm.coeff_natDegree, ha]
    · intro i hi hin
      have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  obtain ⟨w, hw, hDw⟩ := sub_inv_mem D 0 R hR hR0
  rw [map_zero, sub_zero] at hDw
  refine ⟨w, ?_, hDw⟩
  have hDmem : D ∈ Algebra.adjoin O ({g} : Set A) :=
    add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hDmem) hw

theorem adjoin_both {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g Y : A) (α β γ : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) (hγ : IsUnit γ)
    (hY : Y * (algebraMap O A α + algebraMap O A β * g) = algebraMap O A γ * g) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  obtain ⟨w, hw, hDw⟩ := inv_small g α β hg hα hβ
  have h1 : Y ∈ Algebra.adjoin O ({g} : Set A) := by
    have e : Y = algebraMap O A γ * g * w := by linear_combination (-Y) * hDw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hw
  refine ⟨h1, ?_⟩
  have hYi : IsIntegral O Y := IsIntegral.of_mem_of_fg _ hg.fg_adjoin_singleton Y h1
  have hβ' : -β ∈ IsLocalRing.maximalIdeal O := neg_mem hβ
  obtain ⟨v, hv, hEv⟩ := inv_small Y γ (-β) hYi hγ hβ'
  have e : g = algebraMap O A α * Y * v := by
    rw [map_neg] at hEv
    linear_combination (-g) * hEv - v * hY
  rw [e]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hv

variable {K : UQ}

theorem congruence_selfadj (B : InvAlg K) (a x y : K.O) (ha0 : a ≠ 0)
    (hac : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hu : (1 + algebraMap K.O B.A a * B.g) * B.σ (1 + algebraMap K.O B.A a * B.g) = 1)
    (Y w : B.A)
    (hw : (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) * w = 1)
    (hY : Y * (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) =
      algebraMap K.O B.A (x * y) * B.g) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have sa : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [σ_algebraMap, hac, ← IsScalarTower.algebraMap_apply]
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_sub, map_add, sx, sy, sa] at h1 hY hw
  rw [map_add, map_one, map_mul, sa] at hu
  set G := B.g
  set S := B.σ B.g
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  set aA := algebraMap K.O B.A a
  have key : (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA = 0 := by
    linear_combination (-aA * (1 + aA * G)) * h1 - (xA * yA - aA * B.σ Y * yA) * hu - aA * hY
  have key2 : (B.σ Y - Y) * aA = 0 := by
    calc (B.σ Y - Y) * aA = (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA * w := by
          linear_combination (-(B.σ Y - Y) * aA) * hw
      _ = 0 := by rw [key, zero_mul]
  have hae : algebraMap K.O K.E a ≠ 0 := by
    intro h; exact ha0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  have : (algebraMap K.O K.E a) • (B.σ Y - Y) = 0 := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]; exact key2
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left hae)

end GlobalTheory.UnitLemma.CongruenceCayley

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a →
    ∀ B₁ B₂ : InvAlg K,
    (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 →
    (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K a ha B₁ B₂ hu₁ hu₂ hsep
  by_cases hint : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  swap
  · obtain ⟨h1, h2⟩ := kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hint
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]
  obtain ⟨i₁, i₂⟩ := hint
  obtain ⟨ha0, ham, hac⟩ := ha
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (CayleyAny.isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := CayleyAny.isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hβ : x * a ∈ IsLocalRing.maximalIdeal K.O := Ideal.mul_mem_left _ _ ham
  have hγ : IsUnit (x * y) := hxu.mul hyu
  obtain ⟨w₁, -, hw₁⟩ := inv_small B₁.g (x - y) (x * a) i₁ hxyu hβ
  obtain ⟨w₂, -, hw₂⟩ := inv_small B₂.g (x - y) (x * a) i₂ hxyu hβ
  set Y₁ := algebraMap K.O B₁.A (x * y) * B₁.g * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A (x * y) * B₂.g * w₂ with hY₂d
  have hY₁ : Y₁ * (algebraMap K.O B₁.A (x - y) + algebraMap K.O B₁.A (x * a) * B₁.g) =
      algebraMap K.O B₁.A (x * y) * B₁.g := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A (x * y) * B₁.g) * hw₁
  have hY₂ : Y₂ * (algebraMap K.O B₂.A (x - y) + algebraMap K.O B₂.A (x * a) * B₂.g) =
      algebraMap K.O B₂.A (x * y) * B₂.g := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A (x * y) * B₂.g) * hw₂
  have adj₁ := adjoin_both B₁.g Y₁ (x - y) (x * a) (x * y) i₁ hxyu hβ hγ hY₁
  have adj₂ := adjoin_both B₂.g Y₂ (x - y) (x * a) (x * y) i₂ hxyu hβ hγ hY₂
  have iP : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := IsIntegral.pair i₁ i₂
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * (algebraMap K.O (B₁.A × B₂.A) (x - y) +
      algebraMap K.O (B₁.A × B₂.A) (x * a) * (B₁.g, B₂.g)) =
      algebraMap K.O (B₁.A × B₂.A) (x * y) * (B₁.g, B₂.g) :=
    Prod.ext hY₁ hY₂
  have adjP := adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (x - y) (x * a) (x * y) iP hxyu hβ hγ hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := congruence_selfadj B₁ a x y ha0 hac hxy hu₁ Y₁ w₁ hw₁ hY₁
  have sa₂ := congruence_selfadj B₂ a x y ha0 hac hxy hu₂ Y₂ w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g i₁
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g i₂
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CongruenceCayley
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsFiniteCosets
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongNIndex

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embO : 𝓞 E →+* RInt F E :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeLeft : E →ₐ[F] AfE F E).toRingHom.comp (algebraMap (𝓞 E) E))
    (RInt F E) fun o => Subring.subset_closure (Set.mem_union_left _ ⟨⟨_, RingHom.mem_range.2 ⟨o, rfl⟩⟩, rfl⟩)

def redO (N : ℕ) : 𝓞 E →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
  (Ideal.Quotient.mk _).comp (embO F E)

theorem one_tmul_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ intAd F) :
    (1 : E) ⊗ₜ[F] a ∈ RInt F E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨a, ha⟩, rfl⟩)

theorem mk_mem_range (N : ℕ) (hN : 0 < N) (z : RInt F E) :
    Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) z ∈ (redO F E N).range := by
  let T : Subring (RInt F E) := (redO F E N).range.comap (Ideal.Quotient.mk _)
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have key : RInt F E ≤ T.map (RInt F E).subtype := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact ⟨embO F E o, ⟨o, rfl⟩, rfl⟩
    · obtain ⟨x, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 y hy
      refine ⟨embO F E (algebraMap (𝓞 F) (𝓞 E) x) + (N : RInt F E) * ⟨_, one_tmul_mem F E (a := a) ha⟩,
        ⟨algebraMap (𝓞 F) (𝓞 E) x, ?_⟩, ?_⟩
      · show redO F E N _ = Ideal.Quotient.mk _ _
        rw [map_add, map_mul, hN0, zero_mul, add_zero]
        rfl
      · show ((algebraMap F E (x : F)) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) + (N : AfE F E) * ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] y
        rw [e, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F),
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, nsmul_eq_mul]
  obtain ⟨w, hw, e⟩ := key z.2
  have : w = z := Subtype.ext e
  subst this
  exact hw

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := by
    apply Ideal.finiteQuotientOfFreeOfNeBot
    simp [Ideal.span_singleton_eq_bot]; omega
  have hN0 : Ideal.Quotient.mk (Ideal.span {(N : RInt F E)}) (N : RInt F E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let φ : 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)} →+* RInt F E ⧸ Ideal.span {(N : RInt F E)} :=
    Ideal.Quotient.lift _ (redO F E N) fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : RInt F E)})), hN0, mul_zero]
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨o, ho⟩ := mk_mem_range F E N hN z
  exact ⟨Ideal.Quotient.mk _ o, ho⟩

def toU : intU F E ≃* (RInt F E)ˣ := Submonoid.unitsEquivUnitsType (RInt F E).toSubmonoid

theorem exists_finset (N : ℕ) (hN : 0 < N) :
    ∃ S : Finset (AfE F E)ˣ, ∀ k ∈ intU F E, ∃ s ∈ S, s⁻¹ * k ∈ congN F E N := by
  classical
  haveI := finite_quot F E N hN
  let I := Ideal.span {(N : RInt F E)}
  let f : (AfE F E)ˣ → (RInt F E ⧸ I)ˣ := fun k =>
    if h : k ∈ intU F E then Units.map (Ideal.Quotient.mk I).toMonoidHom (toU F E ⟨k, h⟩) else 1
  let g : (RInt F E ⧸ I)ˣ → (AfE F E)ˣ := fun q =>
    if h : ∃ k ∈ intU F E, f k = q then h.choose else 1
  refine ⟨(Set.finite_range g).toFinset, fun k hk => ?_⟩
  have hex : ∃ k' ∈ intU F E, f k' = f k := ⟨k, hk, rfl⟩
  have hg : g (f k) = hex.choose := dif_pos hex
  obtain ⟨hs, hfs⟩ := hex.choose_spec
  refine ⟨g (f k), (Set.finite_range g).mem_toFinset.2 ⟨_, rfl⟩, ?_⟩
  rw [hg]
  set s := hex.choose
  refine ⟨(toU F E ⟨s, hs⟩)⁻¹ * toU F E ⟨k, hk⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have h1 : f s = _ := dif_pos hs
    have h2 : f k = _ := dif_pos hk
    rw [← h1, ← h2, hfs]
  · ext
    simp only [map_mul, map_inv, Units.val_mul]
    rfl

end GlobalTheory.CongNIndex

theorem GlobalTheory.congN_finite_index : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N :=
  fun L _ _ N hN => GlobalTheory.CongNIndex.exists_finset ℚ L N hN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.CharBound

noncomputable section

variable {C : Type} [Field C]

theorem isIntV_add' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)

theorem isIntV_mul' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x * y) := by
  unfold IsIntV at *
  rw [v.map_mul]
  exact add_nonneg hx hy

theorem isIntV_zero' {v : AddValuation C (WithTop ℝ)} : IsIntV v 0 := by
  unfold IsIntV; rw [v.map_zero]; exact le_top

theorem isIntV_one' {v : AddValuation C (WithTop ℝ)} : IsIntV v 1 := by
  unfold IsIntV; rw [v.map_one]

theorem mvIsInt_mul' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F G : MvPowerSeries σ C}
    (hF : MvIsInt v F) (hG : MvIsInt v G) : MvIsInt v (F * G) := by
  classical
  intro α
  rw [coeff_mul]
  exact Finset.sum_induction _ (IsIntV v) (fun _ _ => isIntV_add') isIntV_zero'
    fun p _ => isIntV_mul' (hF _) (hG _)

theorem mvIsInt_one' {v : AddValuation C (WithTop ℝ)} {σ : Type} : MvIsInt v (1 : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_one]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_X' {v : AddValuation C (WithTop ℝ)} {σ : Type} (s : σ) :
    MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_X]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_pow' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F : MvPowerSeries σ C}
    (hF : MvIsInt v F) (n : ℕ) : MvIsInt v (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact mvIsInt_one'
  | succ n ih => rw [pow_succ]; exact mvIsInt_mul' ih hF

theorem mvIsInt_subst' {v : AddValuation C (WithTop ℝ)} {σ τ : Type} {a : σ → MvPowerSeries τ C}
    (ha : HasSubst a) (hai : ∀ s, MvIsInt v (a s)) {F : MvPowerSeries σ C} (hF : MvIsInt v F) :
    MvIsInt v (subst a F) := by
  intro β
  rw [coeff_subst ha]
  refine finsum_induction (IsIntV v) isIntV_zero' (fun _ _ => isIntV_add') fun e => ?_
  rw [smul_eq_mul]
  refine isIntV_mul' (hF e) ?_
  exact Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    (fun s _ => mvIsInt_pow' (hai s) _) β

theorem isInt_prod_rename (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (χ : Fin i → MvPowerSeries (Fin d) C) (h : ∀ b, MvIsInt v (χ b)) :
    MvIsInt v (∏ b, subst (fun e : Fin d =>
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) :=
  Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    fun b _ => mvIsInt_subst' (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => mvIsInt_X' _) (h b)

variable [CharZero C]

theorem coeff_mvExp_lin {σ : Type} [Fintype σ] (c : σ → C) (α : σ →₀ ℕ) :
    coeff α (Formalism.L2.Th1.C.mvExp (∑ s, c s • (X s : MvPowerSeries σ C))) =
      α.prod fun s n => c s ^ n / (n.factorial : C) := by
  classical
  set L : MvPowerSeries σ C := ∑ s, c s • (X s : MvPowerSeries σ C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  let g : MvPowerSeries σ C := fun β => β.prod fun s n => c s ^ n / (n.factorial : C)
  have hg : ∀ β, coeff β g = ∏ s, c s ^ β s / ((β s).factorial : C) := fun β => by
    show (β.prod fun s n => c s ^ n / (n.factorial : C)) = _
    exact Finsupp.prod_fintype _ _ (fun s => by simp)
  have hpL : ∀ i, pderiv C i L = c i • (1 : MvPowerSeries σ C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have hpg : ∀ i, pderiv C i g = c i • g := fun i => by
    ext β
    rw [coeff_pderiv, hg, coeff_smul, hg, Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i (fun s => c s ^ β s / ((β s).factorial : C))]
    have hrest : ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ (β + Finsupp.single i 1 : σ →₀ ℕ) s /
        (((β + Finsupp.single i 1 : σ →₀ ℕ) s).factorial : C) =
        ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ β s / ((β s).factorial : C) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s ≠ i := by simpa using hs
      simp [Finsupp.single_apply, Ne.symm hs']
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorial_succ]
    have h0 : ((β i).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h1 : ((β i : C) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    push_cast
    field_simp
    ring
  have hcg : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hg]
    simp
  have key : g * Formalism.L2.Th1.C.mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, Formalism.L2.Th1.C.pderiv_mvExp hnL, map_neg, hpL, hpg, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, hcg, Formalism.L2.Th1.C.constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : Formalism.L2.Th1.C.mvExp L = g := by
    calc Formalism.L2.Th1.C.mvExp L = (g * Formalism.L2.Th1.C.mvExp (-L)) * Formalism.L2.Th1.C.mvExp L := by
          rw [key, one_mul]
      _ = g := by rw [mul_assoc, Formalism.L2.Th1.C.mvExp_neg hL, mul_one]
  rw [hE]
  rfl

theorem derivAt0_eq_eval {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) (w : σ → C)
    (hg : ∀ α, coeff α g = α.prod fun s n => w s ^ n / (n.factorial : C)) :
    derivAt0 P g = MvPolynomial.eval w P := by
  rw [MvPolynomial.eval_eq, derivAt0]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hg, mfact, mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have : (((α s).factorial : ℕ) : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem eval_detPow (i c : ℕ) (H : Matrix (Fin i) (Fin i) C) :
    MvPolynomial.eval (fun x : (Σ _ : Fin i, Fin i) => H x.2 x.1) (detPow C i c) = H.det ^ c := by
  rw [detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

open Formalism.L2.Th1.C in

theorem subst_col (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C)
    (b : Fin i) (w : Fin d → C) (χ : MvPowerSeries (Fin d) C)
    (hχ : ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => w e ^ n / (n.factorial : C)) :
    subst (expAlong (fun _ : Fin i => G) (fun _ => u))
        (subst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) χ) =
      mvExp (∑ e, w e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
  have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hexp.1
  have hL : ∀ b' : Fin i, HasSubst (fun e : Fin d => ∑ a, u a e • (X (⟨b', a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
    fun b' => hasSubst_of_constantCoeff_zero fun e => by simp
  have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero (hL x.1) (fun e => by simp) (hexp.1 x.2)
  have hR : HasSubst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun e => by simp
  have h1 : subst (expOf G) χ = mvExp (∑ e, w e • (X e : MvPowerSeries (Fin d) C)) := by
    ext α; rw [hχ, coeff_mvExp_lin]
  rw [subst_comp_subst_apply hR hEA]
  have h2 : (fun e : Fin d => subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) =
      fun e => subst (fun e : Fin d => ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (expOf G e) := by
    funext e; rw [subst_X hEA]; rfl
  rw [h2, ← subst_comp_subst_apply hE (hL b), h1, mvSubst_mvExp (by simp) (hL b)]
  congr 1
  rw [← coe_substAlgHom (hL b), map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, coe_substAlgHom, subst_X (hL b)]

theorem lin_sum {i d : ℕ} (l : Fin i → Fin d → C) (u : Fin i → Fin d → C) :
    (∑ b, ∑ e, l b e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
      ∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_smul]

theorem detDepth_le_char : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (l : Fin i → Fin d → C), (∀ b, IsCharLog G (l b)) →
    detDepth G u c ≤ toE (v ((Matrix.det (Matrix.of fun a b => ∑ e, l b e * u a e)) ^ c)) := by
  intro C _ _ v i d c G u l hl
  choose χ hχi hχc using hl
  have hf := isInt_prod_rename v i d χ hχi
  have key : subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (∏ b, subst (fun e : Fin d =>
        (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) =
      Formalism.L2.Th1.C.mvExp (∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
    have hexp := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G).1
    have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
      hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun e => by simp) (fun e => by simp) (hexp.1 x.2)
    rw [← coe_substAlgHom hEA, map_prod, ← lin_sum, Formalism.L2.Th1.C.mvExp_sum _ _ (fun b _ => by simp)]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_substAlgHom, subst_col v G u b (l b) (χ b) (hχc b)]
  unfold detDepth depth
  refine le_trans (iInf_le _ ⟨_, hf⟩) (le_of_eq ?_)
  dsimp only
  rw [key, derivAt0_eq_eval _ _ (fun x : (Σ _ : Fin i, Fin i) => (Matrix.of fun a b => ∑ e, l b e * u a e) x.2 x.1)
    (fun α => by rw [coeff_mvExp_lin]; rfl), eval_detPow]

end

end GlobalTheory.FGDepth.CharBound
end

