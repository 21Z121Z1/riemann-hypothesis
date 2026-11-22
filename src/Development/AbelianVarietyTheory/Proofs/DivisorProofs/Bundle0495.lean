import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
section
open scoped IntermediateField Polynomial RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace RiemannCofinal

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_ne_zero (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 :=
  (Valuation.ne_zero_iff _).2 hx

theorem ord_mul (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (val_ne_zero v hx) (val_ne_zero v hy)]
  ring

theorem ord_inv (v : Place k F) (x : F) : ord v x⁻¹ = -ord v x := by
  unfold ord
  rw [map_inv₀, WithZero.log_inv]

theorem ord_pow (v : Place k F) (x : F) (n : ℕ) : ord v (x ^ n) = n * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow]
  simp

theorem ord_one (v : Place k F) : ord v 1 = 0 := by simp [ord]

theorem ord_le_ord (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : v.1 x ≤ v.1 y) :
    ord v y ≤ ord v x := by
  unfold ord
  have := (WithZero.log_le_log (val_ne_zero v hx) (val_ne_zero v hy)).2 h
  omega

theorem le_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem lt_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x < 1 ↔ 0 < ord v x := by
  unfold ord
  rw [← WithZero.log_lt_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem ord_prod {ι : Type} (v : Place k F) (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, x i ≠ 0) :
    ord v (∏ i ∈ s, x i) = ∑ i ∈ s, ord v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hx a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem val_algebraMap_le (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [v.2.2 c hc]

end RiemannCofinal

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open RiemannCofinal

theorem riemann_cofinal : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  intro k F _ _ _ _ _ hFF
  classical
  obtain ⟨t, ht, -⟩ := id hFF
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hti : Transcendental k t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.1 h)
  have hadj : k⟮t⁻¹⟯ = k⟮t⟯ := le_antisymm
    (IntermediateField.adjoin_simple_le_iff.2 (inv_mem (IntermediateField.mem_adjoin_simple_self k t)))
    (IntermediateField.adjoin_simple_le_iff.2
      (by simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental k F hFF t ht
  obtain ⟨hPfin, hPdeg⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hFF t⁻¹ hti
  rw [hadj] at hPdeg
  refine ⟨c * Module.finrank k⟮t⟯ F, fun D => ?_⟩

  have hpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 ↔ w.1 t⁻¹ < 1 := by
    intro w
    rw [lt_one_iff w (inv_ne_zero ht0), ord_inv, le_one_iff w ht0]
    constructor <;> intro <;> omega

  have hres : ∀ v : Place k F, v.1 t ≤ 1 → ∃ a : k, v.1 (t - algebraMap k F a) < 1 :=
    fun v => (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hFF v).2 t
  obtain ⟨r, hr⟩ : ∃ r : Place k F → k, ∀ v : Place k F, v.1 t ≤ 1 → v.1 (t - algebraMap k F (r v)) < 1 :=
    ⟨fun v => if h : v.1 t ≤ 1 then (hres v h).choose else 0, fun v h => by
      simp only [dif_pos h]; exact (hres v h).choose_spec⟩
  have hlin0 : ∀ a : k, t - algebraMap k F a ≠ 0 := fun a h =>
    ht (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap a)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ∑ v ∈ D.support, (D v).natAbs := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : F, h = ∏ v ∈ D.support, (t - algebraMap k F (r v)) ^ (D v).natAbs :=
    ⟨_, rfl⟩
  have hh0 : h ≠ 0 := hh ▸ Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hlin0 _)
  have hordh : ∀ w : Place k F,
      ord w h = ∑ v ∈ D.support, ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)) := by
    intro w
    rw [hh, ord_prod w _ _ (fun v _ => pow_ne_zero _ (hlin0 _))]
    exact Finset.sum_congr rfl fun v _ => ord_pow w _ _
  obtain ⟨hhfin, hhsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF h hh0
  obtain ⟨n, f, hli, hn, hf⟩ := hc (2 * M)
  obtain ⟨P, hP⟩ : ∃ P : Place k F → ℤ,
      P = {v : Place k F | v.1 t⁻¹ < 1}.indicator fun v => ord v t⁻¹ := ⟨_, rfl⟩
  have hPpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 → P w = -ord w t := by
    intro w hw
    rw [hP, Set.indicator_of_mem (show w ∈ {v : Place k F | v.1 t⁻¹ < 1} from (hpole w).1 hw),
      ord_inv]
  have hPint : ∀ w : Place k F, w.1 t ≤ 1 → P w = 0 := by
    intro w hw
    rw [hP, Set.indicator_of_notMem (show w ∉ {v : Place k F | v.1 t⁻¹ < 1} from
      fun h' => (hpole w).2 h' hw)]
  have hPsupp : Function.support P ⊆ {v : Place k F | v.1 t⁻¹ < 1} := by
    intro w hw
    by_contra hw'
    exact hw (hPint w (by by_contra h'; exact hw' ((hpole w).1 h')))
  have hhsupp : Function.support (fun v : Place k F => ord v h) ⊆ {v : Place k F | v.1 h ≠ 1} := by
    intro v hv hv1
    exact hv (show ord v h = 0 by simp [ord, hv1])
  obtain ⟨g, hg⟩ : ∃ g : Place k F → ℤ, g = fun v => ((2 * M : ℕ) : ℤ) * P v + ord v h := ⟨_, rfl⟩
  have hgfin : (Function.support g).Finite := by
    refine (hPfin.union hhfin).subset fun v hv => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hv
    have h1 : P v = 0 := by
      by_contra h'; exact hnot.1 (hPsupp h')
    have h2 : ord v h = 0 := by simp [ord, hnot.2]
    simp [hg, h1, h2]
  refine ⟨Finsupp.ofSupportFinite g hgfin, ?_, n, fun i => f i * h⁻¹, ?_, ?_, ?_⟩
  ·
    intro w
    show D w ≤ g w
    simp only [hg]
    have hDM : D w ≤ (M : ℤ) := by
      by_cases hw : w ∈ D.support
      · have h1 := Finset.single_le_sum (f := fun v => (D v).natAbs) (fun _ _ => Nat.zero_le _) hw
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        rw [hM]
        have h3 : (((D w).natAbs : ℕ) : ℤ) ≤ ((∑ v ∈ D.support, (D v).natAbs : ℕ) : ℤ) :=
          Nat.cast_le.2 h1
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]; positivity
    by_cases ht1 : w.1 t ≤ 1
    · have hnn : ∀ v, 0 ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        (le_one_iff w (hlin0 _)).1
          ((Valuation.map_sub _ _ _).trans (max_le ht1 (val_algebraMap_le w _)))
      simp only [hPint w ht1, mul_zero, zero_add, hordh w]
      by_cases hw : w ∈ D.support
      · have hone : 0 < ord w (t - algebraMap k F (r w)) := (lt_one_iff w (hlin0 _)).1 (hr w ht1)
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        have h3 := Finset.single_le_sum
          (f := fun v => ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)))
          (fun v _ => mul_nonneg (by positivity) (hnn v)) hw
        have h4 : ((D w).natAbs : ℤ) ≤ ((D w).natAbs : ℤ) * ord w (t - algebraMap k F (r w)) := by
          nlinarith
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hnn v)
    · have hge : ∀ v, ord w t ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        ord_le_ord w (hlin0 _) ht0 ((Valuation.map_sub _ _ _).trans
          (max_le le_rfl ((val_algebraMap_le w _).trans (le_of_lt (not_le.1 ht1)))))
      have hsum : (M : ℤ) * ord w t ≤ ord w h := by
        rw [hordh, hM]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hge v) (by positivity)
      have hneg : ord w t < 0 := by
        have := (le_one_iff w ht0).not.1 ht1
        omega
      rw [hPpole w ht1]
      push_cast
      have hM0 : (0 : ℤ) ≤ M := by positivity
      nlinarith
  ·
    exact hli.map' (LinearMap.mulRight k h⁻¹)
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero hh0)))
  ·
    have hsub : Function.support g ⊆ ↑(Finsupp.ofSupportFinite g hgfin).support := by
      intro v hv
      exact Finsupp.mem_support_iff.2 hv
    have hdeg : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) =
        ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F := by
      have h1 : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ∑ᶠ v, g v := by
        rw [finsum_eq_sum_of_support_subset g hsub]
        rfl
      have hPsum : ∑ᶠ v, P v = Module.finrank k⟮t⟯ F := by
        rw [finsum_mem_def] at hPdeg
        rw [hP]; exact hPdeg
      rw [h1, hg]
      rw [finsum_add_distrib
        ((hPfin.subset hPsupp).subset fun v hv h0 => hv (by simp [h0]))
        (hhfin.subset hhsupp), ← mul_finsum, hhsum, hPsum, add_zero]
    rw [hdeg]
    push_cast
    calc ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F - c * Module.finrank k⟮t⟯ F
        = (((2 * M : ℕ) : ℤ) - c) * Module.finrank k⟮t⟯ F := by ring
      _ ≤ n := hn
  ·
    intro i w
    have hfi : f i ≠ 0 := hli.ne_zero i
    show -(g w) ≤ ord w (f i * h⁻¹)
    rw [ord_mul w hfi (inv_ne_zero hh0), ord_inv, hg]
    have key : -(((2 * M : ℕ) : ℤ) * P w) ≤ ord w (f i) := by
      by_cases ht1 : w.1 t ≤ 1
      · have h1 : w.1 (f i) ≤ 1 := by simpa [max_eq_left ht1] using hf i w
        rw [hPint w ht1]
        simpa using (le_one_iff w hfi).1 h1
      · have h1 : w.1 (f i) ≤ w.1 (t ^ (2 * M)) := by
          rw [map_pow]; simpa [max_eq_right (le_of_lt (not_le.1 ht1))] using hf i w
        have := ord_le_ord w hfi (pow_ne_zero _ ht0) h1
        rw [ord_pow] at this
        rw [hPpole w ht1]
        push_cast at this ⊢
        linarith
    simp only
    linarith

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
section
namespace GlobalTheory.IntFiniteTypeDim

theorem exists_natPrime_mem_of_isMaximal (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  letI := Ideal.Quotient.field m
  have hfin : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  rcases CharP.char_is_prime_or_zero (A ⧸ m) p with h | h
  · refine ⟨p, h, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · subst h
    haveI : CharZero (A ⧸ m) := CharP.charP_to_charZero _
    exfalso
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) :=
      RingHom.injective_int _
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (A ⧸ m)))

theorem ringKrullDim_quotient_le_of_minimalPrimes {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := s.head.1.asIdeal) s.head.2
  refine le_trans ?_ (h P hP)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) P) :=
    ⟨s.length, fun i => ⟨(s i).1, hle.trans (show s.head.1 ≤ (s i).1 from s.head_le i)⟩,
      fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

theorem ringKrullDim_eq_trdeg_add_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by
  intro A _ _ _ hinj
  haveI : CharZero A := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ℤ) (S := A))
  have hrhs : ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) =
      (d : WithBot ℕ∞) + 1 := by
    rw [hd, Cardinal.toENat_nat]; rfl
  rw [hrhs]
  apply le_antisymm
  · refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm => ?_
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    refine (Ideal.height_le_ringKrullDim_quotient_add_one hlm).trans ?_
    gcongr
    refine ringKrullDim_quotient_le_of_minimalPrimes _ _ fun q hq => ?_
    haveI := hq.1.1
    exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd).le
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {(l : A)}) (J := m)
      ((Ideal.span_singleton_le_iff_mem _).mpr hlm)
    haveI := hq.1.1
    rw [← ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd]
    have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      (r := (l : A)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hl.ne_zero))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hlq)

end GlobalTheory.IntFiniteTypeDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledRestrictionEndomorphisms
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.DivLin

theorem inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK (O := O) K H) := by
  have hf : Function.Injective (Algebra.linearMap O K) := IsFractionRing.injective O K
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K) hf
  have e : (inK K H : H →ₗ[O] K ⊗[O] H) =
      ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [e]
  exact h2.comp (TensorProduct.lid O H).symm.injective

section K

variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]

theorem algebraMap_bilin (B : LinearMap.BilinForm O H) (x y : H) :
    algebraMap O K (B x y) = B.baseChange K (inK K H x) (inK K H y) := by
  simp [inK, Algebra.algebraMap_eq_smul_one]

theorem inK_apply_end (f : Module.End O H) (h : H) : inK K H (f h) = f.baseChange K (inK K H h) := by
  simp [inK]

variable [Module.Free O H]

theorem restr_mul_eq_zero {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : N * N' = 0) : M * M' = 0 := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply, LinearMap.zero_apply, map_zero]
  rw [hM, hM', map_smul, ← Module.End.mul_apply N N', h]; simp

theorem restr_commute {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (f : Module.End O H)
    (hM : IsScaledRestr D N M) (h : Commute N (f.baseChange K)) : Commute M f := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply]
  rw [hM, inK_apply_end, inK_apply_end, hM, map_smul]
  congr 1
  exact LinearMap.congr_fun h.eq _

theorem restr_skew {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (h : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (x y : H) :
    B (M x) y + B x (M y) = 0 := by
  apply IsFractionRing.injective O K
  rw [map_add, algebraMap_bilin, algebraMap_bilin, hM, hM, map_zero]
  simp only [map_smul, LinearMap.smul_apply]
  rw [← smul_add, h, smul_zero]

theorem restr_iso {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : ∀ x y, B.baseChange K (N x) (N' y) = 0) (x y : H) :
    B (M x) (M' y) = 0 := by
  apply IsFractionRing.injective O K
  rw [algebraMap_bilin, hM, hM', map_zero]
  simp only [map_smul, LinearMap.smul_apply, h, smul_zero]

end K

section R

variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem baseChange_mul' (f g : Module.End O H) : (f * g).baseChange R = f.baseChange R * g.baseChange R := by
  ext x
  simp

theorem nilPart_eq (l : ℕ) (M : I → Module.End O H) (t : I → R) :
    nilPart l M R t = (lPrime l : R) • ∑ i, t i • (M i).baseChange R := rfl

theorem nilPart_sq {M : I → Module.End O H} (hMM : ∀ i j, M i * M j = 0) (l : ℕ) (t : I → R) :
    nilPart l M R t * nilPart l M R t = 0 := by
  have hSS : (∑ i, t i • (M i).baseChange R) * (∑ i, t i • (M i).baseChange R) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ← baseChange_mul', hMM,
      LinearMap.baseChange_zero, smul_zero, Finset.sum_const_zero]
  rw [nilPart_eq, smul_mul_smul_comm, hSS, smul_zero]

theorem nilPart_commute {M : I → Module.End O H} (f : Module.End O H) (hM : ∀ i, Commute (M i) f) (l : ℕ) (t : I → R) :
    Commute (nilPart l M R t) (f.baseChange R) := by
  rw [nilPart_eq]
  refine Commute.smul_left ?_ _
  refine Commute.sum_left _ _ _ fun i _ => Commute.smul_left ?_ _
  show _ * _ = _ * _
  rw [← baseChange_mul', ← baseChange_mul', (hM i).eq]

theorem baseChange_skew_iso (B : LinearMap.BilinForm O H) {M M' : Module.End O H}
    (hskew : ∀ x y, B (M x) y + B x (M y) = 0) (hiso : ∀ x y, B (M x) (M' y) = 0) (x y : R ⊗[O] H) :
    B.baseChange R (M.baseChange R x) y + B.baseChange R x (M.baseChange R y) = 0 ∧
      B.baseChange R (M.baseChange R x) (M'.baseChange R y) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
  | tmul c₀ a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add]
      exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
    | tmul c' b =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
      rw [← add_smul, hskew, hiso]
      simp

theorem nilPart_skew (B : LinearMap.BilinForm O H) {M : I → Module.End O H}
    (hskew : ∀ i x y, B (M i x) y + B x (M i y) = 0) (hiso : ∀ i j x y, B (M i x) (M j y) = 0) (l : ℕ) (t : I → R)
    (x y : R ⊗[O] H) :
    B.baseChange R (nilPart l M R t x) y + B.baseChange R x (nilPart l M R t y) = 0 := by
  simp only [nilPart_eq, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.sum_eq_zero fun i _ => by rw [(baseChange_skew_iso R B (hskew i) (hiso i i) x y).1, smul_zero], smul_zero]

theorem nilPart_iso (B : LinearMap.BilinForm O H) {M : I → Module.End O H}
    (hskew : ∀ i x y, B (M i x) y + B x (M i y) = 0) (hiso : ∀ i j x y, B (M i x) (M j y) = 0) (l : ℕ) (t : I → R)
    (x y : R ⊗[O] H) :
    B.baseChange R (nilPart l M R t x) (nilPart l M R t y) = 0 := by
  simp only [nilPart_eq, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    (baseChange_skew_iso R B (hskew _) (hiso _ _) _ _).2, smul_zero, Finset.sum_const_zero]

end R

end GlobalTheory.DivLin

namespace GlobalTheory.DivLin

theorem nilPart_claims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y := by
  intro E _ _ _ c O _ _ K _ _ _ H _ _ hfree ρ B I _ N D M hMN hcomm hNN hskew hiso l R _ _ t
  haveI := hfree
  have hMM : ∀ i j, M i * M j = 0 := fun i j => restr_mul_eq_zero (hMN i) (hMN j) (hNN i j)
  have hMρ : ∀ (a : OF E) i, Commute (M i) (ρ (ofF c a)) := fun a i => restr_commute _ (hMN i) (hcomm i a)
  have hMskew : ∀ i x y, B (M i x) y + B x (M i y) = 0 := fun i => restr_skew B (hMN i) (hskew i)
  have hMiso : ∀ i j x y, B (M i x) (M j y) = 0 := fun i j => restr_iso B (hMN i) (hMN j) (hiso i j)
  have hnn := nilPart_sq R hMM l t
  refine ⟨fun x => ⟨(∑ i, t i • (M i).baseChange R) x, ?_⟩, ⟨?_, ?_⟩, fun a => ?_, fun x y => ?_⟩
  · rw [LinearMap.add_apply, Module.End.one_apply, nilPart_eq, LinearMap.smul_apply]
  · rw [add_mul, one_mul, mul_sub, mul_one, hnn]; abel
  · rw [sub_mul, one_mul, mul_add, mul_one, hnn]; abel
  · exact (Commute.one_left _).add_left (nilPart_commute R _ (hMρ a) l t)
  · simp only [LinearMap.add_apply, Module.End.one_apply, map_add]
    linear_combination nilPart_skew R B hMskew hMiso l t x y + nilPart_iso R B hMskew hMiso l t x y

end GlobalTheory.DivLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctor
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem sec_of_basis_unit : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e s hs
  have uniq : ∀ (S : C) (y : F.obj S), (∀ t (w : S ⟶ G.obj t), mp F w y = 0) → y = 0 := by
    intro S y hy
    obtain ⟨n, b, hb, hb'⟩ := hcov S
    refine sep_std H hb y fun S'' u' ⟨i, hi⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' i S'' u' hi
    rw [mp_comp, hy t v, map_zero]
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, IsUnit (mp F u e) →
      ∀ t (w : S ⟶ G.obj t), mp F w y = s t (u ≫ w) := by
    intro S u
    by_cases h : IsUnit (mp F u e)
    · obtain ⟨y, hy⟩ := glue_comma_of_basis F G H hcov hdir S (fun t w ↦ s t (u ≫ w))
        fun t t' w a ↦ by
          rw [← Category.assoc]
          exact hs t t' (u ≫ w) a (isUnit_comp w h)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose x hx using hex
  refine ⟨x, fun S S' u ψ hu ↦ sub_eq_zero.1 (uniq S' _ fun t w ↦ ?_), fun t u hu ↦ ?_⟩
  · rw [map_sub, hx S' (u ≫ ψ) (isUnit_comp ψ hu) t w, ← mp_comp, hx S u hu t (ψ ≫ w),
      Category.assoc, sub_self]
  · have := hx (G.obj t) u hu t (𝟙 _)
    rwa [mp_id, Category.comp_id] at this

end GlobalTheory.CatCoh.Desc
end

