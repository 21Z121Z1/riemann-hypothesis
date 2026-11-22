import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalNormalIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalNormalIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    ∀ [IsFractionRing O L] (m : Ideal O) [m.IsMaximal],
      (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors).toSubring.toAddSubgroup.relIndex
        (integralClosure (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors) L).toSubring.toAddSubgroup ≠ 0

example : ∃ (O : Subalgebra ℤ ℚ) (m : Ideal O), Algebra.FiniteType ℤ O ∧
    IsFractionRing O ℚ ∧ m.IsMaximal := by
  let e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ := Algebra.botEquivOfInjective Int.cast_injective
  have hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ) := Algebra.FiniteType.equiv inferInstance e.symm
  have hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ := by
    refine IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp [Rat.num_div_den]
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top
  exact ⟨⊥, m, hft, hfr, hm⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlacesRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) : Subring L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  zero_mem' := fun w _ ↦ by simp
  one_mem' := fun w _ ↦ by simp
  add_mem' := fun hx hy w hw ↦ (FinitePlace.add_le w _ _).trans (max_le (hx w hw) (hy w hw))
  neg_mem' := fun hx w hw ↦ by simpa [map_neg_eq_map] using hx w hw
  mul_mem' := fun hx hy w hw ↦ by
    rw [map_mul]
    exact mul_le_one₀ (hx w hw) (apply_nonneg w _) (hy w hw)

theorem mem_placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : L) :
    x ∈ placesRing S ↔ ∀ w ∈ S, w x ≤ 1 := Iff.rfl

example {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : 𝓞 L) :
    algebraMap (𝓞 L) L x ∈ placesRing S := fun w _ ↦ by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one _ _ x

example : placesRing (∅ : Set (FinitePlace ℚ)) = ⊤ :=
  eq_top_iff.2 fun _ _ w hw ↦ absurd hw (Set.notMem_empty w)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightSemilocalQuotCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def integralAtPlaces {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) :
    Subalgebra ℤ L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul]
    exact mul_le_one₀ (ha w hw) (apply_nonneg w b) (hb w hw)
  add_mem' {a b} ha hb w hw := (FinitePlace.add_le w a b).trans (max_le (ha w hw) (hb w hw))
  algebraMap_mem' z w _ := by
    rw [eq_intCast, ← FinitePlace.mk_maximalIdeal w, FinitePlace.mk_apply,
      FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.adicAbv_intCast_le_one (K := L) (v := w.maximalIdeal) z

def SemilocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ t : integralAtPlaces S, t ≠ 0 →
      (Nat.card (integralAtPlaces S ⧸ Ideal.span {t}) : ℝ) = ∏ᶠ w ∈ S, (w (t : L))⁻¹

example : ∃ (S : Set (FinitePlace ℚ)) (t : integralAtPlaces S), S.Finite ∧ S.Nonempty ∧ t ≠ 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
  have hne : P ≠ ⊥ := fun h ↦
    RingOfIntegers.not_isField ℚ (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨P, hP.isPrime, hne⟩
  refine ⟨{FinitePlace.mk v}, 2, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
  intro h
  have := congrArg (fun y : integralAtPlaces ({FinitePlace.mk v} : Set (FinitePlace ℚ)) ↦ (y : ℚ)) h
  norm_num at this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightSubringPrimeMaximal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def SubringPrimeMaximal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subalgebra ℤ K) (q : Ideal O),
    q.IsPrime → q ≠ ⊥ → q.IsMaximal

example : ∃ q : Ideal (⊥ : Subalgebra ℤ ℚ), q.IsPrime ∧ q ≠ ⊥ := by
  let e := Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  refine ⟨Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}), Ideal.comap_isPrime _ _, ?_⟩
  intro h
  have hm : (2 : (⊥ : Subalgebra ℤ ℚ)) ∈
      Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}) := by
    rw [Ideal.mem_comap, map_ofNat]
    exact Ideal.mem_span_singleton_self 2
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Subtype.val hm
  norm_num at this

end GroundTheory.Heights₂.Heights
end

