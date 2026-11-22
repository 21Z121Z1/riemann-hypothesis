import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegHorPf
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem not_isUnit_algebraMap_of_finite {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by
  intro hu
  have htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤ := by
    intro v _
    obtain ⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v :=
      ⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    rw [← hw, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤
    Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
  have h1 : (1 : V) ∈ (⊥ : Submodule O V) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot O).mp h1)

theorem reg_horizontal_pf {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  obtain ⟨a, s, haP, hsP, hfas⟩ := hdvr hno
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hno ⟨0, 1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩
  have hs0 : algebraMap A (FractionRing A) s ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro rfl; exact hsP P.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hfas
    rcases hfas with h | h
    · exact hf0 (inv_eq_zero.mp h)
    · exact hs0 h
  have hfa : f * algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) s := by
    rw [← hfas, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hmapw : Ideal.map (algebraMap O A) (maximalIdeal O) = Ideal.span {algebraMap O A ϖ} := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hwP : algebraMap O A ϖ ∉ P := fun h =>
    hh (by rw [hmapw, Ideal.span_le, Set.singleton_subset_iff]; exact h)
  have hws : algebraMap O A ϖ * s ∉ P := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hwP hsP
  have hws0 : algebraMap A (FractionRing A) (algebraMap O A ϖ * s) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro h; exact hws (h ▸ P.zero_mem)

  have hOA : Function.Injective (algebraMap O A) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, mul_eq_zero] at hx
    rcases hx with h | h
    · exact (u.isUnit.map (algebraMap O A)).ne_zero h
    · exact hwP (pow_eq_zero_iff'.mp h |>.1 ▸ P.zero_mem)

  set y : FractionRing A := algebraMap A (FractionRing A) a /
    algebraMap A (FractionRing A) (algebraMap O A ϖ * s) with hy
  let B : Subalgebra A (FractionRing A) := Algebra.adjoin A {y}
  have hyB : y ∈ B := Algebra.subset_adjoin rfl

  let S : Subalgebra A (FractionRing A) :=
    { carrier := {x | ∃ a' p t : A, p ∈ P ∧ t ∉ P ∧
        x * algebraMap A (FractionRing A) t = algebraMap A (FractionRing A) (a' * t + p)}
      mul_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 * a2, a1 * t1 * p2 + a2 * t2 * p1 + p1 * p2, t1 * t2,
          P.add_mem (P.add_mem (P.mul_mem_left _ hp2) (P.mul_mem_left _ hp1)) (P.mul_mem_left _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : x1 * x2 * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * (x2 * algebraMap A (FractionRing A) t2) := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul]
        congr 1
        ring
      add_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 + a2, p1 * t2 + p2 * t1, t1 * t2,
          P.add_mem (P.mul_mem_right _ hp1) (P.mul_mem_right _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : (x1 + x2) * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * algebraMap A (FractionRing A) t2 +
              (x2 * algebraMap A (FractionRing A) t2) * algebraMap A (FractionRing A) t1 := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul, ← map_mul, ← map_add]
        congr 1
        ring
      algebraMap_mem' := fun r => ⟨r, 0, 1, P.zero_mem, (Ideal.ne_top_iff_one P).mp
        (Ideal.IsPrime.ne_top ‹_›), by simp⟩ }
  have hyS : y ∈ S := ⟨0, a, algebraMap O A ϖ * s, haP, hws, by
    rw [hy, div_mul_cancel₀ _ hws0]; simp⟩
  have hBS : B ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyS)

  have hcoe : ∀ r : O, ((algebraMap O B r : B) : FractionRing A) =
      algebraMap A (FractionRing A) (algebraMap O A r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply O A (FractionRing A)]
    rfl
  have hOB : Function.Injective (algebraMap O B) := by
    intro r1 r2 h
    apply hOA; apply hinj
    rw [← hcoe, ← hcoe, h]
  have : Module.Flat O B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, Algebra.smul_def] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact absurd (hOB (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero r)
    · rw [h]; exact Submodule.zero_mem _
  have : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType B).mp (by simpa using Subalgebra.fg_adjoin_finset ({y} : Finset _))
  have : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance

  have hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤ := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨a', p, t, hp, ht, h⟩ := hBS (↑u⁻¹ : B).2
    apply hmeet
    rw [eq_top_iff, hmapw]
    have hwb : algebraMap A (FractionRing A) (algebraMap O A ϖ) * ((↑u⁻¹ : B) : FractionRing A) = 1 := by
      rw [← hcoe, ← hu, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hkey : algebraMap A (FractionRing A) (t - algebraMap O A ϖ * (a' * t + p)) = 0 := by
      rw [map_sub, map_mul, ← h]
      calc algebraMap A (FractionRing A) t - algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            (((↑u⁻¹ : B) : FractionRing A) * algebraMap A (FractionRing A) t)
          = algebraMap A (FractionRing A) t - (algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            ((↑u⁻¹ : B) : FractionRing A)) * algebraMap A (FractionRing A) t := by ring
        _ = 0 := by rw [hwb, one_mul, sub_self]
    have hk := hinj (hkey.trans (map_zero _).symm)
    have htw : t * (1 - algebraMap O A ϖ * a') ∈ P := by
      have : t * (1 - algebraMap O A ϖ * a') = algebraMap O A ϖ * p := by
        linear_combination hk
      rw [this]; exact P.mul_mem_left _ hp
    have h1 : 1 - algebraMap O A ϖ * a' ∈ P :=
      (Ideal.IsPrime.mem_or_mem ‹_› htw).resolve_left ht
    have : (1 : A) = (1 - algebraMap O A ϖ * a') + algebraMap O A ϖ * a' := by ring
    intro z _
    rw [← mul_one z, this, mul_add]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left _ h1))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Ideal.subset_span rfl))))

  have heas : algebraMap A B (e * a * s) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : B => (x : FractionRing A)) h
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h'
    have := hinj (h'.trans (map_zero _).symm)
    rcases mul_eq_zero.mp this with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact he h3
      · exact ha0 h3
    · exact hsP (h2 ▸ P.zero_mem)
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point hsp _ heas
  let φA : A →ₐ[O] V := φ.comp (IsScalarTower.toAlgHom O A B)
  have hφA : ∀ x : A, φA x = φ (algebraMap A B x) := fun x => rfl
  rw [map_mul, map_mul, map_mul, map_mul] at hφ
  have hφe : φA e ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφa : φA a ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφs : φA s ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  obtain ⟨v, hv⟩ := hf V φA s a hfa hφa hφe

  have hab : algebraMap A B a = algebraMap O B ϖ * algebraMap A B s * ⟨y, hyB⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply O A (FractionRing A) ϖ, hy, ← map_mul]
    field_simp
  have hφab : φA a = algebraMap O V ϖ * φA s * φ ⟨y, hyB⟩ := by
    rw [hφA, hab, map_mul, map_mul, AlgHom.commutes]
    rfl
  rw [hφab] at hv
  have hunit : algebraMap O V ϖ * (v * φ ⟨y, hyB⟩) = 1 := by
    have h2 : φA s * (1 - algebraMap O V ϖ * (v * φ ⟨y, hyB⟩)) = 0 := by
      linear_combination hv
    have h3 := (mul_eq_zero.mp h2).resolve_left hφs
    linear_combination -h3
  exact not_isUnit_algebraMap_of_finite ϖ hϖm
    ⟨⟨algebraMap O V ϖ, v * φ ⟨y, hyB⟩, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem regVert_eq_of_le_height_one {A : Type*} [CommRing A] [IsDomain A] {Q P : Ideal A} [Q.IsPrime]
    [P.IsPrime] (hQ : Q ≠ ⊥) (hQP : Q ≤ P) (hP : P.height = 1) : Q = P := by
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP hne
  have hbot : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQ
  have hQle : Q.height ≤ 1 := hP ▸ Ideal.height_mono hQP
  have hQfin : Q.height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hQle
  haveI : Q.FiniteHeight := ⟨Or.inr hQfin⟩
  haveI : (⊥ : Ideal A).FiniteHeight := ⟨Or.inr (by simp)⟩
  have h1 : (⊥ : Ideal A).height + 1 ≤ Q.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hbot)
  have h2 : Q.height + 1 ≤ P.height := by
    first
    | exact ENat.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
    | exact Order.add_one_le_of_lt (Ideal.height_strict_mono_of_isPrime hlt)
  rw [hP] at h2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal A).height + 1 + 1 := by gcongr; simp
      _ ≤ Q.height + 1 := by gcongr
      _ ≤ 1 := h2
  exact absurd h3 (by norm_num)

theorem regVert_valuationRing {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ValuationRing (Localization.AtPrime P) := by
  have hPne : P ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal A).height = 0 := by
      first
      | exact Ideal.height_bot
      | simp
    rw [h0] at hP
    exact zero_ne_one hP
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hmax : Ideal.map (algebraMap A (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcm : Ideal.comap (algebraMap A (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) = P := by
    first
    | exact Localization.AtPrime.comap_maximalIdeal
    | exact IsLocalization.AtPrime.comap_maximalIdeal _ P
  have hmne : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≠ ⊥ := by
    rw [← hmax]
    intro h
    exact hPne ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hmne
  haveI : IsDomain (Localization.AtPrime P) := by
    first
    | infer_instance
    | exact IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI hic : IsIntegrallyClosed (Localization.AtPrime P) := by
    first
    | exact isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact IsIntegrallyClosed.of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
    | exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
  have huniq : ∃! Q' : Ideal (Localization.AtPrime P), Q' ≠ ⊥ ∧ Q'.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal _, ⟨hmne, inferInstance⟩, ?_⟩
    rintro Q' ⟨hQ'ne, hQ'p⟩
    haveI := hQ'p
    have hc : Q'.under A ≤ P := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'p.ne_top)).trans hcm.le
    have hcne : Q'.under A ≠ ⊥ := by
      intro h
      apply hQ'ne
      rw [← IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) Q', h, Ideal.map_bot]
    have heq := regVert_eq_of_le_height_one hcne hc hP
    rw [← IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) Q', heq, hmax]
  first
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 2).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr (And.intro hic huniq)
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 3).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 2).mpr (And.intro hic huniq))
  | exact @ValuationRing.of_isDiscreteValuationRing _ _ _ (((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 5).mpr (And.intro hic huniq))
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 3).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 4).mpr (And.intro hic huniq)
  | exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 2 5).mpr (And.intro hic huniq)

theorem reg_vertical {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  haveI : ValuationRing (Localization.AtPrime P) := regVert_valuationRing P hP
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinjOA : Function.Injective (algebraMap O A) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hfl := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := O) (M := A)).1 inferInstance
    have h1 : (1 : A) ∈ Submodule.torsion O A :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨x, mem_nonZeroDivisors_of_ne_zero hx0⟩, by
        simp [Algebra.smul_def, hx]⟩
    rw [hfl] at h1
    exact one_ne_zero ((Submodule.mem_bot O).1 h1)
  have ht0 : algebraMap O A ϖ ≠ 0 := fun h => hϖ0 (hinjOA (by rw [h, map_zero]))
  have htP : algebraMap O A ϖ ∈ P := hv (Ideal.mem_map_of_mem _ hϖm)
  have hmin : P ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 htP⟩, fun Q hQ hQP => ?_⟩
    haveI := hQ.1
    have hQ0 : Q ≠ ⊥ := fun h => ht0 (by
      have := hQ.2 (Ideal.mem_span_singleton_self (algebraMap O A ϖ)); rw [h] at this; exact this)
    exact (regVert_eq_of_le_height_one hQ0 hQP hP).symm.le
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqK : algebraMap A (FractionRing A) q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hfq : f * algebraMap A (FractionRing A) q = algebraMap A (FractionRing A) p := by
    rw [← hpq, div_mul_cancel₀ _ hqK]
  have hinjAR : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have key : ∀ d : Localization.AtPrime P,
      algebraMap A (Localization.AtPrime P) q * d = algebraMap A (Localization.AtPrime P) p → False := by
    intro d hd
    obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj P.primeCompl d
    simp only at hcs
    apply hno
    refine ⟨a, s, s.2, ?_⟩
    have h3 : algebraMap A (Localization.AtPrime P) (q * a) = algebraMap A (Localization.AtPrime P) (p * s) := by
      rw [map_mul, map_mul, ← hd, mul_assoc, hcs]
    have h2 := hinjAR h3
    apply mul_left_cancel₀ hqK
    calc algebraMap A (FractionRing A) q * (f * algebraMap A (FractionRing A) s)
        = (f * algebraMap A (FractionRing A) q) * algebraMap A (FractionRing A) s := by ring
      _ = algebraMap A (FractionRing A) (p * s) := by rw [hfq, map_mul]
      _ = algebraMap A (FractionRing A) (q * a) := by rw [h2]
      _ = _ := by rw [map_mul]
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime P) q)
    (algebraMap A (Localization.AtPrime P) p)
  · exact key c hc
  have hcm : c ∈ maximalIdeal (Localization.AtPrime P) := by
    by_contra hcu
    have hu : IsUnit c := by
      by_contra h
      exact hcu ((IsLocalRing.mem_maximalIdeal c).2 h)
    refine key (↑hu.unit⁻¹) ?_
    rw [← hc, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime P)
    P _ hmin
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hc' : c ∈ (Ideal.map (algebraMap A (Localization.AtPrime P))
      (Ideal.span {algebraMap O A ϖ})).radical := hrad ▸ hcm
  obtain ⟨n, hn⟩ := hc'
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hn
  obtain ⟨z, hz⟩ := hn
  let S : Subalgebra A (Localization.AtPrime P) := Algebra.adjoin A {z}
  haveI : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).1 (by
    simpa using Subalgebra.fg_adjoin_finset (R := A) ({z} : Finset (Localization.AtPrime P)))
  haveI : Algebra.FiniteType O S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hinjOR : Function.Injective (algebraMap O (Localization.AtPrime P)) := by
    rw [IsScalarTower.algebraMap_eq O A (Localization.AtPrime P)]; exact hinjAR.comp hinjOA
  have hcoe : ∀ x : O, ((algebraMap O S x : S) : Localization.AtPrime P) =
      algebraMap O (Localization.AtPrime P) x := fun x => rfl
  haveI : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).2 (by
    intro x y hxy
    apply hinjOR
    rw [← hcoe, ← hcoe, hxy])
  have hsp : Ideal.map (algebraMap O S) (maximalIdeal O) ≠ ⊤ := by
    intro htop
    have h2 : Ideal.map (S.val : S →+* Localization.AtPrime P)
        (Ideal.map (algebraMap O S) (maximalIdeal O)) ≤ maximalIdeal (Localization.AtPrime P) := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.comp_apply]
      have : (S.val : S →+* Localization.AtPrime P) (algebraMap O S x) =
          algebraMap A (Localization.AtPrime P) (algebraMap O A x) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [this]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2
        (hv (Ideal.mem_map_of_mem _ hx))
    rw [htop, Ideal.map_top] at h2
    exact (maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top (top_le_iff.1 h2)
  have hqS : algebraMap A S q ≠ 0 := by
    intro h0
    apply hq0; apply hinjAR
    rw [map_zero]
    exact congrArg Subtype.val h0
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point (O := O) (B := S) hsp (algebraMap A S q) hqS
  obtain ⟨w, hw⟩ := hf V (φ.comp (IsScalarTower.toAlgHom O A S)) p q hfq hφ
  have hzS : z ∈ S := Algebra.subset_adjoin (Set.mem_singleton z)
  have hrel : (algebraMap A S q) ^ n = (algebraMap A S p) ^ n * (⟨z, hzS⟩ * algebraMap O S ϖ) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, MulMemClass.coe_mul]
    change (algebraMap A (Localization.AtPrime P) q) ^ n =
      (algebraMap A (Localization.AtPrime P) p) ^ n * (z * algebraMap O (Localization.AtPrime P) ϖ)
    rw [IsScalarTower.algebraMap_apply O A (Localization.AtPrime P) ϖ, hz, ← hc, mul_pow]
  have h1 := congrArg φ hrel
  rw [map_pow, map_mul, map_pow, map_mul, AlgHom.commutes] at h1
  have hw' : φ (algebraMap A S p) = w * φ (algebraMap A S q) := hw
  rw [hw', mul_pow] at h1
  have hunit : IsUnit (algebraMap O V ϖ) := by
    refine IsUnit.of_mul_eq_one (w ^ n * φ ⟨z, hzS⟩) ?_
    have hQ : φ (algebraMap A S q) ^ n ≠ 0 := pow_ne_zero _ hφ
    apply mul_left_cancel₀ hQ
    linear_combination -h1
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) (maximalIdeal V)
  have heq : Ideal.comap (algebraMap O V) (maximalIdeal V) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  have hmV : algebraMap O V ϖ ∈ maximalIdeal V := by
    rw [← Ideal.mem_comap, heq]; exact hϖm
  exact (IsLocalRing.mem_maximalIdeal _).1 hmV hunit

end ReciprocityTheory.ChartRestriction.G.T0
end

