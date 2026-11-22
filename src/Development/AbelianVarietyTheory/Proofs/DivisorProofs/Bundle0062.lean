import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraBis
section
open FractionalIdeal nonZeroDivisors

namespace GlobalTheory.ClosingLemma

theorem main {Ω : Type} [Field Ω] (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S Ω] [IsFractionRing S Ω] (A : ValuationSubring Ω)
    (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  by_contra hcon
  push_neg at hcon
  have hSle : ∀ c : S, A.valuation (algebraMap S Ω c) ≤ 1 := fun c => (A.valuation_le_one_iff _).2 (hS c)
  let M : Submodule S Ω :=
    { carrier := {z | A.valuation z < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * A.valuation z := by
              gcongr; exact hSle c
          _ < 1 := by simpa using hz }
  let N : Submodule S Ω :=
    { carrier := {z | A.valuation z ≤ 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * 1 := by
              gcongr; exact hSle c
          _ = 1 := one_mul 1 }
  let J : FractionalIdeal S⁰ Ω := 1 + spanSingleton S⁰ x
  have hJ1 : (1 : FractionalIdeal S⁰ Ω) ≤ J := by
    show (1 : FractionalIdeal S⁰ Ω) ≤ 1 + spanSingleton S⁰ x
    rw [← sup_eq_add]; exact le_sup_left
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJ1
    exact one_ne_zero (le_antisymm hJ1 (zero_le _))
  have hJN : (J : Submodule S Ω) ≤ N := by
    simp only [J, coe_add, coe_one, coe_spanSingleton]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hz
      exact hSle c
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (A.valuation_le_one_iff _).2 hx
  have hinv : ((J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    intro y hy
    have hy' := (mem_inv_iff hJ0).1 hy
    obtain ⟨s, hs⟩ := (mem_one_iff S⁰).1 (by simpa using hy' 1 (hJ1 (one_mem_one _)))
    have hxJ : x ∈ J := by
      show x ∈ (J : Submodule S Ω)
      simp only [J, coe_add, coe_one, coe_spanSingleton]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    obtain ⟨t, ht⟩ := (mem_one_iff S⁰).1 (hy' x hxJ)
    show A.valuation y < 1
    rw [← hs] at ht ⊢
    exact lt_of_le_of_ne (hSle s) (fun h => hcon s t h ht.symm)
  have hmul : ((J * J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    rw [coe_mul, Submodule.mul_le]
    intro z hz y hy
    show A.valuation (z * y) < 1
    rw [map_mul]
    calc A.valuation z * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hJN hz
      _ < 1 := by rw [one_mul]; exact hinv hy
  rw [mul_inv_cancel₀ hJ0, coe_one] at hmul
  have := hmul (Submodule.one_le.1 le_rfl)
  exact absurd this (by show ¬ A.valuation 1 < 1; simp)

end GlobalTheory.ClosingLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraLast
section
namespace GlobalTheory.NonzeroSmulMembership

theorem exists_ne_zero_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • a • y := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (NumberField.RingOfIntegers E) E (by simpa using h))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • y) = p • a • y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [key]
    exact L.smul_mem p hay

end GlobalTheory.NonzeroSmulMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraSide
section
namespace GlobalTheory.ClosingLemmaFourth

theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherExtra
section
namespace GlobalTheory.SpectralLemmaSecond

open Matrix

theorem main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by
  intro d1 m k p _ _ _ M N
  simp only [d1]
  have hB : ∀ l : k, ∑ j : p, ‖N l j‖ ≤ ∑ l' : k, ∑ j : p, ‖N l' j‖ := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j : p, ‖N l' j‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ l)
  calc ∑ i : m, ∑ j : p, ‖(M * N) i j‖
      ≤ ∑ i : m, ∑ j : p, ∑ l : k, ‖M i l‖ * ‖N l j‖ := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        gcongr with l _
        exact (norm_mul _ _).le
    _ = ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ j : p, ‖N l j‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        gcongr with i _ l _
        exact hB l
    _ = (∑ i : m, ∑ l : k, ‖M i l‖) * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end GlobalTheory.SpectralLemmaSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherLast
section
namespace GlobalTheory.ValuationExtensionExistence

theorem exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R)]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)

theorem main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_TFAE ρ).out 4 0).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev

end GlobalTheory.ValuationExtensionExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTail
section
namespace GlobalTheory.IntegralNormAtMostOne

theorem norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hcon
  have h1 : 1 < ‖y‖ := not_le.mp hcon
  have h0 : 0 < ‖y‖ := lt_trans one_pos h1
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, one_smul] at hpy
  have heq : y ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, p.coeff i • y ^ i :=
    eq_neg_of_add_eq_zero_right hpy
  have hlt : ∀ (s : Finset ℕ), (∀ i ∈ s, i < p.natDegree) →
      ‖∑ i ∈ s, p.coeff i • y ^ i‖ < ‖y‖ ^ p.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using pow_pos h0 _
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [zsmul_eq_mul, norm_mul, norm_pow]
        have hc : ‖((p.coeff a : ℤ) : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        calc ‖((p.coeff a : ℤ) : ℂ_[l])‖ * ‖y‖ ^ a ≤ 1 * ‖y‖ ^ a :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg h0.le _)
          _ = ‖y‖ ^ a := one_mul _
          _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ h1 (hs a (Finset.mem_insert_self _ _))
      · exact ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
  have := hlt (Finset.range p.natDegree) fun i hi => Finset.mem_range.mp hi
  rw [← norm_neg, ← heq, norm_pow] at this
  exact lt_irrefl _ this

end GlobalTheory.IntegralNormAtMostOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastRest
section
noncomputable section

open MeasureTheory

namespace GlobalTheory.Pc3.RS

theorem exists_finset_sep {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∀ (m : ℕ) (K : Submodule ℂ W), Module.finrank ℂ K = m →
      ∃ S : Finset X, ∀ w ∈ K, (∀ s ∈ S, (w : X → ℂ) s = 0) → w = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K hK
    by_cases h0 : K = ⊥
    · exact ⟨∅, fun w hw _ => by rw [h0] at hw; exact (Submodule.mem_bot ℂ).1 hw⟩
    · obtain ⟨w0, hw0K, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      have : ∃ x0, (w0 : X → ℂ) x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (Subtype.ext (funext hc))
      obtain ⟨x0, hx0⟩ := this
      let e : W →ₗ[ℂ] ℂ := (LinearMap.proj x0).comp W.subtype
      let K' : Submodule ℂ W := K ⊓ LinearMap.ker e
      have hlt : K' < K := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have : w0 ∈ K' := heq ▸ hw0K
        exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
      have hr : Module.finrank ℂ K' < m := hK ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨S, hS⟩ := ih _ hr K' rfl
      refine ⟨insert x0 S, fun w hw hv => hS w (Submodule.mem_inf.2 ⟨hw, ?_⟩) fun s hs => hv s (Finset.mem_insert_of_mem hs)⟩
      exact LinearMap.mem_ker.2 (hv x0 (Finset.mem_insert_self _ _))

theorem integral_mem {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] (G : Y → X → ℂ) (hG : ∀ y, G y ∈ W) (hi : ∀ x, Integrable (fun y => G y x) μ) :
    (fun x => ∫ y, G y x ∂μ) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_sep W _ ⊤ rfl
  let r : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w s => (w : X → ℂ) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact hS w Submodule.mem_top fun s hs => congrFun hw ⟨s, hs⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective r hinj
  have key : ∀ (w : W) (x : X), (w : X → ℂ) x = ∑ s : S, (w : X → ℂ) s * ((L (Pi.single s 1) : W) : X → ℂ) x := by
    intro w x
    have h1 : L (r w) = w := by simpa using LinearMap.congr_fun hL w
    have h2 : r w = ∑ s : S, (w : X → ℂ) s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [r, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]
    simp [map_sum, map_smul, Finset.sum_apply]
  have hfun : (fun x => ∫ y, G y x ∂μ) =
      ((∑ s : S, (∫ y, G y s ∂μ) • L (Pi.single s 1) : W) : X → ℂ) := by
    funext x
    have e : ∀ y, G y x = ∑ s : S, G y s * ((L (Pi.single s 1) : W) : X → ℂ) x :=
      fun y => key ⟨G y, hG y⟩ x
    simp_rw [e]
    rw [integral_finsetSum (Finset.univ : Finset S) fun (s : S) _ =>
      (hi (s : X)).mul_const (((L (Pi.single s 1) : W) : X → ℂ) x)]
    simp only [integral_mul_const, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.coe_mem _

end GlobalTheory.Pc3.RS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreAlt
section
namespace GlobalTheory.AbelianSumIdentityThird

theorem main : ∀ {S : Type} [inst : Ring S] (ε a b Gi K : S), (∀ (x : S), ε * x = x * ε) → ε * ε = ε → ε * a = a → ε * b = b → ((1 : S) - K) * a = ε → a * ((1 : S) - K) = ε → ((1 : S) - Gi * K) * b = ε → b * ((1 : S) - Gi * K) = ε → ((1 : S) - ε + b * ((1 : S) - K)) * ((1 : S) - ε + a * ((1 : S) - Gi * K)) = (1 : S) ∧ ((1 : S) - ε + a * ((1 : S) - Gi * K)) * ((1 : S) - ε + b * ((1 : S) - K)) = (1 : S) := by
  intro S _ ε a b Gi K hc hε ha hb h1 h2 h3 h4
  have haε : a * ε = a := by rw [← hc]; exact ha
  have hbε : b * ε = b := by rw [← hc]; exact hb
  have t1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  have t2a : (1 - ε) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
  have t2b : (1 - ε) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
  have t3 : ∀ x y : S, x * ε = x → x * y * (1 - ε) = 0 := by
    intro x y hx
    rw [mul_sub, mul_one, mul_assoc, ← hc y, ← mul_assoc, hx, sub_self]
  constructor
  · have e : b * (1 - K) * (a * (1 - Gi * K)) = ε := by
      rw [← mul_assoc, mul_assoc b, h1, hbε, h4]
    calc (1 - ε + b * (1 - K)) * (1 - ε + a * (1 - Gi * K))
        = (1 - ε) * (1 - ε) + (1 - ε) * a * (1 - Gi * K) + b * (1 - K) * (1 - ε)
          + b * (1 - K) * (a * (1 - Gi * K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2a, t3 b _ hbε, e]; noncomm_ring
  · have e : a * (1 - Gi * K) * (b * (1 - K)) = ε := by
      rw [← mul_assoc, mul_assoc a, h3, haε, h2]
    calc (1 - ε + a * (1 - Gi * K)) * (1 - ε + b * (1 - K))
        = (1 - ε) * (1 - ε) + (1 - ε) * b * (1 - K) + a * (1 - Gi * K) * (1 - ε)
          + a * (1 - Gi * K) * (b * (1 - K)) := by noncomm_ring
      _ = 1 := by rw [t1, t2b, t3 a _ haε, e]; noncomm_ring

end GlobalTheory.AbelianSumIdentityThird
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreBis
section
namespace GlobalTheory.TargetSimplification

theorem main {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V] {s : E →+* E} {r : ℕ}
  (B : V →ₛₗ[s] V →ₗ[E] E) (hB : ∀ u v : V, B u v = s (B v u))
  {x y : Fin r → V} (hx : ∀ i j, B (x i) (x j) = 0) (hy : ∀ i j, B (y i) (y j) = 0)
  (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
  {z w₀ : V} (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0)
  (hzw : B z w₀ = 1) :
  ∃ (x' y' : Fin (r+1) → V), (∀ i j, B (x' i) (x' j) = 0) ∧ (∀ i j, B (y' i) (y' j) = 0) ∧
    (∀ i j, B (x' i) (y' j) = if i = j then 1 else 0) ∧ ∀ i : Fin r, x' (Fin.castSucc i) = x i := by
  have hyx : ∀ i j, B (y i) (x j) = if i = j then 1 else 0 := by
    intro i j; rw [hB, hxy]; by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hzx : ∀ i, B z (x i) = 0 := fun i => by rw [hB, hxz, map_zero]
  have hzy : ∀ i, B z (y i) = 0 := fun i => by rw [hB, hyz, map_zero]
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : V, w₁ = w₀ - ∑ j, B (y j) w₀ • x j - ∑ j, B (x j) w₀ • y j := ⟨_, rfl⟩
  have hxw₁ : ∀ i, B (x i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hx, hxy]
  have hyw₁ : ∀ i, B (y i) w₁ = 0 := by
    intro i; simp [hw₁, map_sub, map_sum, hy, hyx]
  have hzw₁ : B z w₁ = 1 := by simp [hw₁, map_sub, map_sum, hzx, hzy, hzw]
  have h1 : B w₁ z = 1 := by rw [hB, hzw₁, map_one]
  have ht : s (B w₁ w₁) = B w₁ w₁ := (hB w₁ w₁).symm
  obtain ⟨c, hc⟩ : ∃ c : E, c = -(B w₁ w₁ / 2) := ⟨_, rfl⟩
  have hsc : s c = c := by rw [hc, map_neg, map_div₀, ht, map_ofNat]
  obtain ⟨w, hw⟩ : ∃ w : V, w = w₁ + c • z := ⟨_, rfl⟩
  have hxw : ∀ i, B (x i) w = 0 := by intro i; simp [hw, hxw₁, hxz]
  have hyw : ∀ i, B (y i) w = 0 := by intro i; simp [hw, hyw₁, hyz]
  have hwy : ∀ i, B w (y i) = 0 := fun i => by rw [hB, hyw, map_zero]
  have hzw' : B z w = 1 := by simp [hw, hzw₁, hzz]
  have hww : B w w = 0 := by
    simp only [hw, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hzz, h1, hsc, hzw₁]
    rw [hc]; simp only [RingHom.id_apply]; ring
  refine ⟨Fin.snoc x z, Fin.snoc y w, ?_, ?_, ?_, ?_⟩
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hx, hxz, hzx, hzz]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hy, hyw, hwy, hww]
  · intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Fin.snoc_castSucc, Fin.snoc_last, hxy, hxw, hzy, hzw', Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  · intro i; simp

end GlobalTheory.TargetSimplification
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreFurther
section
namespace GlobalTheory.TargetEquivalence

open Finset

theorem main {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        exact Finset.sum_comm

theorem target : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β] (f : α → β → α → β → R), ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e :=
  fun f => main f

end GlobalTheory.TargetEquivalence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreRest
section
namespace GlobalTheory.AbelianSumIdentityFourth

open Matrix

theorem main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A), RY * X = (1 : Matrix (Fin q) (Fin q) A) → RY * Y = (0 : Matrix (Fin q) (Fin q) A) → RX * X = (0 : Matrix (Fin q) (Fin q) A) → RX * Y = (1 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + a' i + a i * a' i = (0 : A)) → (∀ (i : Fin q), b i + b' i + b i * b' i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a * RY + Y * Matrix.diagonal b * RX) * ((1 : Matrix (Fin n) (Fin n) A) + X * Matrix.diagonal a' * RY + Y * Matrix.diagonal b' * RX) = (1 : Matrix (Fin n) (Fin n) A) := by
  intro A _ n q X Y RX RY a b a' b' h1 h2 h3 h4 ha hb
  have e1 : ∀ {m : Type} (M : Matrix (Fin q) m A), RY * (X * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : ∀ {m : Type} (M : Matrix (Fin q) m A), RY * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have e3 : ∀ {m : Type} (M : Matrix (Fin q) m A), RX * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  have e4 : ∀ {m : Type} (M : Matrix (Fin q) m A), RX * (Y * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have hDa : Matrix.diagonal a + Matrix.diagonal a' + Matrix.diagonal a * Matrix.diagonal a' = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, ha i]
    · simp [Matrix.diagonal_apply, hij]
  have hDb : Matrix.diagonal b + Matrix.diagonal b' + Matrix.diagonal b * Matrix.diagonal b' = 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal_apply, hb i]
    · simp [Matrix.diagonal_apply, hij]
  have kx : X * (Matrix.diagonal a * RY) + X * (Matrix.diagonal a' * RY)
      + X * (Matrix.diagonal a * (Matrix.diagonal a' * RY)) = 0 := by
    have := congrArg (fun M => X * (M * RY)) hDa
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] using this
  have ky : Y * (Matrix.diagonal b * RX) + Y * (Matrix.diagonal b' * RX)
      + Y * (Matrix.diagonal b * (Matrix.diagonal b' * RX)) = 0 := by
    have := congrArg (fun M => Y * (M * RX)) hDb
    simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero] using this
  calc _ = 1 + (X * (Matrix.diagonal a * RY) + X * (Matrix.diagonal a' * RY)
          + X * (Matrix.diagonal a * (Matrix.diagonal a' * RY)))
        + (Y * (Matrix.diagonal b * RX) + Y * (Matrix.diagonal b' * RX)
          + Y * (Matrix.diagonal b * (Matrix.diagonal b' * RX))) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul,
          e1, e2, e3, e4, Matrix.zero_mul, Matrix.mul_zero, add_zero]
        abel
    _ = 1 := by rw [kx, ky, add_zero, add_zero]

end GlobalTheory.AbelianSumIdentityFourth
end

