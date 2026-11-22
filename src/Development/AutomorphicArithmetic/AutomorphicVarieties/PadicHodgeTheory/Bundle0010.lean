import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartChange
section
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : ∃ g : σ → MvPowerSeries σ O, f = ∑ i, MvPowerSeries.X i * g i :=
  _root_.UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X f hf

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem lin_part {E : Type} [Field E] {n : ℕ} (f : MvPowerSeries (Fin n) E)
    (hf : constantCoeff f = 0) :
    f - ∑ j, coeff (Finsupp.single j 1) f • (X j : MvPowerSeries (Fin n) E) ∈ maximalIdeal _ ^ 2 := by
  obtain ⟨g, hg⟩ := mem_span_X f hf
  have hc : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (g j) := by
    intro j
    rw [hg, map_sum, Finset.sum_eq_single j]
    · rw [MvPowerSeries.X, coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self,
        coeff_zero_eq_constantCoeff_apply]
    · intro i _ hij
      rw [MvPowerSeries.X, coeff_monomial_mul, if_neg]
      intro h
      have := h i
      simp [Finsupp.single_apply, hij.symm] at this
    · simp
  simp only [hc]
  rw [hg, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [smul_eq_C_mul, mul_comm (C _), ← mul_sub, pow_two]
  exact Ideal.mul_mem_mul ((mem_max _).2 (by simp)) ((mem_max _).2 (by simp))

private theorem inj_of_surj {A : Type} [CommRing A] [IsNoetherianRing A] (s : A →+* A)
    (hs : Function.Surjective s) : Function.Injective s := by
  let K : ℕ →o Ideal A := ⟨fun k => RingHom.ker (s ^ k), monotone_nat_of_le_succ fun k a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha, map_zero]⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A A) K
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hsN : Function.Surjective (s ^ N) := by
    rw [RingHom.coe_pow]; exact hs.iterate N
  obtain ⟨b, rfl⟩ := hsN a
  have h1 : b ∈ K (N + 1) := by
    show (s ^ (N + 1)) b = 0
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha]
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  exact h1

private theorem exists_equiv {E : Type} [Field E] {n : ℕ} (y : Fin n → MvPowerSeries (Fin n) E)
    (hy : ∀ i, constantCoeff (y i) = 0)
    (hsp : Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) = ⊤) :
    ∃ s : MvPowerSeries (Fin n) E ≃ₐ[E] MvPowerSeries (Fin n) E, ∀ i, s (X i) = y i := by
  haveI : IsAdicComplete (maximalIdeal E) E := by
    rw [maximalIdeal_eq_bot]; infer_instance
  haveI := co_mvps E E (Fin n)
  obtain ⟨s, ⟨-, hs⟩, -⟩ := co_ev E E (MvPowerSeries (Fin n) E) (Fin n) (Algebra.ofId E _) y
    fun i => (mem_max _).2 (hy i)
  have hsurj : Function.Surjective s := by
    refine co_surj E _ _ s fun f hf => ?_
    set J := (maximalIdeal (MvPowerSeries (Fin n) E)).map s ⊔ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2
    have hT : ∀ v : Fin n → E, ∑ j, v j • (X j : MvPowerSeries (Fin n) E) ∈ J := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) := by
        rw [hsp]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        have h1 : y i ∈ J := Ideal.mem_sup_left (by
          rw [← hs]; exact Ideal.mem_map_of_mem s ((mem_max _).2 (by simp)))
        have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s) (lin_part (y i) (hy i))
        simpa using J.sub_mem h1 h2
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        exact J.add_mem ha hb
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
        rw [smul_eq_C_mul]
        exact J.mul_mem_left _ ha
    have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s)
      (lin_part f ((mem_max _).1 hf))
    simpa using J.add_mem h2 (hT fun j => coeff (Finsupp.single j 1) f)
  exact ⟨AlgEquiv.ofBijective s ⟨inj_of_surj s.toRingHom hsurj, hsurj⟩, hs⟩

private theorem const_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E)
    (f : MvPowerSeries σ E) : constantCoeff (s f) = constantCoeff f := by
  have h1 : f - algebraMap E _ (constantCoeff f) ∈ maximalIdeal _ :=
    (mem_max _).2 (by simp [MvPowerSeries.algebraMap_apply])
  have h2 : s (f - algebraMap E _ (constantCoeff f)) ∈ maximalIdeal _ := fun h => h1 (by
    simpa using h.map s.symm)
  rw [mem_max, map_sub, AlgEquiv.commutes] at h2
  simpa [MvPowerSeries.algebraMap_apply, sub_eq_zero] using h2

private theorem pow_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E) (N : ℕ)
    {f : MvPowerSeries σ E} (hf : f ∈ maximalIdeal _ ^ N) : s f ∈ maximalIdeal _ ^ N := by
  have h : maximalIdeal (MvPowerSeries σ E) ≤ (maximalIdeal _).comap s := fun a ha => by
    rw [Ideal.mem_comap, mem_max, const_equiv]; exact (mem_max _).1 ha
  exact ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow _ N)) hf

theorem UpperTheory.V.Loc.chartChange :
    ∀ {O R E : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, x (z i) = 0) → Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (z i))) = ⊤ → ∃ φ' : R →ₐ[O] MvPowerSeries (Fin n) E, UpperTheory.V.Loc.IsCompl I x φ' ∧ ∀ i, φ' (z i) = MvPowerSeries.X i := by
  intro O R E _ _ _ _ _ n I x φ z h hz hsp
  obtain ⟨s, hs⟩ := exists_equiv (fun i => φ (z i)) (fun i => by rw [h.const, hz, map_zero]) hsp
  let φ' : R →ₐ[O] MvPowerSeries (Fin n) E := ((s.symm.restrictScalars O).toAlgHom).comp φ
  have hφ : ∀ a, φ' a = s.symm (φ a) := fun _ => rfl
  refine ⟨φ', ⟨?_, fun a => ?_, fun N f => ?_, fun N a ha => ?_⟩, fun i => ?_⟩
  · rw [← h.ker]
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, hφ, map_eq_zero_iff _ s.symm.injective]
  · rw [hφ, const_equiv, h.const]
  · obtain ⟨a, c, hc, hm⟩ := h.dense N (s f)
    refine ⟨a, c, hc, ?_⟩
    have h1 := pow_equiv s.symm N hm
    have h2 : s.symm (c • s f) = c • f := by
      rw [← algebraMap_smul E c, map_smul, AlgEquiv.symm_apply_apply, algebraMap_smul]
    rwa [map_sub, h2] at h1
  · refine h.inj N a ?_
    have h1 := pow_equiv s N ha
    rwa [hφ, AlgEquiv.apply_symm_apply] at h1
  · rw [hφ, ← hs, AlgEquiv.symm_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartGraded
section
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem cg_max {E σ : Type} [Field E] : maximalIdeal (MvPowerSeries σ E) = GlobalTheory.germIdeal σ E := by
  ext g
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  simp [GlobalTheory.germIdeal, RingHom.mem_ker]

private theorem cg_ext {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    [IsFractionRing O E] {n : ℕ} {I : Ideal R} {x : R →ₐ[O] O} {φ : R →ₐ[O] MvPowerSeries (Fin n) E}
    (hφ : UpperTheory.V.Loc.IsCompl I x φ) {z : Fin n → R} (hz : ∀ i, φ (z i) = MvPowerSeries.X i)
    (α β : R →ₐ[O] MvPowerSeries (Fin n) E)
    (hα : ∀ a, MvPowerSeries.constantCoeff (α a) = algebraMap O E (x a))
    (hβ : ∀ a, MvPowerSeries.constantCoeff (β a) = algebraMap O E (x a))
    (hI : ∀ a ∈ I, α a = β a) (hzz : ∀ i, α (z i) = β (z i)) (a : R) : α a = β a := by
  classical
  have hm := cg_max (E := E) (σ := Fin n)
  have hA : ∀ (γ : R →ₐ[O] MvPowerSeries (Fin n) E),
      (∀ a, MvPowerSeries.constantCoeff (γ a) = algebraMap O E (x a)) →
      ∀ N, ∀ b ∈ RingHom.ker x ^ N, γ b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro γ hγ N b hb
    have h1 : Ideal.map γ (RingHom.ker x) ≤ GlobalTheory.germIdeal (Fin n) E := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [hγ, RingHom.mem_ker.mp hc, map_zero]
    have h2 : Ideal.map γ (RingHom.ker x ^ N) ≤ GlobalTheory.germIdeal (Fin n) E ^ N := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' h1 N
    exact h2 (Ideal.mem_map_of_mem γ hb)
  have hB : ∀ N, ∀ b ∈ RingHom.ker x ^ N ⊔ I, α b - β b ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    have hv0 : α v - β v = 0 := sub_eq_zero.mpr (hI v hv)
    rw [map_add, map_add, add_sub_add_comm, hv0, add_zero]
    exact Ideal.sub_mem _ (hA α hα N u hu) (hA β hβ N u hu)
  have hC : ∀ p : MvPolynomial (Fin n) O, α (MvPolynomial.aeval z p) = β (MvPolynomial.aeval z p) := by
    intro p
    have hcomp : α.comp (MvPolynomial.aeval z) = β.comp (MvPolynomial.aeval z) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hzz i]
    exact AlgHom.congr_fun hcomp p
  have hP : ∀ p : MvPolynomial (Fin n) O, φ (MvPolynomial.aeval z p) =
      ((MvPolynomial.map (algebraMap O E) p : MvPolynomial (Fin n) E) : MvPowerSeries (Fin n) E) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.aeval_C, AlgHom.commutes, MvPolynomial.map_C, MvPolynomial.coe_C,
        MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp only [map_add, hp, hq, MvPolynomial.coe_add]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, hz i, MvPolynomial.map_X, MvPolynomial.coe_mul,
        MvPolynomial.coe_X]
  have hmain : ∀ N, ∃ e : O, e ≠ 0 ∧ e • (α a - β a) ∈ GlobalTheory.germIdeal (Fin n) E ^ N := by
    intro N
    set s := (Finsupp.finite_of_degree_lt (σ := Fin n) N).toFinset with hs
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s
      (fun d => MvPowerSeries.coeff d (φ a))
    have hb' : ∀ d ∈ s, ∃ k : O, algebraMap O E k = (b : O) • MvPowerSeries.coeff d (φ a) :=
      fun d hd => RingHom.mem_rangeS.mp (hb d hd)
    choose! k hk using hb'
    set p : MvPolynomial (Fin n) O := ∑ d ∈ s, MvPolynomial.monomial d (k d) with hp
    set y : R := (b : O) • a - MvPolynomial.aeval z p with hy
    have hφy : φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N := by
      rw [hm, GlobalTheory.mem_germIdeal_pow_iff]
      intro d hd
      have hds : d ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        exact hd
      have hcp : MvPolynomial.coeff d p = k d := by
        rw [hp, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_monomial]
        rw [Finset.sum_ite_eq' s d (fun e => k e), if_pos hds]
      rw [hy, map_sub, map_smul, hP, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_map, hcp,
        hk d hds]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc0, hc⟩ := hφ.inj N y hφy
    refine ⟨c * b, mul_ne_zero hc0 (nonZeroDivisors.ne_zero b.2), ?_⟩
    have heq : α (c • y) - β (c • y) = (c * (b : O)) • (α a - β a) := by
      rw [hy]
      simp only [map_smul, map_sub]
      rw [hC p, ← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, mul_smul]
    rw [← heq]
    exact hB N _ hc
  rw [← sub_eq_zero]
  ext d
  obtain ⟨e, he0, he⟩ := hmain (d.degree + 1)
  rw [GlobalTheory.mem_germIdeal_pow_iff] at he
  have h1 := he d (Nat.lt_succ_self _)
  change e • MvPowerSeries.coeff d (α a - β a) = 0 at h1
  rw [Algebra.smul_def, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).mpr he0)
  · rw [map_zero]
    exact h1

theorem UpperTheory.V.Loc.chartGraded :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R) (w : Fin n → ℤ) (θ : R →ₐ[O] R) (t : Oˣ), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, φ (z i) = MvPowerSeries.X i) → x.comp θ = x → (∀ a ∈ I, θ a ∈ I) → (Function.Injective fun j : ℤ => t ^ j) → (∀ i, θ (z i) = algebraMap O R ((t ^ w i : Oˣ) : O) * z i) → ∀ (j : ℤ) (a : R), θ a = algebraMap O R ((t ^ j : Oˣ) : O) * a → φ a ∈ wtPart E w j := by
  intro O R E _ _ _ _ _ _ _ n I x φ z w θ t hφ hz hxθ hθI hinj hθz j a ha
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin n → E, c = fun i => algebraMap O E ((t ^ w i : Oˣ) : O) := ⟨_, rfl⟩
  have hρC : ∀ e : E, MvPowerSeries.rescale c (MvPowerSeries.C e) = MvPowerSeries.C e := by
    intro e
    ext m
    rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
    split_ifs with hm
    · subst hm
      simp
    · simp
  let β : R →ₐ[O] MvPowerSeries (Fin n) E :=
    AlgHom.mk ((MvPowerSeries.rescale c).comp φ.toRingHom) (fun r => by
      show MvPowerSeries.rescale c (φ (algebraMap O R r)) = _
      rw [AlgHom.commutes, MvPowerSeries.algebraMap_apply, hρC])
  have hβ_apply : ∀ r, β r = MvPowerSeries.rescale c (φ r) := fun r => rfl
  have hker : ∀ r ∈ I, φ r = 0 := by
    intro r hr
    rw [← RingHom.mem_ker, hφ.ker]
    exact hr
  have key := cg_ext hφ hz (φ.comp θ) β
    (by
      intro r
      rw [AlgHom.comp_apply, hφ.const, ← AlgHom.comp_apply, hxθ])
    (by
      intro r
      rw [hβ_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
        Finsupp.prod_zero_index, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ.const])
    (by
      intro r hr
      rw [AlgHom.comp_apply, hker _ (hθI r hr), hβ_apply, hker r hr, map_zero])
    (by
      intro i
      rw [AlgHom.comp_apply, hθz i, map_mul, AlgHom.commutes, hz i, hβ_apply, hz i,
        MvPowerSeries.algebraMap_apply]
      ext m
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      split_ifs with hm
      · subst hm
        simp [hc]
      · simp) a
  have hθa : φ (θ a) = MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a := by
    rw [ha, map_mul, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
  have key' : MvPowerSeries.C (algebraMap O E ((t ^ j : Oˣ) : O)) * φ a = MvPowerSeries.rescale c (φ a) := by
    rw [← hθa]
    exact key
  have hprod : ∀ m : Fin n →₀ ℕ,
      (m.prod fun i k => c i ^ k) = algebraMap O E ((t ^ (Finsupp.weight w m) : Oˣ) : O) := by
    intro m
    rw [hc, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    simp only [← map_pow, ← map_prod, ← Units.val_pow_eq_pow_val, ← Units.coe_prod]
    congr 2
    have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → ℤ), t ^ (∑ i ∈ s, f i) = ∏ i ∈ s, t ^ f i := by
      intro s f
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
    rw [hsum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← zpow_natCast, ← zpow_mul, nsmul_eq_mul, mul_comm]
  change ∀ (m : Fin n →₀ ℕ), (Finsupp.weight w) m ≠ j → MvPowerSeries.coeff m (φ a) = 0
  intro m hm
  have hcm := congrArg (MvPowerSeries.coeff m) key'
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_rescale, hprod m, ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at hcm
  rcases hcm with h | h
  · exfalso
    apply hm
    rw [sub_eq_zero] at h
    have h3 : t ^ j = t ^ (Finsupp.weight w m) := Units.ext (IsFractionRing.injective O E h)
    exact (hinj h3).symm
  · exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartSpan
section
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem coeff1_mul {σ E : Type} [CommRing E] (j : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single j 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single j 1) g +
        MvPowerSeries.coeff (Finsupp.single j 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
    Finset.Nat.antidiagonal_succ]
  simp

private theorem exists_den {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ a, ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
  classical
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (RingHom.ker x) : (RingHom.ker x).FG)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) T D
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h0 : D 0 = 0 := by simpa using halg 0
  have key : ∀ a ∈ Submodule.span R (T : Set R), ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨o, ho⟩ := hc a ha
      exact ⟨o, by rw [ho, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp [h0]⟩
    | add a b _ _ ha hb =>
      obtain ⟨o, ho⟩ := ha
      obtain ⟨o', ho'⟩ := hb
      exact ⟨o + o', by rw [map_add, ho, ho', hadd, mul_add]⟩
    | smul r a ha' ha =>
      obtain ⟨o, ho⟩ := ha
      rw [hT] at ha'
      have hx : x a = 0 := ha'
      exact ⟨x r * o, by rw [map_mul, ho, smul_eq_mul, hmul, hx, map_zero]; ring⟩
  intro a
  have hm : a - algebraMap O R (x a) ∈ RingHom.ker x := by
    simp [RingHom.mem_ker]
  rw [← hT] at hm
  obtain ⟨o, ho⟩ := key _ hm
  refine ⟨o, ?_⟩
  have : D a = D (a - algebraMap O R (x a)) := by
    conv_lhs => rw [← sub_add_cancel a (algebraMap O R (x a))]
    rw [hadd, halg, add_zero]
  rw [this, ho]

private def dualHom {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (d : R → O)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = x a * d b + d a * x b)
    (halg : ∀ o, d (algebraMap O R o) = 0) : R →ₐ[O] DualNumber O where
  toFun a := TrivSqZeroExt.inl (x a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have : d 1 = 0 := by simpa using halg 1
    ext <;> simp [this]
  map_mul' a b := by
    ext <;> simp [hmul, mul_comm]
  map_zero' := by
    have : d 0 = 0 := by simpa using halg 0
    ext <;> simp [this]
  map_add' a b := by
    ext <;> simp [hadd]
  commutes' o := by
    ext <;> simp [halg, TrivSqZeroExt.algebraMap_eq_inl]

private theorem der_zero {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) (S : Type) (e : S → R)
    (hsep : ∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f')
    (hs : ∀ s, D (e s) = 0) (a : R) : D a = 0 := by
  obtain ⟨c, hc, h⟩ := exists_den x D hadd hmul halg
  choose d hd using h
  have inj := IsFractionRing.injective O E
  have hc' : algebraMap O E c ≠ 0 := fun h => hc (inj (by rw [h, map_zero]))
  have := hsep
    (dualHom x d (fun a b => inj (by rw [map_add, hd, hd, hd, hadd, mul_add]))
      (fun a b => inj (by rw [map_add, map_mul, map_mul, hd, hd, hd, hmul]; ring))
      (fun o => inj (by rw [hd, halg, mul_zero, map_zero])))
    (dualHom x (fun _ => 0) (by simp) (by simp) (by simp))
    (fun s => by
      have : d (e s) = 0 := inj (by rw [hd, hs, mul_zero, map_zero])
      ext <;> simp [dualHom, this])
  have h3 : d a = 0 := by
    simpa [dualHom] using congrArg TrivSqZeroExt.snd (DFunLike.congr_fun this a)
  have h4 := hd a
  rw [h3, map_zero] at h4
  exact (mul_eq_zero.mp h4.symm).resolve_left hc'

theorem UpperTheory.V.Loc.chartSpan :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (S : Type) (e : S → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f') → ∃ u : Fin n → S, Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (e (u i)))) = ⊤ := by
  intro O R E _ _ _ _ _ _ _ _ n I x φ S e h hsep
  classical
  let L : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E) :=
    LinearMap.pi fun j => MvPowerSeries.coeff (Finsupp.single j 1)
  have hL : ∀ f j, L f j = MvPowerSeries.coeff (Finsupp.single j 1) f := fun _ _ => rfl
  have hLmul : ∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f := by
    intro f g
    funext j
    simp only [hL, coeff1_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, L f = 0 := by
    have hm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E), MvPowerSeries.constantCoeff f = 0 := by
      intro f hf
      by_contra hne
      exact hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (Ne.isUnit hne))
    intro f hf
    rw [pow_two] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [hLmul, hm a ha, hm b hb]; simp
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  have hspan : Submodule.span E (Set.range fun s => L (φ (e s))) = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hD := der_zero x (fun a => lam (L (φ a))) (fun a b => by simp)
      (fun a b => by
        rw [map_mul, hLmul, h.const, h.const]
        simp only [map_add, map_smul, smul_eq_mul]
        ring)
      (fun o => by
        have : L (φ (algebraMap O R o)) = 0 := by
          funext j
          rw [AlgHom.commutes, hL, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp
        rw [this, map_zero])
      S e hsep (fun s => hker (Submodule.subset_span ⟨s, rfl⟩))
    apply hlam
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    obtain ⟨a, c, hc, hca⟩ := h.dense 2 (MvPowerSeries.X j)
    have h1 := hm2 _ hca
    have hX : L (MvPowerSeries.X j) = Pi.basisFun E (Fin n) j := by
      funext i
      rw [hL, MvPowerSeries.coeff_index_single_X]
      simp [Pi.single_apply]
    rw [map_sub, ← algebraMap_smul E c, map_smul, hX, sub_eq_zero] at h1
    have h2 := hD a
    simp only [← h1, map_smul, smul_eq_mul] at h2
    have hc' : algebraMap O E c ≠ 0 := fun h => hc (IsFractionRing.injective O E (by rw [h, map_zero]))
    exact (mul_eq_zero.mp h2).resolve_left hc'
  obtain ⟨b, hb, hbs, hbi⟩ := exists_linearIndependent E (Set.range fun s => L (φ (e s)))
  rw [hspan] at hbs
  have hfin : b.Finite := hbi.set_finite_of_isNoetherian
  haveI := hfin.fintype
  let B : Module.Basis b E (Fin n → E) := Module.Basis.mk hbi (by simp [hbs])
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis B]; simp
  let q : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose u hu using fun i : Fin n => hb (q i).2
  refine ⟨u, ?_⟩
  rw [eq_top_iff, ← hbs]
  refine Submodule.span_mono fun v hv => ⟨q.symm ⟨v, hv⟩, ?_⟩
  have := hu (q.symm ⟨v, hv⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobCyc
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.frobCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ σ : GQ l, IsFrob σ ∧ cyc l l σ = 1 := by
  intro l _
  obtain ⟨-, -, -, ⟨σ, hσ⟩, h⟩ := iqBasic l
  obtain ⟨g, hg, hc⟩ := (cycInertia l).1 (cyc l l σ)⁻¹
  refine ⟨σ * g, (h σ _ hσ).2 ?_, ?_⟩
  · rwa [inv_mul_cancel_left]
  · rw [map_mul, hc, mul_inv_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem UpperTheory.V.Loc.adicCont_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  intro N
  have h1 : IsLocallyConstant (fun g => Units.map (Ideal.Quotient.mk (I ^ N) : R →+* R ⧸ I ^ N).toMonoidHom (Ψ g)) :=
    IsLocallyConstant.desc _ (fun u : (R ⧸ I ^ N)ˣ => (u : R ⧸ I ^ N)) (by simpa [Function.comp_def] using h N)
      (fun a b hab => Units.ext hab)
  have h2 := h1.comp (fun u => ((u ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N))
  convert h2 using 1
  funext g
  simp only [Function.comp_apply, ← map_zpow, Units.coe_map]
  rfl

theorem UpperTheory.V.Loc.univEx :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), ∃! x, IsBase D.η D.Ψ U.r.hom x := by
  intro l _ O _ _ _ _ _ _ _ D U
  have hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((D.Ψ g ^ j : Oˣ) : O) :=
    fun j => adicCont_zpow _ _ D.Ψ_cont j
  obtain ⟨f, hf, hu⟩ := (U.rep O).2 (baseLift O D.η D.Ψ hΨ) trivial
  refine ⟨f, congrArg GLift.hom hf, fun y hy => hu y (GLift.ext hy)⟩
end

