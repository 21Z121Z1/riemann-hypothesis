import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add, h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add, h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem homog_of_span {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) :
    IsHomog O wt (Ideal.span S) := by
  intro f hf j
  have key : ∀ b : MvPowerSeries σ O, ∀ j, wcomp O wt j (b * f) ∈ Ideal.span S := by
    induction hf using Submodule.span_induction with
    | mem a ha =>
      intro b j
      obtain ⟨c, hc⟩ := hS a ha
      rw [wcomp_mul_homog wt hc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ha)
    | zero => intro b j; simp
    | add x y _ _ hx hy =>
      intro b j
      rw [mul_add, map_add]
      exact add_mem (hx b j) (hy b j)
    | smul r x _ hx =>
      intro b j
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _ j
  simpa using key 1 j

private theorem homog_span_pow {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) (N : ℕ) :
    IsHomog O wt (Ideal.span S ^ N) := by
  have key : ∃ T : Set (MvPowerSeries σ O), (∀ a ∈ T, ∃ c, a ∈ wtPart O wt c) ∧
      Ideal.span S ^ N = Ideal.span T := by
    induction N with
    | zero =>
      refine ⟨{1}, ?_, by simp⟩
      rintro a rfl
      exact ⟨0, one_mem_wtPart O wt⟩
    | succ n ih =>
      obtain ⟨T, hT, hT'⟩ := ih
      refine ⟨_, ?_, by rw [pow_succ, hT', Ideal.span_mul_span']⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hT a ha
      obtain ⟨d, hd⟩ := hS b hb
      exact ⟨c + d, mul_mem_wtPart O wt hc hd⟩
  obtain ⟨T, hT, hT'⟩ := key
  rw [hT']
  exact homog_of_span wt T hT

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

theorem UpperTheory.V.Alg.part_closed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (x : R), (∀ N : ℕ, ∃ y ∈ W.part j, x - y ∈ maximalIdeal R ^ N) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ hR W hz j x hx
  classical
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  let S : Set (MvPowerSeries W.σ O) :=
    Set.range MvPowerSeries.X ∪ algebraMap O _ '' (maximalIdeal O : Set O)
  have hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O W.wt c := by
    rintro _ (⟨i, rfl⟩ | ⟨a, -, rfl⟩)
    · exact ⟨_, X_mem_wtPart O W.wt i⟩
    · refine ⟨0, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart O W.wt)
  have hle : (Ideal.span S).map W.π ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact hz i
    · show W.π (algebraMap O _ a) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact fun h => ha (IsLocalHom.map_nonunit a h)
  have hmap : (Ideal.span S).map W.π = maximalIdeal R := by
    refine le_antisymm hle fun r hr => ?_
    obtain ⟨f, rfl⟩ := W.surj r
    have h1 : f - algebraMap O _ (constantCoeff f) ∈ Ideal.span S := by
      refine Ideal.span_mono Set.subset_union_left (mem_span_X _ ?_)
      simp [MvPowerSeries.algebraMap_apply]
    have h2 : constantCoeff f ∈ maximalIdeal O := fun hu =>
      hr ((MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map W.π)
    have h3 : algebraMap O _ (constantCoeff f) ∈ Ideal.span S :=
      Ideal.subset_span (Or.inr ⟨_, h2, rfl⟩)
    exact Ideal.mem_map_of_mem _ (by simpa using add_mem h1 h3)
  obtain ⟨f, rfl⟩ := W.surj x
  have key : ∀ N : ℕ, W.π (f - wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
    intro N
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx N
    rw [← hmap, ← Ideal.map_pow] at hxy ⊢
    obtain ⟨g, hg, hgxy⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hxy
    have h1 : f - y - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, map_sub, hgxy]
      exact sub_self _
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j y = y := by
      ext n
      rw [coeff_wcomp]
      split_ifs with h
      · rfl
      · exact (hy n h).symm
    have h4 : g - wcomp O W.wt j g ∈ Ideal.span S ^ N :=
      sub_mem hg (homog_span_pow W.wt S hS N g hg j)
    have h5 : f - wcomp O W.wt j f =
        (f - y - g) - wcomp O W.wt j (f - y - g) + (g - wcomp O W.wt j g) := by
      rw [map_sub, map_sub, h3]; ring
    rw [h5, map_add, (RingHom.mem_ker).1 (sub_mem h1 h2), zero_add]
    exact Ideal.mem_map_of_mem _ h4
  have h0 : W.π (f - wcomp O W.wt j f) = 0 := by
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
    exact key
  rw [map_sub, sub_eq_zero] at h0
  exact ⟨_, wcomp_mem O W.wt j f, h0.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private noncomputable def tchU (n : ℕ) (O : Type) [CommRing O] (i : Fin n) : (MvPowerSeries (Fin n) O)ˣ :=
  (show IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) O) from
    MvPowerSeries.isUnit_iff_constantCoeff.2 (by simp)).unit

private lemma tchU_val (n : ℕ) (O : Type) [CommRing O] (i : Fin n) :
    (tchU n O i : MvPowerSeries (Fin n) O) = 1 + MvPowerSeries.X i := IsUnit.unit_spec _

private lemma tch_poly (n : ℕ) (R : Type) [CommRing R] {X : Type} (s : Finset X) (x : X → R)
    (e : X → Fin n →₀ ℕ) (he : Set.InjOn e s)
    (h : ∑ j ∈ s, (∏ i, (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) R) ^ (e j i)) * C (x j) = 0) :
    ∀ j ∈ s, x j = 0 := by
  classical
  have h1 : (∑ j ∈ s, (∏ i, (1 + MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (e j i)) *
      MvPolynomial.C (x j)) = 0 := by
    apply MvPolynomial.coe_injective (Fin n) R
    rw [MvPolynomial.coe_zero, ← h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_prod]
    simp
  have h2 := congrArg (MvPolynomial.aeval (R := R)
    (fun i : Fin n => (MvPolynomial.X i - 1 : MvPolynomial (Fin n) R))) h1
  rw [map_sum, map_zero] at h2
  have h3 : ∑ j ∈ s, MvPolynomial.monomial (e j) (x j) = 0 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp [map_prod, mul_comm]
  intro j hj
  have h4 := congrArg (MvPolynomial.coeff (e j)) h3
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j] at h4
  · simpa using h4
  · intro k hk hkj
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hh
    exact hkj (he hk hj hh)
  · intro h; exact absurd hj h

theorem UpperTheory.V.Alg.tchar :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (n : ℕ) (t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ), (∀ j, constantCoeff (t j : MvPowerSeries (Fin n) O) = 1) ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (s : Finset X) (x : X → R),
        ∑ j ∈ s, MvPowerSeries.map (algebraMap O R) (t (Multiplicative.ofAdd j) : MvPowerSeries (Fin n) O) * C (x j) = 0 → ∀ j ∈ s, x j = 0 := by
  intro O _ _ X _ _ _
  classical
  let n := Module.finrank ℤ X
  let b : Module.Basis (Fin n) ℤ X := Module.finBasis ℤ X
  let t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ :=
    { toFun := fun j => ∏ i, tchU n O i ^ (b.repr j.toAdd i)
      map_one' := by simp
      map_mul' := by
        intro a c
        simp [zpow_add, Finset.prod_mul_distrib] }
  have ht : ∀ j : X, t (Multiplicative.ofAdd j) = ∏ i, tchU n O i ^ (b.repr j i) := fun j => rfl
  refine ⟨n, t, ?_, ?_⟩
  · intro j
    have h1 : ∀ i, Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (tchU n O i) = 1 := by
      intro i
      ext
      simp [tchU_val]
    have h2 : Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (t j) = 1 := by
      have := ht j.toAdd
      rw [ofAdd_toAdd] at this
      rw [this, map_prod]
      simp only [map_zpow, h1, one_zpow, Finset.prod_const_one]
    simpa using congrArg Units.val h2
  · intro R _ _ s x h
    let N : ℕ := ∑ j ∈ s, ∑ i, (b.repr j i).natAbs
    have hN : ∀ j ∈ s, ∀ i, 0 ≤ b.repr j i + N := by
      intro j hj i
      have h1 : (b.repr j i).natAbs ≤ ∑ i, (b.repr j i).natAbs :=
        Finset.single_le_sum (f := fun i => (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : ∑ i, (b.repr j i).natAbs ≤ N :=
        Finset.single_le_sum (f := fun j => ∑ i, (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) hj
      omega
    let e : X → Fin n →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm fun i => (b.repr j i + N).toNat
    have he : ∀ j i, e j i = (b.repr j i + N).toNat := fun j i => rfl
    refine tch_poly n R s x e ?_ ?_
    · intro j hj k hk hjk
      apply b.repr.injective
      ext i
      have h1 := he j i
      rw [hjk, he] at h1
      have := hN j hj i
      have := hN k hk i
      omega
    · have h1 := congrArg (fun y => MvPowerSeries.map (algebraMap O R)
        ((∏ i, tchU n O i ^ (N : ℤ) : (MvPowerSeries (Fin n) O)ˣ) : MvPowerSeries (Fin n) O) * y) h
      simp only [mul_zero] at h1
      rw [Finset.mul_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, ht, ← Finset.prod_mul_distrib]
      congr 1
      have h2 : ∀ i, tchU n O i ^ (N : ℤ) * tchU n O i ^ (b.repr j i) = tchU n O i ^ (e j i) := by
        intro i
        rw [← zpow_add, ← zpow_natCast, he, Int.toNat_of_nonneg (hN j hj i), add_comm]
      simp only [h2]
      simp [map_prod, tchU_val]
end

