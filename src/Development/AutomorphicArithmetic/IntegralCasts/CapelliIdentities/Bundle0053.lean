import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PbMem
section
namespace UpperTheory.Reformulated.B.Qi43

theorem pb_mem {B C : Type} [Group B] [Group C] (J : B →* C) (UQ : Subgroup C)
    (hc : ∀ u ∈ UQ, ∀ g : B, Commute u (J g)) (K : Subgroup B) (x : C) :
    x ∈ UQ ⊔ Subgroup.map J K ↔ ∃ u ∈ UQ, ∃ k ∈ K, x = u * J k := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨1, UQ.one_mem, k, hk, by simp⟩
    | one => exact ⟨1, UQ.one_mem, 1, K.one_mem, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      obtain ⟨v, hv, l, hl, rfl⟩ := hz
      refine ⟨u * v, UQ.mul_mem hu hv, k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (J k), ← (hc v hv k).eq]
      simp only [mul_assoc]
    | inv y _ hy =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      refine ⟨u⁻¹, UQ.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩
      rw [(hc u hu k).eq, mul_inv_rev, map_inv]
  · rintro ⟨u, hu, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem J hk))

end UpperTheory.Reformulated.B.Qi43
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Per
section
namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulSelf
section
noncomputable def UpperTheory.Reformulated.B.Yzd3.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd3.phi_mul_self :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd3.Phi a R * UpperTheory.Reformulated.B.Yzd3.Phi a R = (-1 : R) ^ (a - (1 : ℕ)) • (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i k
  have hi := i.2
  have hk := k.2
  have hj : a - 1 - (i : ℕ) < a := by omega
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.Yzd3.Phi, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨a - 1 - (i : ℕ), hj⟩ : Fin a)]
  · have h1 : (i : ℕ) + (a - 1 - (i : ℕ)) + 1 = a := by omega
    dsimp only
    rw [if_pos h1]
    by_cases hik : i = k
    · subst hik
      have h2 : (a - 1 - (i : ℕ)) + (i : ℕ) + 1 = a := by omega
      rw [if_pos h2, if_pos rfl, mul_one, ← pow_add]
      congr 1
      omega
    · have h2 : ¬ ((a - 1 - (i : ℕ)) + (k : ℕ) + 1 = a) := by
        intro h
        exact hik (Fin.ext (by omega))
      rw [if_neg h2, if_neg hik, mul_zero, mul_zero]
  · intro j _ hne
    have h1 : ¬ ((i : ℕ) + (j : ℕ) + 1 = a) := by
      intro h
      exact hne (Fin.ext (by simp only []; omega))
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulTranspose
section
noncomputable def UpperTheory.Reformulated.B.Yzd2.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd2.Phi a R * (UpperTheory.Reformulated.B.Yzd2.Phi a R).transpose = (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    have hi := i.isLt
    let k : Fin a := ⟨a - 1 - (i : ℕ), by omega⟩
    have hk : (k : ℕ) = a - 1 - (i : ℕ) := rfl
    rw [Finset.sum_eq_single k]
    · have h1 : (i : ℕ) + (k : ℕ) + 1 = a := by omega
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · intro b _ hb
      have h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a) := by
        intro h2
        apply hb
        ext
        omega
      simp [h1]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : (i : ℕ) + (k : ℕ) + 1 = a
    · have h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a) := by
        intro h2
        apply h
        ext
        omega
      simp [h2]
    · simp [h1]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
section
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X :
    ∀ {O σ : Type} [inst : CommRing O] (s : Finset σ)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ), (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ inst s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a t hat ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
      apply ih
      intro n hn
      rw [hg]
      split_ifs with h
      · apply hf
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hg, if_pos hm, sub_self]
    have h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PinsOfClosedSubgroupPadicCharacterInv
section
noncomputable def UpperTheory.Reformulated.B.Qe19.LiftEquiv :
    Prop :=
    ∀ (Γ X : Type) [inst : Group Γ] [inst_1 : MulAction Γ X],
      (∀ (x : X), Finite ↥(MulAction.stabilizer Γ x)) →
        ∀ (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B),
          Function.Surjective (⇑(Rep.Hom.hom f) : (↑A : Type) → (↑B : Type)) →
            ∀ (φ : X → (↑B : Type)),
              (∀ (g : Γ) (x : X),
                  φ (g • x) = ((B.ρ : Γ → (↑B : Type) →ₗ[ℂ] (↑B : Type)) g : (↑B : Type) → (↑B : Type)) (φ x)) →
                ∃ (ψ : X → (↑A : Type)),
                  (∀ (g : Γ) (x : X),
                      ψ (g • x) = ((A.ρ : Γ → (↑A : Type) →ₗ[ℂ] (↑A : Type)) g : (↑A : Type) → (↑A : Type)) (ψ x)) ∧
                    ∀ (x : X), (Rep.Hom.hom f : (↑A : Type) → (↑B : Type)) (ψ x) = φ x

private theorem UpperTheory.Reformulated.B.Qe19.fixed_lift {Γ : Type} [Group Γ] (H : Subgroup Γ) [Finite H]
    (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B) (hf : Function.Surjective (Rep.Hom.hom f))
    (b : B) (hb : ∀ h ∈ H, B.ρ h b = b) :
    ∃ a : A, (∀ h ∈ H, A.ρ h a = a) ∧ (Rep.Hom.hom f) a = b := by
  classical
  haveI := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hf b
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ k : H, A.ρ k a, ?_, ?_⟩
  · intro h hh
    rw [map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ ?_
    intro k
    simp [map_mul]
  · rw [map_smul, map_sum]
    have h1 : ∀ k : H, (Rep.Hom.hom f) (A.ρ k a) = b := by
      intro k
      rw [Rep.hom_comm_apply, ha, hb k k.2]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.Reformulated.B.Qe19.LiftEquiv := by
  intro Γ X _ _ hfin A B f hf φ hφ
  have h1 : ∀ x : X, ∃ a : A, (∀ h ∈ MulAction.stabilizer Γ x, A.ρ h a = a) ∧
      (Rep.Hom.hom f) a = φ x := by
    intro x
    haveI := hfin x
    refine UpperTheory.Reformulated.B.Qe19.fixed_lift _ A B f hf (φ x) ?_
    intro h hh
    rw [← hφ, MulAction.mem_stabilizer_iff.mp hh]
  choose a ha hfa using h1
  have h2 : ∃ r : X → X, (∀ (g : Γ) (x : X), r (g • x) = r x) ∧ ∀ x, ∃ g : Γ, g • r x = x := by
    refine ⟨fun x => (Quotient.mk (MulAction.orbitRel Γ X) x).out, ?_, ?_⟩
    · intro g x
      have : Quotient.mk (MulAction.orbitRel Γ X) (g • x) = Quotient.mk (MulAction.orbitRel Γ X) x :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g))
      simp only [this]
    · intro x
      have h := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ X) x)).symm
      exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  obtain ⟨r, hr, hg⟩ := h2
  choose s hs using hg
  refine ⟨fun x => A.ρ (s x) (a (r x)), ?_, ?_⟩
  · intro g x
    have hm : (s (g • x))⁻¹ * (g * s x) ∈ MulAction.stabilizer Γ (r x) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hs x, inv_smul_eq_iff, ← hr g x, hs]
    have h3 := congrArg (A.ρ (s (g • x))) (ha (r x) _ hm)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    simp only [hr g x]
    exact h3.symm
  · intro x
    show (Rep.Hom.hom f) (A.ρ (s x) (a (r x))) = φ x
    rw [Rep.hom_comm_apply, hfa, ← hφ, hs]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlacewiseToOutsideS
section
noncomputable def UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

noncomputable def UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] → (ι → Module.End k E) → (Finset ι → E) →ₗ[k] Finset ι → E :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (w : ι → Module.End k E) ↦
      LinearMap.pi fun (t : Finset ι) ↦ ∑ i ∈ t, UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i • w i ∘ₗ LinearMap.proj (t.erase i)

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt {ι : Type} [LinearOrder ι] (t : Finset ι) (i j : ι)
    (hi : i ∈ t) (hij : i < j) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j =
      -(UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t j * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase j) i) := by
  have h1 : (t.erase j).filter (fun x => x < i) = t.filter (fun x => x < i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨(h'.trans hij).ne, h⟩, h'⟩
  have h2 : (t.filter (fun x => x < j)).card = ((t.erase i).filter (fun x => x < j)).card + 1 := by
    rw [Finset.filter_erase, Finset.card_erase_add_one]
    exact Finset.mem_filter.2 ⟨hi, hij⟩
  simp only [UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign]
  rw [h1, h2, pow_succ]
  ring

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_ne {ι : Type} [LinearOrder ι] (t : Finset ι) (i j : ι)
    (hi : i ∈ t) (hj : j ∈ t) (hij : i ≠ j) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j =
      -(UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t j * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt t i j hi h
  · rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt t j i hj h, neg_neg]

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply {σ E : Type} [LinearOrder σ] [AddCommGroup E]
    [_root_.Module ℂ E] (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w c t = ∑ i ∈ t, UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i • w i (c (t.erase i)) := by
  simp [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd, LinearMap.sum_apply]

theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_wd :
    ∀ {σ E : Type} [inst : LinearOrder σ] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module ℂ E] (w : σ → Module.End ℂ E),
      (∀ (i j : σ), Commute (w i) (w j)) →
        ∀ (c : Finset σ → E),
          (UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w : (Finset σ → E) → Finset σ → E) ((UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w : (Finset σ → E) → Finset σ → E) c) =
            (0 : Finset σ → E) := by
  intro σ E _ _ _ w hw c
  funext t
  rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply, Pi.zero_apply]
  simp only [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  set f : σ → σ → E := fun i j =>
    (UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j) •
      w i (w j (c ((t.erase i).erase j))) with hf
  change ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = 0
  have hanti : ∀ i ∈ t, ∀ j ∈ t.erase i, f j i = - f i j := by
    intro i hi j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [hf]
    rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_ne t j i hj hi hne, neg_smul, Finset.erase_right_comm,
      ← Module.End.mul_apply, (hw j i).eq, Module.End.mul_apply]
  have hswap : ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ j ∈ t, ∑ i ∈ t.erase j, f i j := by
    apply Finset.sum_comm'
    intro x y
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2.symm, h1⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, h1.symm, h3⟩
  have hneg : ∑ j ∈ t, ∑ i ∈ t.erase j, f i j = -∑ i ∈ t, ∑ j ∈ t.erase i, f i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hanti i hi j hj
  have h2 : (2 : ℂ) • ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 (hswap.trans hneg)
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Plc
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe49.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.Qe49.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [NumberField E] (w : UpperTheory.Reformulated.B.Qe49.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal),
    CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PointFinitePower
section
theorem UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow :
    ∀ {O S : Type} [inst : CommRing O] [inst_1 : CommRing S]
    [inst_2 : Algebra O S] [IsNoetherianRing S] (m : Ideal S),
    (∀ (x : S), ∃ (a : O), x - (Algebra.algebraMap O S : O → S) a ∈ m) →
      ∀ (n : ℕ), ∃ (N : Submodule O S), N.FG ∧ ∀ (x : S), ∃ y ∈ N, x - y ∈ m ^ n := by
  intro O S _ _ _ _ m hm n
  induction n with
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z : S, z ∈ Submodule.span S (s : Set S) →
        ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        exact ⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | zero =>
        exact ⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | add z z' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
        have e : z + z' - (w + w') = (z - w) + (z' - w') := by ring
        rw [e]
        exact Submodule.add_mem _ h h'
      | smul c z hz h =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨a, ha⟩ := hm c
        refine ⟨a • w, Submodule.smul_mem _ a hw, ?_⟩
        have hz' : z ∈ m ^ n := by
          rw [← hs]
          exact hz
        have e : c • z - a • w
            = algebraMap O S a * (z - w) + z * (c - algebraMap O S a) := by
          rw [Algebra.smul_def a w, smul_eq_mul]
          ring
        rw [e]
        refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' ha
    refine ⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, h⟩ := key (x - y) hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rw [← sub_sub]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PolyInMul
section
noncomputable def UpperTheory.Reformulated.B.Qk18.PolyIn :
    {R : Type} → [inst : Ring R] → [Algebra ℂ R] → (ℂ → R) → ℕ → Prop :=
    fun {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ) ↦
      ∃ (a : ℕ → R), ∀ (s : ℂ), f s = ∑ k ∈ Finset.range (d + (1 : ℕ)), s ^ k • a k

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowCong
section
theorem UpperTheory.Reformulated.B.Qh11.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowEig
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp8.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp8.pow_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp8.Mat C N) (l : C) (w : Fin N → C),
      Matrix.mulVec y w = l • w → ∀ (m : ℕ), Matrix.mulVec (y ^ m) w = l ^ m • w := by
  intro C _ N y l w h m
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
end

