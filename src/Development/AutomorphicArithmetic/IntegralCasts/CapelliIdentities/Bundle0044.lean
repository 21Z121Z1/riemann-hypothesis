import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LayerApproximation
section
private theorem UpperTheory.Reformulated.B.LayerApproximation.first_layer {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ (2 : ℕ)) :
    ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2 := by
  have hspan : ∀ y ∈ Ideal.span T, ∃ a ∈ A, a ∈ m ∧ y - a ∈ m ^ 2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨t, (hT t ht).1, (hT t ht).2, by simp⟩
    | zero => exact ⟨0, A.zero_mem, m.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨b, hb, hbm, hvb⟩ := hv
      refine ⟨a + b, A.add_mem ha hb, m.add_mem ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb
    | smul r u _ hu =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨c, hc⟩ := h0 r
      refine ⟨algebraMap O R c * a, A.mul_mem (A.algebraMap_mem c) ha,
        m.mul_mem_left _ ham, ?_⟩
      have e : r • u - algebraMap O R c * a = r * (u - a) + (r - algebraMap O R c) * a := by
        rw [smul_eq_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hc ham
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hm hx)
  obtain ⟨a, ha, ham, hya⟩ := hspan y hy
  refine ⟨a, ha, ham, ?_⟩
  have e : y + z - a = (y - a) + z := by ring
  rw [e]
  exact Ideal.add_mem _ hya hz

private theorem UpperTheory.Reformulated.B.LayerApproximation.all_layers {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (h1 : ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2) (N : ℕ) :
    ∀ x ∈ m ^ N, ∃ a ∈ A, a ∈ m ^ N ∧ x - a ∈ m ^ (N + 1) := by
  induction N with
  | zero =>
    intro x _
    obtain ⟨c, hc⟩ := h0 x
    exact ⟨algebraMap O R c, A.algebraMap_mem c, by simp, by simpa using hc⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨a, ha, ham, hya⟩ := ih y hy
      obtain ⟨b, hb, hbm, hzb⟩ := h1 z hz
      refine ⟨a * b, A.mul_mem ha hb, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have e : y * z - a * b = y * (z - b) + (y - a) * b := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show N + 1 + 1 = N + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hy hzb
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hya hbm
    · rintro u v ⟨a, ha, ham, hua⟩ ⟨b, hb, hbm, hvb⟩
      refine ⟨a + b, A.add_mem ha hb, Ideal.add_mem _ ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb

theorem UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : CommRing R]
    [inst_2 : Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R),
    (∀ (x : R), ∃ (a : O), x - (Algebra.algebraMap O R : O → R) a ∈ m) →
      (∀ t ∈ T, t ∈ A ∧ t ∈ m) → m ≤ Ideal.span T ⊔ m ^ (2 : ℕ) → ∀ (N : ℕ) (x : R), ∃ a ∈ A, x - a ∈ m ^ N := by
  intro O R _ _ _ m A T h0 hT hm N x
  have h1 := UpperTheory.Reformulated.B.LayerApproximation.first_layer m A T h0 hT hm
  induction N with
  | zero => exact ⟨0, A.zero_mem, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    obtain ⟨b, hb, -, hab⟩ := UpperTheory.Reformulated.B.LayerApproximation.all_layers m A h0 h1 N _ hxa
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have e : x - (a + b) = x - a - b := by ring
    rw [e]
    exact hab
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeSpanSingletonOfForallMemEq
section
theorem UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π ξ : R} [IsAdicComplete (Ideal.span {π}) R] {J : Ideal R},
      (∀ x ∈ J, ∃ (a : R), ∃ z ∈ J, x = a * ξ + z * π) → J ≤ Ideal.span {ξ} := by
  intro R _ π ξ hc J h x hx
  choose! a z hz he using h
  have hsm : ∀ (n : ℕ) (u v : R),
      u ≡ v [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule R R)] ↔ π ^ n ∣ u - v := by
    intro n u v
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
      Ideal.mem_span_singleton]
  have hzs : ∀ n : ℕ, z^[n] x ∈ J := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [Function.iterate_succ_apply']; exact hz _ ih
  let f : ℕ → R := fun n => ∑ i ∈ Finset.range n, a (z^[i] x) * π ^ i
  have hf : ∀ n, f (n + 1) = f n + a (z^[n] x) * π ^ n := fun n => Finset.sum_range_succ _ _
  have key : ∀ n, x = f n * ξ + z^[n] x * π ^ n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hf]
      have h1 := he _ (hzs n)
      linear_combination ih + π ^ n * h1
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {π}) ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hf, ← sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow π hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcau
  have h0 : x - L * ξ = 0 := by
    apply IsHausdorff.haus hc.toIsHausdorff
    intro n
    rw [hsm]
    obtain ⟨c, hc'⟩ := (hsm _ _ _).1 (hL n)
    exact ⟨c * ξ + z^[n] x, by linear_combination key n + ξ * hc'⟩
  exact Ideal.mem_span_singleton'.2 ⟨L, (sub_eq_zero.1 h0).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LidxFinite
section
theorem UpperTheory.Reformulated.B.Yzb2.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
    simp only [smul_add, smul_smul, mul_comm]
  rw [e]
  exact L.add_mem (L.smul_mem _ hx) (L.smul_mem _ hy)

theorem UpperTheory.Reformulated.B.Yzb2.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Yzb2.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem _ hx

noncomputable def UpperTheory.Reformulated.B.Yzb2.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Yzb2.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Yzb2.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Yzb2.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Yzb2.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Yzb2.locS p.primeCompl L

noncomputable def UpperTheory.Reformulated.B.Yzb2.locLen.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℕ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (Module.length R
          (↥(UpperTheory.Reformulated.B.Yzb2.localization₂ p A) ⧸
            Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p B))).toNat

noncomputable def UpperTheory.Reformulated.B.Yzb2.lidx.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℤ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (↑(UpperTheory.Reformulated.B.Yzb2.locLen p A (A ⊓ B)) : ℤ) - (↑(UpperTheory.Reformulated.B.Yzb2.locLen p B (A ⊓ B)) : ℤ)

private theorem UpperTheory.Reformulated.B.Yzb2.common_mul {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V]
    [_root_.Module R V] (B : Submodule R V) (T : Finset V)
    (h : ∀ x ∈ T, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ Submodule.span R (T : Set V), s • x ∈ B := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | insert a T _ ih =>
    obtain ⟨t, ht, htT⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    obtain ⟨s, hs, hsa⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨s * t, mul_ne_zero hs ht, fun x hx => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
    obtain ⟨c, z, hz, rfl⟩ := hx
    have e : (s * t) • (c • a + z) = (t * c) • (s • a) + s • (t • z) := by
      simp only [smul_add, smul_smul]
      congr 2
      ring
    rw [e]
    exact B.add_mem (B.smul_mem _ hsa) (B.smul_mem _ (htT z hz))

private theorem UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (X Y : Submodule R V) (u : R) (hu : u ∉ p)
    (h : ∀ x ∈ X, u • x ∈ Y) : UpperTheory.Reformulated.B.Yzb2.locLen p X Y = 0 := by
  have top : Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p X).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p Y) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, v, hv, hy⟩ -
    refine ⟨u * v, p.primeCompl.mul_mem hu hv, ?_⟩
    rw [mul_smul]
    exact h _ hy
  have : Subsingleton (↥(UpperTheory.Reformulated.B.Yzb2.localization₂ p X) ⧸
      Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p X).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p Y)) :=
    Submodule.Quotient.subsingleton_iff.mpr top
  simp only [UpperTheory.Reformulated.B.Yzb2.locLen, Module.length_eq_zero, ENat.toNat_zero]

theorem UpperTheory.Reformulated.B.Yzb2.lidx_finite :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module (NumberField.RingOfIntegers K) V] (A B : Submodule (NumberField.RingOfIntegers K) V),
      A.FG →
        B.FG →
          (∀ x ∈ A, ∃ (s : NumberField.RingOfIntegers K), s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ B) →
            (∀ x ∈ B, ∃ (s : NumberField.RingOfIntegers K), s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ A) →
              {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
                  UpperTheory.Reformulated.B.Yzb2.lidx w.asIdeal A B ≠ (0 : ℤ)}.Finite := by
  intro K V _ _ _ _ A B hA hB hAB hBA
  obtain ⟨TA, rfl⟩ := id hA
  obtain ⟨TB, rfl⟩ := id hB
  obtain ⟨s, hs, hsA⟩ := UpperTheory.Reformulated.B.Yzb2.common_mul _ TA
    (fun x hx => hAB x (Submodule.subset_span hx))
  obtain ⟨t, ht, htB⟩ := UpperTheory.Reformulated.B.Yzb2.common_mul _ TB
    (fun x hx => hBA x (Submodule.subset_span hx))
  have hst : Ideal.span {s * t} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hs ht
  refine (Ideal.finite_factors hst).subset fun w hw => ?_
  rw [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hw
  have hsw : s ∉ w.asIdeal := fun h => hmem (Ideal.mul_mem_right _ _ h)
  have htw : t ∉ w.asIdeal := fun h => hmem (Ideal.mul_mem_left _ _ h)
  have h1 := UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero w.asIdeal _ (Submodule.span _ (TA : Set V) ⊓ Submodule.span _ (TB : Set V)) s hsw
    (fun x hx => ⟨Submodule.smul_mem _ _ hx, hsA x hx⟩)
  have h2 := UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero w.asIdeal _ (Submodule.span _ (TA : Set V) ⊓ Submodule.span _ (TB : Set V)) t htw
    (fun x hx => ⟨htB x hx, Submodule.smul_mem _ _ hx⟩)
  simp only [UpperTheory.Reformulated.B.Yzb2.lidx, h1, h2, Nat.cast_zero, sub_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftErrorLocal
section
noncomputable def UpperTheory.Reformulated.B.LiftErrorLocal.ShellInt :
    Prop :=
    ∀ (X : Type) [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X) (N : X → ℝ) (C d A : ℝ),
      Measurable N →
        (∀ᵐ (x : X) ∂μ, (1 : ℝ) ≤ N x) →
          (0 : ℝ) ≤ d →
            (∀ (R : ℝ), (1 : ℝ) ≤ R → (μ : Set X → ENNReal) {x : X | N x ≤ R} ≤ ENNReal.ofReal (C * R ^ d)) →
              d < A → ∫⁻ (x : X), ENNReal.ofReal (N x ^ (-A)) ∂μ < ⊤

theorem UpperTheory.Reformulated.B.LiftErrorLocal.shell_int :
    UpperTheory.Reformulated.B.LiftErrorLocal.ShellInt := by
  intro X _ μ N C d A hN h1 hd hμ hA
  have hA0 : -A ≤ 0 := by linarith
  have hmeas : ∀ k : ℕ, MeasurableSet {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := fun k =>
    measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤
      ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem (show x ∈ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} from hk2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hk1 hA0)
  have hr : (2 : ℝ) ^ (d - A) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (d - A) := by positivity
  have hsum : Summable fun k : ℕ => C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-A) * (C * ((2 : ℝ) ^ (k + 1)) ^ d) =
      C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k := by
    intro k
    have h2 : (0 : ℝ) < 2 := two_pos
    have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [pow_succ, Real.mul_rpow hk.le h2.le, Real.rpow_pow_comm h2.le, sub_eq_add_neg,
      Real.rpow_add hk]
    ring
  calc ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x ∂μ :=
        MeasureTheory.lintegral_mono_ae hpt
    _ = ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A)) *
        μ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := by
        rw [MeasureTheory.lintegral_tsum
          (fun k => (measurable_const.indicator (hmeas k)).aemeasurable)]
        exact tsum_congr fun k => MeasureTheory.lintegral_indicator_const (hmeas k) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← hterm k, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hμ _ (one_le_pow₀ one_le_two)
    _ < ⊤ := hsum.tsum_ofReal_lt_top
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftMap
section
theorem UpperTheory.Reformulated.B.Qk56.lift_map :
    ∀ {α β : Type} (f : α → β) (B : Multiset α)
    (t : Multiset β), (∀ x ∈ t, x ∈ Multiset.map f B) → ∃ (t' : Multiset α), Multiset.map f t' = t ∧ ∀ x ∈ t', x ∈ B := by
  intro α β f B t
  induction t using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, Multiset.map_zero f, fun x hx => absurd hx (Multiset.notMem_zero x)⟩
  | cons b s ih =>
    intro h
    obtain ⟨s', hs', hB⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    obtain ⟨a, ha, hab⟩ := Multiset.mem_map.1 (h b (Multiset.mem_cons_self b s))
    refine ⟨a ::ₘ s', by rw [Multiset.map_cons, hab, hs'], fun x hx => ?_⟩
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hB x hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LimitOfFinite
section
theorem UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite.{u_1, u_2}
    {A : Type u_1} {M : Type u_2} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m : ℕ, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L : M, ∀ m : ℕ, f m - L ∈ (I ^ m • ⊤ : Submodule A M) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have key : ∀ (J : Ideal A) (x : M), x ∈ (J • ⊤ : Submodule A M) →
      ∃ d : Fin n → A, (∀ i, d i ∈ J) ∧ ∑ i, d i • s i = x := by
    intro J x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      have hy : y ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
      refine ⟨fun i => r * c i, fun i => J.mul_mem_right _ hr, ?_⟩
      rw [← hc, Finset.smul_sum]
      simp [mul_smul]
    · rintro x y ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩
      refine ⟨fun i => d i + e i, fun i => J.add_mem (hd i) (he i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
  choose d hd hdf using fun m => key (I ^ m) _ (hf m)
  let g : ℕ → Fin n → A := fun m i => ∑ k ∈ Finset.range m, d k i
  have hg : ∀ m, f m = f 0 - ∑ i, g m i • s i := by
    intro m
    induction m with
    | zero => simp [g]
    | succ m ih =>
      have h1 : ∑ i, g (m + 1) i • s i = ∑ i, g m i • s i + ∑ i, d m i • s i := by
        simp [g, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      rw [h1, hdf m, ← sub_sub, ← ih]
      abel
  have hc : ∀ i, ∀ m k, m ≤ k → g m i - g k i ∈ I ^ m := by
    intro i m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      have h1 : g m i - g (k + 1) i = g m i - g k i - d k i := by
        simp only [g, Finset.sum_range_succ]; ring
      rw [h1]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmk (hd k i))
  have hl : ∀ i, ∃ a : A, ∀ m, g m i - a ∈ I ^ m := by
    intro i
    obtain ⟨a, ha⟩ := hI.prec (f := fun m => g m i) (by
      intro m k hmk
      rw [SModEq.sub_mem]
      simpa using hc i m k hmk)
    refine ⟨a, fun m => ?_⟩
    have := ha m
    rw [SModEq.sub_mem] at this
    simpa using this
  choose a ha using hl
  refine ⟨f 0 - ∑ i, a i • s i, fun m => ?_⟩
  have h2 : f m - (f 0 - ∑ i, a i • s i) = -∑ i, (g m i - a i) • s i := by
    rw [hg m]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [h2]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (ha i m) Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinBound
section
theorem UpperTheory.Reformulated.B.Qj19.lin_bound.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by
  intro ι _ _ L
  refine ⟨∑ i, ∑ j, ‖L (Matrix.single i j 1)‖, by positivity, fun B C hB => ?_⟩
  have h : L B = ∑ i, ∑ j, B i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LinPart
section
noncomputable def UpperTheory.Reformulated.B.ComplexLinearPart.linPart :
    {a b : ℕ} → ((Fin a → ℂ) →ₗ[ℝ] Fin b → ℂ) → (Fin a → ℂ) →ₗ[ℂ] Fin b → ℂ :=
  fun {a b} T =>
    { toFun := fun v => (1 / 2 : ℂ) • (T v - Complex.I • T (Complex.I • v))
      map_add' := fun v w => by
        simp only [smul_add, map_add]
        module
      map_smul' := fun c v => by
        have hc : ∀ {n : ℕ} (x : Fin n → ℂ), c • x = c.re • x + c.im • (Complex.I • x) := by
          intro n x
          ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
          rw [← mul_assoc, ← add_mul, Complex.re_add_im]
        have hI : Complex.I • Complex.I • v = -v := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        have h1 : T (c • v) = c.re • T v + c.im • T (Complex.I • v) := by
          rw [hc v, T.map_add, T.map_smul, T.map_smul]
        have h2 : T (Complex.I • c • v) = c.re • T (Complex.I • v) - c.im • T v := by
          rw [smul_comm Complex.I c v, hc (Complex.I • v), hI, T.map_add, T.map_smul, T.map_smul,
            map_neg, smul_neg, sub_eq_add_neg]
        rw [h1, h2, RingHom.id_apply]
        ext j
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        linear_combination (1 / 2 : ℂ) * c.im * T (Complex.I • v) j * Complex.I_mul_I }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ListEig
section
theorem UpperTheory.Reformulated.B.Qk12.list_eig :
    ∀ {M ι : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι),
    (∀ i ∈ l, (L i : M → M) x = c i • x) → ((List.map L l).prod : M → M) x = (List.map c l).prod • x := by
  intro M ι _ _ L c x l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have h1 : L a x = c a • x := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, h2,
      map_smul, h1, smul_smul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocConstOfKer
section
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) := by
  intro G M _ _ _ _ χ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : χ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSumLt
section
theorem UpperTheory.Reformulated.B.Qe17.norm_sum_lt :
    ∀ {F ι : Type} [inst : NormedField F] [IsUltrametricDist F]
    (s : Finset ι) (f : ι → F) {C : ℝ}, (0 : ℝ) < C → (∀ i ∈ s, ‖f i‖ < C) → ‖∑ i ∈ s, f i‖ < C := by
  intro F ι _ _ s f C hC h
  refine Finset.sum_induction f (fun x => ‖x‖ < C) ?_ ?_ h
  · intro a b ha hb
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  · simpa using hC
end

