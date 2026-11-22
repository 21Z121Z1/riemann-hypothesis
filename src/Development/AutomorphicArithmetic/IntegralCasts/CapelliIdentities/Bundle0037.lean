import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailFurther
section
namespace UpperTheory.Reformulated.B.Yva3.Helpers

private lemma key {α ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) (u : Finset (ι → α)) :
    ∑ ξ ∈ u, ∏ i, f (ξ i) ≤ ∏ _i : ι, ∑' x, f x := by
  have h1 : ∑ ξ ∈ u, ∏ i, f (ξ i)
      ≤ ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hξ
    · intro ξ _ _
      exact Finset.prod_nonneg fun i _ => h0 (ξ i)
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i)
      = ∏ i, ∑ x ∈ u.image (fun η => η i), f x :=
    by rw [Finset.prod_univ_sum]
  have h3 : ∏ i, ∑ x ∈ u.image (fun η => η i), f x ≤ ∏ _i : ι, ∑' x, f x := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg fun x _ => h0 x
    · intro i _
      exact hf.sum_le_tsum _ (fun x _ => h0 x)
  exact h1.trans (h2.le.trans h3)

private lemma summ {α ι : Type} [Fintype ι] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) : Summable fun (ξ : ι → α) ↦ ∏ i : ι, f (ξ i) := by
  classical
  exact summable_of_sum_le (fun ξ => Finset.prod_nonneg fun i _ => h0 (ξ i)) (key hf h0)

end UpperTheory.Reformulated.B.Yva3.Helpers

theorem UpperTheory.Reformulated.B.Yva3.main :
    ∀ {k : Type} [inst : Field k] [NumberField k] {ι : Type} [inst : Fintype ι] {f : k → ℝ},
      Summable f → (∀ (a : k), (0 : ℝ) ≤ f a) → Summable fun (ξ : ι → k) ↦ ∏ i : ι, f (ξ i) := by
  intro k _ _ ι _ f hf h0
  exact UpperTheory.Reformulated.B.Yva3.Helpers.summ hf h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntMvPderiv
section
noncomputable def UpperTheory.Reformulated.B.Gwb7.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwb7.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.Gwb7.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.Gwb7.intMv_pderiv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]} (i : σ),
      UpperTheory.Reformulated.B.Gwb7.IntegralMv F →
        UpperTheory.Reformulated.B.Gwb7.IntegralMv ((MvPowerSeries.pderiv ℂ_[p] i : MvPowerSeries σ ℂ_[p] → MvPowerSeries σ ℂ_[p]) F) := by
  intro p _ σ F i hF n
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : ℕ) : ℂ_[p]) + 1‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n i + 1)
    rwa [Nat.cast_add, Nat.cast_one] at h
  change ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv ℂ_[p] i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntRing
section
noncomputable def UpperTheory.Reformulated.B.CapelliIdentity₂.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegerDenominator
section
private theorem UpperTheory.Reformulated.B.IntegerDenominator.exists_int_denom {E : Type} [Field E] [NumberField E] {n : Type}
    (L : Submodule (NumberField.RingOfIntegers E) (n → E))
    (x : n → E) (hx : x ∈ Submodule.span E (↑L : Set (n → E))) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hay b) (zsmul_mem hbz a)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hbc⟩ := hc.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (c • y) =
        (⟨b • c, hbc⟩ : NumberField.RingOfIntegers E) • (a • y) := by
      change _ = (b • c) • (a • y)
      rw [smul_comm (b • c) a y, smul_assoc, mul_smul]
    rw [h]
    exact L.smul_mem _ hay

theorem UpperTheory.Reformulated.B.IntegerDenominator.exists_denom_pt :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E]
    [NumberField E] [inst_4 : Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
    (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
    Submodule.span E (↑L : Set (n → E)) = ⊤ →
      ∀ (x : n → E),
        ∃ (D : NumberField.RingOfIntegers F),
          D ≠ (0 : NumberField.RingOfIntegers F) ∧ (Algebra.algebraMap F E : F → E) (↑D : F) • x ∈ L := by
  intro F E _ _ _ _ _ n _ _ L hL x
  obtain ⟨N, hN, hNx⟩ := UpperTheory.Reformulated.B.IntegerDenominator.exists_int_denom L x (hL ▸ Submodule.mem_top)
  refine ⟨(N : NumberField.RingOfIntegers F), Int.cast_ne_zero.2 hN, ?_⟩
  have h : (Algebra.algebraMap F E : F → E) ((N : NumberField.RingOfIntegers F) : F) = (N : E) := by
    have h1 : ((N : NumberField.RingOfIntegers F) : F) = (N : F) :=
      map_intCast (algebraMap (NumberField.RingOfIntegers F) F) N
    rw [h1]
    exact map_intCast (algebraMap F E) N
  rw [h, Int.cast_smul_eq_zsmul]
  exact hNx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralExtensionAlgClosed
section
theorem UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral :
    ∀ (R S K : Type) [inst : CommRing R] [inst_1 : CommRing S]
    [inst_2 : Algebra R S] [Algebra.IsIntegral R S] [inst_4 : Field K] [IsAlgClosed K],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (b : R →+* K), ∃ (Φ : S →+* K), Φ.comp (Algebra.algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ hinj b
  haveI hp : (RingHom.ker b).IsPrime := RingHom.ker_isPrime b
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker b) ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := by simpa using hx
      have : x = 0 := hinj (by simpa using hx0)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker b) := ⟨hQp.symm⟩
  letI : Algebra (R ⧸ RingHom.ker b) K := (RingHom.kerLift b).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective b)
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker b) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker b] K := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext x
  exact ψ.commutes (Ideal.Quotient.mk (RingHom.ker b) x)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralImagQuadraticHalfInt
section
open Polynomial

private lemma coords {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (z : E) (hz : z ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, z = (a : E) + (b : E) * s := by
  have hint : IsIntegral ℚ s := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]
    exact (isIntegral_natCast d).neg
  have hz' : z ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * e * hs

private lemma aeval_pair {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hs : s ^ 2 = -(d : E))
    (a b : ℚ) (p : ℤ[X]) :
    ∃ u v : ℚ, aeval ((a : E) + (b : E) * s) p = (u : E) + (v : E) * s ∧
      aeval ((a : E) - (b : E) * s) p = (u : E) - (v : E) * s := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hq
    refine ⟨u + u', v + v', ?_, ?_⟩
    · rw [map_add, h1, h1']; push_cast; ring
    · rw [map_add, h2, h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨u, v, h1, h2⟩ := h
    refine ⟨u * a - d * v * b, u * b + v * a, ?_, ?_⟩
    · rw [pow_succ, ← mul_assoc, map_mul, h1, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs
    · rw [pow_succ, ← mul_assoc, map_mul, h2, aeval_X]
      push_cast
      linear_combination (v : E) * b * hs

private lemma conj_integral {E : Type} [Field E] [CharZero E] (d : ℕ) (s : E) (hd : 0 < d)
    (hs : s ^ 2 = -(d : E)) (a b : ℚ) (h : IsIntegral ℤ ((a : E) + (b : E) * s)) :
    IsIntegral ℤ ((a : E) - (b : E) * s) := by
  obtain ⟨p, hp, h0⟩ := h
  obtain ⟨u, v, h1, h2⟩ := aeval_pair d s hs a b p
  rw [← aeval_def, h1] at h0
  have hn : u ^ 2 + d * v ^ 2 = 0 := by
    have : (u : E) ^ 2 + d * (v : E) ^ 2 = 0 := by
      linear_combination ((u : E) - v * s) * h0 + (v : E) ^ 2 * hs
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hv2 : 0 ≤ (d : ℚ) * v ^ 2 := by positivity
  have hu : u = 0 := by nlinarith [sq_nonneg u]
  have hv : v = 0 := by
    rw [hu] at hn
    have : (d : ℚ) * v ^ 2 = 0 := by simpa using hn
    simpa [hd'.ne'] using this
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, h2, hu, hv]
  simp

private lemma rat_int {E : Type} [Field E] [CharZero E] (q : ℚ) (h : IsIntegral ℤ (q : E)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  have h' : IsIntegral ℤ q := by
    have := (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := E) (x := q)
      (algebraMap ℚ E).injective).1 (by simpa using h)
    exact this
  simpa using (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 h'

private lemma int_of_sqfree_mul_sq (d : ℕ) (hd : Squarefree d) (q : ℚ) (m : ℤ)
    (h : (m : ℚ) = d * q ^ 2) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
  have h2 : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * m := by
    have : (d : ℚ) * (q.num : ℚ) ^ 2 = (q.den : ℚ) ^ 2 * m := by
      rw [← h1, h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    (Rat.isCoprime_num_den q).symm.pow
  have h3 : (q.den : ℤ) ^ 2 ∣ d := hc.dvd_of_dvd_mul_right ⟨m, h2⟩
  have h4 : q.den * q.den ∣ d := by
    rw [← sq]; exact_mod_cast h3
  have h5 : q.den = 1 := Nat.isUnit_iff.1 (hd _ h4)
  exact ⟨q.num, by rw [← h1, h5]; simp⟩

theorem UpperTheory.integral_imag_quadratic_half_int :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by
  intro E _ _ d s hd hs z hz hi
  obtain ⟨a, b, rfl⟩ := coords d s hs z hz
  have hc := conj_integral d s (Nat.pos_of_ne_zero hd.ne_zero) hs a b hi
  obtain ⟨x, hx⟩ := rat_int (E := E) (2 * a) (by
    have e : ((2 * a : ℚ) : E) = (a : E) + (b : E) * s + ((a : E) - (b : E) * s) := by
      push_cast; ring
    rw [e]
    exact hi.add hc)
  obtain ⟨n, hn⟩ := rat_int (E := E) (a ^ 2 + d * b ^ 2) (by
    have e : ((a ^ 2 + d * b ^ 2 : ℚ) : E)
        = ((a : E) + (b : E) * s) * ((a : E) - (b : E) * s) := by
      push_cast
      linear_combination (b : E) ^ 2 * hs
    rw [e]
    exact hi.mul hc)
  obtain ⟨y, hy⟩ := int_of_sqfree_mul_sq d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hx, hn]; ring)
  have key : x ^ 2 + d * y ^ 2 = 4 * n := by
    have : (x : ℚ) ^ 2 + d * (y : ℚ) ^ 2 = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  refine ⟨x, y, ?_, ?_⟩
  · rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨l, rfl | rfl⟩
    · exact ⟨k - l, by ring⟩
    · exfalso
      have h4 : (4 : ℤ) ∣ d := ⟨n - k ^ 2 - d * (l ^ 2 + l), by linear_combination key⟩
      have h5 : 2 * 2 ∣ d := by exact_mod_cast h4
      simpa using hd 2 h5
    · exfalso
      have h4 : 4 * (n - k ^ 2 - k - d * l ^ 2) = 1 := by linear_combination -key
      omega
    · exact ⟨k - l, by ring⟩
  · have hx' : (x : E) = 2 * (a : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hx
    have hy' : (y : E) = 2 * (b : E) := by exact_mod_cast congrArg (fun t : ℚ => (t : E)) hy
    rw [hx', hy']; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralMv
section
noncomputable def UpperTheory.Reformulated.B.Gwb3.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwb3.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.Gwb3.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.Gwb3.intMv_one.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1}, UpperTheory.Reformulated.B.Gwb3.IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p inst σ n
  classical
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ (1 : ℝ)
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralOfNormBounded
section
open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra A K) {t y : K} (hty : t * y = 1) (hy : y ∈ B) (ht : IsIntegral A t) :
    t ∈ B := by
  obtain ⟨p, hm, hp⟩ := ht
  have key : ∀ (q : A[X]) (n : ℕ), q.natDegree ≤ n → y ^ n * aeval t q ∈ B := by
    intro q n hq
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ n * (q.coeff i • t ^ i) = q.coeff i • y ^ (n - i) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
      rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add]
      congr 1
      rw [mul_comm (y ^ i), mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hy _) _
  have h0 : aeval t p = 0 := hp
  have hd : p.natDegree ≠ 0 := by
    intro h
    have h1 := eq_one_of_monic_natDegree_zero hm h
    simp [h1] at h0
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h2 : aeval t p.eraseLead + t ^ (d + 1) = 0 := by
    have h3 := p.eraseLead_add_C_mul_X_pow
    rw [← h3, map_add, map_mul, aeval_C, map_pow, aeval_X, hm.leadingCoeff, map_one, one_mul,
      hd'] at h0
    exact h0
  have h4 : t = -(y ^ d * aeval t p.eraseLead) := by
    have h5 : y ^ d * t ^ (d + 1) = t := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, one_mul]
    have h6 : aeval t p.eraseLead = -t ^ (d + 1) := eq_neg_of_add_eq_zero_left h2
    rw [h6, mul_neg, neg_neg, h5]
  rw [h4]
  refine neg_mem (key _ _ ?_)
  have := p.eraseLead_natDegree_le
  omega

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le {l : ℕ} [Fact (Nat.Prime l)] {K : Type}
    [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K]
    [IsScalarTower ℤ_[l] ℚ_[l] K] (z : K) (hz : spectralNorm ℚ_[l] K z ≤ 1) :
    IsIntegral ℤ_[l] z := by
  have hzi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hzi
  have hc := (spectralValue_le_one_iff hmon).mp hz
  have hl : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, ← eval₂_map, hq]
  exact minpoly.aeval ℚ_[l] z

theorem UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] {K : Type} [inst_4 : Field K]
    [inst_5 : Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [inst_7 : Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R,
      IsIntegral ℤ_[l] ((x : R → K) a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ (x : R → K) a ^ n = (↑l : K) * b := by
  intro l _ R _ _ _ K _ _ _ _ _ x a ha
  have hA : ∀ t : K, t * x a = 1 → ¬ IsIntegral ℤ_[l] t := by
    intro t hty ht
    obtain ⟨r, hr⟩ : t ∈ x.range :=
      UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one x.range hty ⟨a, rfl⟩ ht
    have hr' : x r = t := hr
    have hmem : a * r ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
    have hu : IsUnit (1 - a * r) := by
      by_contra hn
      have h1 : 1 - a * r ∈ IsLocalRing.maximalIdeal R := hn
      have h2 := Ideal.add_mem _ h1 hmem
      rw [sub_add_cancel] at h2
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
    have h3 := hu.map x
    have h4 : x (1 - a * r) = 0 := by
      rw [map_sub, map_mul, map_one, hr', mul_comm, hty, sub_self]
    rw [h4] at h3
    exact not_isUnit_zero h3
  change IsIntegral ℤ_[l] (x a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ x a ^ n = (↑l : K) * b
  generalize x a = y at hA
  by_cases hy : y = 0
  · subst hy
    exact ⟨isIntegral_zero, 1, 0, isIntegral_zero, by simp⟩
  let f := spectralMulAlgNorm ℚ_[l] K
  have hf : ∀ z, f z = spectralNorm ℚ_[l] K z := fun _ => rfl
  have hfmul : ∀ u v, f (u * v) = f u * f v := fun u v => map_mul f u v
  have hf1 : f 1 = 1 := map_one f
  have hfy : f y < 1 := by
    have h1 : ¬ f y⁻¹ ≤ 1 := fun h =>
      hA y⁻¹ (inv_mul_cancel₀ hy) (UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ h)
    have h2 : f y * f y⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ hy, hf1]
    have h3 : 0 ≤ f y := (hf y).symm ▸ spectralNorm_nonneg y
    push_neg at h1
    nlinarith
  have hfpow : ∀ (n : ℕ) (z : K), f (z ^ n) = f z ^ n := by
    intro n z
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hfmul, ih, pow_succ]
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime l).pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hlpos) hfy
  have hlK : (l : K) ≠ 0 := by
    have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h1]
    have h2 : (l : ℚ_[l]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    exact (map_ne_zero (algebraMap ℚ_[l] K)).mpr h2
  refine ⟨UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ hfy.le, n, y ^ n * (l : K)⁻¹,
    UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ ?_, ?_⟩
  · have h1 : f ((l : K)⁻¹) = l := by
      have h2 : (l : K)⁻¹ = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by simp
      rw [h2, hf, spectralNorm_extends, norm_inv, Padic.norm_p]
      simp
    change f (y ^ n * (l : K)⁻¹) ≤ 1
    rw [hfmul, hfpow, h1]
    calc f y ^ n * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ hlpos.ne'
  · field_simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFirst
section
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFirst.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialFirst.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialFirst.intMv_add.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv (F + G) := by
  intro p _ σ F G hF hG n
  have h1 : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := hF n
  have h2 : ‖MvPowerSeries.coeff n G‖ ≤ (1 : ℝ) := hG n
  show ‖MvPowerSeries.coeff n (F + G)‖ ≤ (1 : ℝ)
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralPolynomialFourth
section
noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialFourth.intMv_neg.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv (-F) := by
  intro p _ σ F h n
  have hn : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := h n
  show ‖MvPowerSeries.coeff n (-F)‖ ≤ (1 : ℝ)
  rw [map_neg, norm_neg]
  exact hn
end

