import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSum
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.GaussSum

theorem twist {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by
  by_cases hz : ∑ x, e (Q x) = 0
  · exact Or.inl hz
  right
  have hsq : (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) := by
    calc (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ x, e (ψ x - Q x) * ∑ y, e (Q y) := by
          rw [← Finset.sum_mul, ← hT]
      _ = ∑ x, ∑ z, e (Q z) * e (ψ x + B x z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Equiv.sum_comp (Equiv.addLeft x), Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← he, ← he, Equiv.coe_addLeft, hQ]
          congr 1
          abel
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
  have hne : ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) ≠ 0 := hsq ▸ mul_ne_zero hz hz
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha' := right_ne_zero_of_mul ha
  have h1 : ∀ y, e (ψ y + B y a) = 1 := by
    intro y
    have : ∑ x, e (ψ x + B x a) = e (ψ y + B y a) * ∑ x, e (ψ x + B x a) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addLeft y)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he, Equiv.coe_addLeft]
      congr 1
      simp only [map_add, AddMonoidHom.add_apply]
      abel
    exact (mul_eq_right₀ ha').1 this.symm
  refine ⟨a, ?_⟩
  conv_lhs => rw [hT]
  rw [map_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (e (Q x))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, ← he, Equiv.coe_addRight, hQ, ← mul_one (e (Q a + _)), ← h1 x, ← he]
  congr 1
  abel

def quat {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) : Fin 4 → M :=
  ![a • x 0 + (-b) • x 1 + (-c) • x 2 + (-d) • x 3,
    b • x 0 + a • x 1 + (-d) • x 2 + c • x 3,
    c • x 0 + d • x 1 + a • x 2 + (-b) • x 3,
    d • x 0 + (-c) • x 1 + b • x 2 + a • x 3]

theorem quat_add {M : Type} [AddCommGroup M] (a b c d : ℤ) (x y : Fin 4 → M) :
    quat a b c d (x + y) = quat a b c d x + quat a b c d y := by
  funext i
  fin_cases i <;> simp [quat] <;> module

theorem quat_conj {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) (i : Fin 4) :
    quat a (-b) (-c) (-d) (quat a b c d x) i = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • x i := by
  fin_cases i <;> simp [quat] <;> module

theorem quat_form {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by
  simp only [Fin.sum_univ_four, quat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply]
  module

theorem pow_four {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by
  classical
  set n := Fintype.card M with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnx : ∀ x : M, (n : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  have hm : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (n : ℤ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) habcd
    push_cast [Nat.cast_sub hn1] at h
    exact h
  have hinj : Function.Injective (quat (M := M) (a : ℤ) b c d) := by
    intro x y hxy
    funext i
    have hx := quat_conj (a : ℤ) b c d x i
    have hy := quat_conj (a : ℤ) b c d y i
    rw [hm, sub_smul, hnx, one_smul, zero_sub] at hx hy
    rw [← neg_inj, ← hx, ← hy, hxy]
  have hbij := hinj.bijective_of_finite
  have hprod : ∀ y : Fin 4 → W, e (∑ i, y i) = ∏ i, e (y i) := by
    intro y; simp only [Fin.sum_univ_four, Fin.prod_univ_four, he]
  have hS4 : (∑ x, e (q x)) ^ 4 = ∑ x : Fin 4 → M, e (∑ i, q (x i)) := by
    rw [Finset.sum_pow', Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => (hprod (fun i => q (x i))).symm)
  let B : (Fin 4 → M) →+ (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ∑ i, β (x i) (y i))
      (fun y z => by simp [Finset.sum_add_distrib]))
    (fun x y => by ext z; simp [Finset.sum_add_distrib])
  have hB : ∀ x y, B x y = ∑ i, β (x i) (y i) := fun _ _ => rfl
  have hQ : ∀ x y : Fin 4 → M, ∑ i, q ((x + y) i) = ∑ i, q (x i) + ∑ i, q (y i) + B x y := by
    intro x y
    simp only [hB, Pi.add_apply, hq, Finset.sum_add_distrib]
  have hnB : ∀ x y, (n : ℤ) • B x y = 0 := by
    intro x y
    rw [← map_zsmul]
    have : (n : ℤ) • y = 0 := funext fun i => hnx (y i)
    rw [this, map_zero]
  let ψ : (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => ∑ i, q (quat (a : ℤ) b c d x i) + ∑ i, q (x i)) (by
      intro x y
      rw [quat_add, hQ, hQ, hB (quat _ _ _ _ _), quat_form, hm, ← hB, sub_smul, hnB, one_smul]
      abel)
  have := twist e he hc h0 (fun x : Fin 4 → M => ∑ i, q (x i)) B hQ ψ (by
    rw [← hbij.sum_comp (fun x => e (∑ i, q (x i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [ψ])
  rw [← hS4] at this
  simpa only [hprod] using this

theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [mul_pow, pow_mul, h, mul_comm m, pow_mul, h']; simp

theorem isMu_norm {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem ph_sum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  intro M _ _ f ⟨h1, h3⟩
  have hmu : ∀ x, IsMu (f x) := fun x => h1 x trivial
  let u : M → Circle := fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (isMu_norm (hmu x))⟩
  let p : M → Additive Circle := fun x => Additive.ofMul (u x)
  have hp : ∀ x y z, p (x + y + z) + p x + p y + p z = p (x + y) + p (y + z) + p (x + z) + p 0 := by
    intro x y z
    have : u (x + y + z) * u x * u y * u z = u (x + y) * u (y + z) * u (x + z) * u 0 :=
      Circle.ext (by simp only [Circle.coe_mul]; exact h3 x trivial y trivial z trivial)
    exact congrArg Additive.ofMul this
  let β : M →+ M →+ Additive Circle := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => p (x + y) - p x - p y + p 0)
      (fun y z => by
        have := hp x y z
        rw [← add_assoc]
        rw [← sub_eq_zero] at this ⊢; rw [← this]; abel))
    (fun x y => by
      ext1 z
      have := hp x y z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← sub_eq_zero] at this ⊢; rw [← this]; abel)
  let e : Additive Circle → ℂ := fun t => ((Additive.toMul t : Circle) : ℂ)
  have he : ∀ s t, e (s + t) = e s * e t := fun s t => by simp [e]
  have hc : ∀ t, e (-t) = conj (e t) := fun t => by
    simp only [e, toMul_neg]; exact Circle.coe_inv_eq_conj _
  have hf : ∀ x, f x = f 0 * e (p x - p 0) := by
    intro x
    have : e (p 0 + (p x - p 0)) = e (p x) := by congr 1; abel
    rw [he] at this
    exact this.symm
  have hmu' : ∀ x, IsMu (e (p x - p 0)) := by
    intro x
    rw [sub_eq_add_neg, he, hc]
    refine isMu_mul (hmu x) ?_
    obtain ⟨m, hm, h⟩ := hmu 0
    exact ⟨m, hm, by rw [← map_pow]; change conj (f 0 ^ m) = 1; rw [h, map_one]⟩
  have hsum : ∑ x, f x = f 0 * ∑ x, e (p x - p 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => hf x
  rw [hsum]
  rcases pow_four e he hc (by simp [e]) (fun x => p x - p 0) β (fun x y => by
    simp only [β, AddMonoidHom.mk'_apply]; abel) with h | ⟨a, h⟩
  · rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h, mul_zero]; exact ph_zero
  · set S := ∑ x, e (p x - p 0)
    have hz : IsMu (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) := by
      refine isMu_mul ?_ ?_
      · obtain ⟨m, hm, h⟩ := hmu 0
        exact ⟨m, hm, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩
      · rw [Fin.prod_univ_four]
        exact isMu_mul (isMu_mul (isMu_mul (hmu' _) (hmu' _)) (hmu' _)) (hmu' _)
    obtain ⟨m, hm, hz⟩ := hz
    refine ⟨8 * m, by omega, ?_⟩
    have h8 : (f 0 * S) ^ 8 = (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) * ((‖f 0 * S‖ : ℝ) : ℂ) ^ 8 := by
      have hn : ((‖S‖ : ℝ) : ℂ) ^ 8 = S ^ 4 * conj (S ^ 4) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
      rw [norm_mul, isMu_norm (hmu 0), one_mul, hn]
      linear_combination f 0 ^ 8 * S ^ 4 * h
    rw [pow_mul, h8, mul_pow, hz, one_mul, pow_mul]

end GlobalTheory.Phase.GaussSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarAlg

variable {K : Type} [Field K] {κ ι : Type}

theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

theorem intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n

theorem hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (intM_natCast_smul S hy)

theorem exists_common_level {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩

theorem hasLevel_map₂ {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]

theorem apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp

theorem apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by
  obtain ⟨p, hp⟩ := QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x
  rw [hp]
  exact apply_add_of_mem_perSub h p.2 x

theorem exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

theorem hasLevel_translate {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy

theorem finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl

end GlobalTheory.SW.HaarAlg

open GlobalTheory.SW.HaarAlg in

theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralEqSumResidueRepresentative
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem mem_perSub_iff_exists_eq_smul_zm {κ ι : Type} [Fintype κ] [Fintype ι] (R : ℕ)
    (y : Matrix κ ι ℚ) : y ∈ _root_.GlobalTheory.SW.perSub ℚ κ ι R ↔
      ∃ m : κ → ι → ℤ, y = R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  rw [_root_.GlobalTheory.SW.HaarLevel.mem_perSub]
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨m, hm⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp
      ((_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y', rfl⟩)
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨y', hy'⟩ := (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mp
      ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)
    exact ⟨y', by rw [hy']⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_injective_of_neg_add_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.FourierJ.haar_eq_sum_rep : ∀ (κ ι : Type) [Fintype κ]
    [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R →
    _root_.GlobalTheory.SW.HasLevel R φ → _root_.GlobalTheory.SW.haar φ =
      ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
        ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) := by
  intro κ ι _ _ _ _ R φ hR hφ
  classical
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.SW.haar_eq_haarAt ℚ κ ι R φ hR hφ
  rw [h1]
  unfold _root_.GlobalTheory.SW.haarAt
  rw [Module.finrank_self, one_mul]
  congr 1
  have hper : ∀ x : Matrix κ ι ℚ, φ (Quotient.out
      (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) = φ x := by
    intro x
    have hmem : -x + Quotient.out
        (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) ∈
        _root_.GlobalTheory.SW.perSub ℚ κ ι R :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have h := _root_.GlobalTheory.SW.HaarLevel.periodic hφ x _ hmem
    rwa [add_neg_cancel_left] at h
  have hsupp : (Function.support fun q : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R =>
      φ (Quotient.out q)) ⊆ ↑(Finset.univ.image fun n : κ → ι → Fin (R * R) =>
        (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
          Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR _ (hφ.1 _ (Function.mem_support.mp hq))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, hnm, QuotientAddGroup.eq, neg_add_cancel_left]
    exact (mem_perSub_iff_exists_eq_smul_zm R _).mpr ⟨m, rfl⟩
  have hinj : Function.Injective fun n : κ → ι → Fin (R * R) =>
      (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
        Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) := by
    intro n n' h
    obtain ⟨m, hm⟩ := (mem_perSub_iff_exists_eq_smul_zm R _).mp (QuotientAddGroup.eq.mp h)
    exact rep_injective_of_neg_add_eq_smul_zm hR m hm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun n _ n' _ h => hinj h)]
  exact Finset.sum_congr rfl fun n _ => hper _

end GlobalTheory.SW.FourierJ
end

