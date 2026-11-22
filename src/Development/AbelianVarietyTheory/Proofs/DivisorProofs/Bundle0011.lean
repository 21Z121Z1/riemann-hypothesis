import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairing
section
namespace GlobalTheory.DualParts

theorem card_le_of_injective_chars (G H : Type) [CommGroup G] [Finite G] (U : Type) [CommRing U]
    [IsDomain U] (f : H → (G →* Uˣ)) (hf : Function.Injective f) :
    Finite H ∧ Nat.card H ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  let g : H → (G →* U) := fun h => (Units.coeHom U).comp (f h)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    refine MonoidHom.ext fun x => Units.ext ?_
    have := congrArg (fun χ : G →* U => χ x) hab
    simpa [g] using this
  have hli : LinearIndependent U (fun h => (g h : G → U)) :=
    (linearIndependent_monoidHom G U).comp g hg
  haveI : Finite H := hli.finite
  haveI := Fintype.ofFinite H
  refine ⟨inferInstance, ?_⟩
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  simpa [Nat.card_eq_fintype_card] using this

theorem conj_dual_parts : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  intro O _ bar U _ _ M M' _ _ α α' h1 hmul hadd h1' hmul' hadd' hbb e e' he he' hee hee' u w n huw hcop
    hkill hw hfin
  have hsurj : Function.Surjective bar := fun a => ⟨bar a, hbb a⟩
  have hbarbar : (u.map bar).map bar = u := by
    rw [Ideal.map_map]
    have : bar.comp bar = RingHom.id O := RingHom.ext hbb
    rw [this, Ideal.map_id]
  have hsplit : ∀ k : ℕ, ∃ a₀ ∈ u ^ k, ∃ b₀ ∈ (u.map bar) ^ k, a₀ + b₀ = 1 := by
    intro k
    have hc : IsCoprime u (u.map bar) := Ideal.isCoprime_iff_sup_eq.2 hcop
    have hs : u ^ k ⊔ (u.map bar) ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.1 (hc.pow)
    have h1mem : (1 : O) ∈ u ^ k ⊔ (u.map bar) ^ k := by rw [hs]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
    exact ⟨a, ha, b, hb, hab⟩
  have hbar1 : ∀ k, ∀ a ∈ u ^ k, bar a ∈ (u.map bar) ^ k := by
    intro k a ha
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem bar ha
  have hbar2 : ∀ k, ∀ b ∈ (u.map bar) ^ k, bar b ∈ u ^ k := by
    intro k b hb
    have := Ideal.mem_map_of_mem bar hb
    rwa [Ideal.map_pow, hbarbar] at this
  have hprod : ∀ k, n ≤ k → ∀ a ∈ u ^ k, ∀ b ∈ (u.map bar) ^ k, a * b ∈ (u * u.map bar) ^ n := by
    intro k hk a ha b hb
    have : a * b ∈ (u * u.map bar) ^ k := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    exact Ideal.pow_le_pow_right hk this
  have hpowle : ∀ (I : Ideal O) (k m : ℕ), m ≤ k → I ^ k ≤ I ^ m := fun I k m h =>
    Ideal.pow_le_pow_right h

  have part1 : ∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1 := by
    rintro x ⟨m, hm⟩ c hc
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective bar hsurj).1 hc
    apply he
    rw [map_one]
    refine MonoidHom.ext fun y => ?_
    rw [MonoidHom.one_apply, hee, hbb]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (m + n)
    have hy : y = α a₀ y * α b₀ y := by rw [← hadd, hab, h1]
    rw [hy, map_mul, map_mul]
    have t1 : e x (α a (α a₀ y)) = 1 := by
      rw [← hmul, ← hbb (a * a₀), ← hee, map_mul bar, hmul',
        hm (bar a₀) (hpowle _ (m + n) m (by omega) (hbar1 _ a₀ ha₀))]
      simp
    have t2 : α a (α b₀ y) = 1 := by
      refine hw (α b₀ y) ⟨m + n, fun c hc => ?_⟩ a ha
      rw [← hmul]; exact (hkill _ (hprod (m + n) (by omega) c hc b₀ hb₀)).1 y
    rw [t1, t2, map_one, one_mul]
  refine ⟨part1, ?_⟩

  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (n + 1)
  let A : Subgroup M :=
    { carrier := {y | ∀ a ∈ w, α a y = 1}
      one_mem' := fun a _ => map_one (α a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w, α a y = 1 from hy) a ha,
          (show ∀ a ∈ w, α a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w, α a y = 1 from hy) a ha, inv_one] }
  let B : Subgroup M' :=
    { carrier := {x | ∀ a ∈ w.map bar, α' a x = 1}
      one_mem' := fun a _ => map_one (α' a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha,
          (show ∀ a ∈ w.map bar, α' a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha, inv_one] }
  have hu1 : u ^ (n + 1) ≤ u := Ideal.pow_le_self (by omega)
  have hub1 : (u.map bar) ^ (n + 1) ≤ u.map bar := Ideal.pow_le_self (by omega)

  have F1 : ∀ y, α b₀ y ∈ A := by
    intro y
    refine hw (α b₀ y) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul]; exact (hkill _ (hprod (n + 1) (by omega) c hc b₀ hb₀)).1 y
  have F2 : ∀ x ∈ B, α' (bar a₀) x = 1 := fun x hx =>
    hx _ (Ideal.map_mono huw (hub1 (hbar1 _ a₀ ha₀)))
  have E1 : ∀ x ∈ B, ∀ y, e x y = e x (α b₀ y) := by
    intro x hx y
    conv_lhs => rw [← h1 y, ← hab, hadd, map_mul]
    rw [← hbb a₀, ← hee, F2 x hx]
    simp
  have F3 : ∀ x, α' a₀ x ∈ B := by
    intro x
    refine part1 (α' a₀ x) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul', mul_comm]; exact (hkill _ (hprod (n + 1) (by omega) a₀ ha₀ c hc)).2 x
  have F4 : ∀ y ∈ A, α (bar b₀) y = 1 := fun y hy => hy _ (huw (hu1 (hbar2 _ b₀ hb₀)))
  have E2 : ∀ y ∈ A, ∀ x, e' y x = e' y (α' a₀ x) := by
    intro y hy x
    conv_lhs => rw [← h1' x, ← hab, hadd', map_mul]
    rw [← hbb b₀, ← hee', F4 y hy]
    simp
  haveI : Finite A := hfin
  have hAB : Finite B ∧ Nat.card B ≤ Nat.card A := by
    refine card_le_of_injective_chars A B U (fun x => (e x.1).comp A.subtype) ?_
    intro x₁ x₂ h
    apply Subtype.ext
    apply he
    refine MonoidHom.ext fun y => ?_
    rw [E1 x₁.1 x₁.2, E1 x₂.1 x₂.2]
    exact congrArg (fun χ : A →* Uˣ => χ ⟨α b₀ y, F1 y⟩) h
  haveI : Finite B := hAB.1
  have hBA : Finite A ∧ Nat.card A ≤ Nat.card B := by
    refine card_le_of_injective_chars B A U (fun y => (e' y.1).comp B.subtype) ?_
    intro y₁ y₂ h
    apply Subtype.ext
    apply he'
    refine MonoidHom.ext fun x => ?_
    rw [E2 y₁.1 y₁.2, E2 y₂.1 y₂.2]
    exact congrArg (fun χ : B →* Uˣ => χ ⟨α' a₀ x, F3 x⟩) h
  exact le_antisymm hAB.2 hBA.2

end GlobalTheory.DualParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConj
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory

open scoped ComplexOrder in
open Matrix in

theorem _root_.GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBounds
section
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  choose u hus hub using hu
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl
  rw [hinf] at hf ⊢
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro t₀
  let ρ : ContDiffBump t₀ := ⟨1/2, 1, by norm_num, by norm_num⟩
  set R : ℝ := ‖t₀‖ + 1 with hR
  let ρc : (Fin k → ℝ) → ℂ := fun t => ((ρ t : ℝ) : ℂ)
  have hρc : ContDiff ℝ ∞ ρc := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have hρcs : HasCompactSupport ρc := ρ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B := fun j =>
    (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hρcs.iteratedFDeriv j)
  choose B hB using hB
  have hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0 := by
    intro j x hx
    by_contra h
    have hx1 : x ∈ tsupport ρc := support_iteratedFDeriv_subset j h
    have h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ) :=
      tsupport_comp_subset Complex.ofReal_zero _
    rw [ρ.tsupport_eq] at h2
    exact hx (h2 hx1)
  have hunonneg : ∀ m i, 0 ≤ u m R i := fun m i =>
    (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  let v : ℕ → ι → ℝ := fun m i =>
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i
  have hv : ∀ m, Summable (v m) := fun m => by
    apply summable_sum
    intro j _
    exact (hus (m - j) R).mul_left _
  have hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i := by
    intro m i x
    refine (norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : x ∈ Metric.closedBall t₀ 1
    · have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have := norm_sub_norm_le x t₀
        rw [hR]; linarith
      apply mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _)
        (mul_nonneg (by positivity) (hB0 j))
      exact mul_le_mul_of_nonneg_left (hB j x) (by positivity)
    · rw [hsupp j x hx, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)
  have hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t) :=
    contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top))
      (fun m _ => hv m) (fun m i x _ => hbound m i x)
  have heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t) := by
    filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [tsum_mul_left]
    have h1 : ρ t = 1 := ρ.one_of_mem_closedBall ht
    simp [ρc, h1]
  exact (hsm.contDiffAt).congr_of_eventuallyEq heq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
section
open Filter Topology

namespace GlobalTheory.CharSeriesCoef

noncomputable def avg {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y)
    (χ : AddChar Y ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, χ (w i)

theorem norm_avg_le_one_of {ι : Type} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hc, mul_one]
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι := by simp

theorem avg_prod {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv]
  ring

theorem geom_avg_le {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) K, geom_sum_eq hζ K]
  have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : ‖ζ ^ K - 1‖ ≤ 2 := by
    calc ‖ζ ^ K - 1‖ ≤ ‖ζ ^ K‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, h1]; norm_num
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (K:ℝ)⁻¹ * (‖ζ ^ K - 1‖ / ‖ζ - 1‖) ≤ (K:ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by gcongr
    _ = 2 / (K * ‖ζ - 1‖) := by field_simp

theorem exists_avg {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by
  classical
  revert h0
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨Unit, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · intro a T ha ih h0
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hT0 : (0:Ξ) ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    obtain ⟨ι, _, _, w, hw⟩ := ih hT0
    obtain ⟨y, hy⟩ := hne a ha0
    have hz : 0 < ‖e a y - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / (δ * ‖e a y - 1‖))
    have hK0 : (0:ℝ) < K := lt_trans (by positivity) hK
    have hKn : 0 < K := by exact_mod_cast hK0
    haveI : Nonempty (Fin K) := ⟨⟨0, hKn⟩⟩
    refine ⟨ι × Fin K, inferInstance, inferInstance,
      fun ik => w ik.1 + (ik.2 : ℕ) • y, ?_⟩
    intro b hb
    rw [avg_prod, norm_mul]
    have hA : ‖avg w (e b)‖ ≤ 1 := norm_avg_le_one_of _ (fun i => (hn b _).le)
    have hG : ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 := by
      have := norm_avg_le_one_of (ι := Fin K) (fun k => e b y ^ (k:ℕ))
        (fun k => by rw [norm_pow, hn]; simp)
      simpa using this
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · have hg := geom_avg_le hy (hn b y) K hKn
      have : 2 / (K * ‖e b y - 1‖) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hK
        nlinarith
      calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 * δ := by
            gcongr
            exact hg.trans this
        _ = δ := one_mul δ
    · calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ δ * 1 := by
            gcongr
            exact hw b hbT
        _ = δ := mul_one δ

theorem continuousAt_coef_zero {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P]
    (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (he0 : ∀ y, e 0 y = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ) (hM : Summable M)
    (hb : ∀ᶠ p in 𝓝 p0, ∀ a, ‖c p a‖ ≤ M a)
    (hc : ∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) :
    ContinuousAt (fun p => c p 0) p0 := by
  classical
  have hM0 : ∀ a, 0 ≤ M a := fun a => (norm_nonneg _).trans (hb.self_of_nhds a)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set S := ∑' a, M a with hSdef
  have hS : 0 ≤ S := tsum_nonneg hM0
  obtain ⟨s, hs⟩ : ∃ s : Finset Ξ, S - ∑ a ∈ s, M a < ε / 6 := by
    have h2 := (Metric.tendsto_nhds.mp hM.hasSum) (ε / 6) (by positivity)
    obtain ⟨s, hs⟩ := h2.exists
    refine ⟨s, ?_⟩
    rw [Real.dist_eq] at hs
    linarith [neg_abs_le (∑ a ∈ s, M a - S)]
  set δ := ε / 6 / (S + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδS : δ * S ≤ ε / 6 := by
    have : δ * (S + 1) = ε / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨ι, _, _, w, hw⟩ := exists_avg e hn hne δ hδ (s.erase 0) (by simp)
  set α : Ξ → ℂ := fun b => avg w (e b) with hαdef
  have hα1 : ∀ b, ‖α b‖ ≤ 1 := fun b => norm_avg_le_one_of _ (fun i => (hn b _).le)
  have hα0 : α 0 = 1 := by
    simp only [hαdef, avg, he0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let A : P → ℂ := fun p => (Fintype.card ι : ℂ)⁻¹ * ∑ i, ∑' a, e a (w i) * c p a
  have hAc : ContinuousAt A p0 :=
    continuousAt_const.mul (tendsto_finset_sum _ (fun i _ => hc (w i)))

  have key : ∀ p, (∀ a, ‖c p a‖ ≤ M a) → ‖A p - c p 0‖ ≤ δ * S + (S - ∑ a ∈ s, M a) := by
    intro p hp
    have hsum : ∀ i, HasSum (fun a => e a (w i) * c p a) (∑' a, e a (w i) * c p a) := by
      intro i
      refine (Summable.of_norm_bounded hM (fun a => ?_)).hasSum
      rw [norm_mul, hn, one_mul]; exact hp a
    have h1 : HasSum (fun a => α a * c p a) (A p) := by
      have := (hasSum_sum (s := Finset.univ) (fun i _ => hsum i)).mul_left
        ((Fintype.card ι : ℂ)⁻¹)
      have hfun : (fun a => α a * c p a)
          = fun a => (Fintype.card ι : ℂ)⁻¹ * ∑ i, e a (w i) * c p a := by
        funext a
        simp only [hαdef, avg, Finset.sum_mul, mul_assoc]
      rw [hfun]; exact this
    have h2 : HasSum (fun a : Ξ => if a = (0:Ξ) then c p 0 else 0) (c p 0) := hasSum_ite_eq (0:Ξ) (c p 0)
    have h3 : HasSum (fun a => α a * c p a - if a = 0 then c p 0 else 0) (A p - c p 0) :=
      HasSum.sub h1 h2
    have hg : HasSum (fun a => δ * M a + (M a - if a ∈ s then M a else 0))
        (δ * S + (S - ∑ a ∈ s, M a)) := by
      refine (hM.hasSum.mul_left δ).add (hM.hasSum.sub ?_)
      have : HasSum (fun a => if a ∈ s then M a else 0) (∑ b ∈ s, if b ∈ s then M b else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
      have e2 : (∑ b ∈ s, if b ∈ s then M b else 0) = ∑ b ∈ s, M b :=
        Finset.sum_congr rfl (fun b hb => if_pos hb)
      rw [e2] at this
      exact this
    refine h3.norm_le_of_bounded hg (fun a => ?_)
    have hMa := hM0 a
    by_cases ha : a = 0
    · subst ha
      simp only [hα0, one_mul, if_true, sub_self, norm_zero]
      split_ifs <;> nlinarith [mul_nonneg hδ.le hMa]
    · simp only [ha, if_false, sub_zero]
      by_cases has : a ∈ s
      · simp only [has, if_true, sub_self, add_zero]
        rw [norm_mul]
        have := hw a (Finset.mem_erase.mpr ⟨ha, has⟩)
        exact mul_le_mul this (hp a) (norm_nonneg _) hδ.le
      · simp only [has, if_false, sub_zero]
        rw [norm_mul]
        have : ‖α a‖ * ‖c p a‖ ≤ 1 * M a := mul_le_mul (hα1 a) (hp a) (norm_nonneg _) zero_le_one
        nlinarith
  have hAev := (Metric.tendsto_nhds.mp hAc) (ε / 3) (by positivity)
  have hp0 := key p0 hb.self_of_nhds
  filter_upwards [hb, hAev] with p hp hAp
  have hpk := key p hp
  rw [dist_eq_norm] at hAp ⊢
  have : c p 0 - c p0 0 = -(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0) := by ring
  rw [this]
  calc ‖-(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0)‖
      ≤ ‖-(A p - c p 0)‖ + ‖A p - A p0‖ + ‖A p0 - c p0 0‖ := norm_add₃_le
    _ < ε := by rw [norm_neg]; linarith

end GlobalTheory.CharSeriesCoef

theorem GlobalTheory.continuousAt_charSeries_coef_zero :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 :=
  fun e hn he0 hne c p0 M hM hb hc =>
    GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e hn he0 hne c p0 M hM hb hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeEmbeddingPi
section
namespace GlobalTheory.DenseEmbeddingProduct

open NumberField NumberField.InfinitePlace

theorem denseRange_embedding_pi {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by
  let Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ) :=
    fun y w ↦ Completion.extensionEmbedding w (y w)
  have hc : Continuous Φ := continuous_pi fun w ↦
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hs : Function.Surjective Φ := by
    intro f
    choose y hy using fun w : InfinitePlace E ↦
      Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)
    exact ⟨y, funext hy⟩
  have h := hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
  convert h using 1
  funext x w
  simp [Φ]

end GlobalTheory.DenseEmbeddingProduct
end

