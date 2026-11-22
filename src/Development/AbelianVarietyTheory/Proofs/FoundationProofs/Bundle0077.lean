import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution
section
open Polynomial

namespace GlobalTheory.FormalDeform

theorem constantCoeff_subst_eq {k : Type} [Field k] (a φ : PowerSeries k)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

theorem not_mem_pow_succ {A : Type} [CommRing A] [IsDedekindDomain A] {N : ℕ} {I : Type}
    [Fintype I] {D P₀ : Ideal A} {Q : I → Ideal A} {f₀ : A} (hP₀ : P₀.IsMaximal)
    (hQmax : ∀ i, (Q i).IsMaximal) (hQinj : Function.Injective Q) (hQP : ∀ i, Q i ≠ P₀)
    (hDQ : ∀ i, ¬ D ≤ Q i) (hf₀ : f₀ ≠ 0)
    (hspan : Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N) (i : I) : f₀ ∉ Q i ^ (N + 1) := by
  classical
  intro hmem
  have hQne : Q i ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_pow (Nat.succ_ne_zero N), Ideal.mem_bot] at hmem
    exact hf₀ hmem
  have hp : Prime (Q i) := Ideal.prime_of_isPrime hQne (hQmax i).isPrime
  have hdvd : Q i ^ (N + 1) ∣ Ideal.span {f₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hsplit : Ideal.span {f₀} = Q i ^ N * (P₀ * D * ∏ j ∈ Finset.univ.erase i, Q j ^ N) := by
    rw [hspan, ← Finset.mul_prod_erase Finset.univ (fun j => Q j ^ N) (Finset.mem_univ i)]
    ring
  rw [hsplit, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero N hQne)] at hdvd
  rcases hp.dvd_or_dvd hdvd with h | h
  · rcases hp.dvd_or_dvd h with h | h
    · exact hQP i (hP₀.eq_of_le (hQmax i).ne_top (Ideal.le_of_dvd h)).symm
    · exact hDQ i (Ideal.le_of_dvd h)
  · obtain ⟨j, hj, hji⟩ := (hp.dvd_finset_prod_iff _).mp h
    have hle : Q j ≤ Q i := Ideal.le_of_dvd (hp.dvd_of_dvd_pow hji)
    exact (Finset.mem_erase.mp hj).1 (hQinj ((hQmax j).eq_of_le (hQmax i).ne_top hle))

theorem coeff_map_sum {k A : Type} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (σ : A →ₐ[k] PowerSeries k) (v : Fin m → A) (c : Fin m → k) (l : ℕ) :
    ∑ j, c j * PowerSeries.coeff l (σ (v j)) = PowerSeries.coeff l (σ (∑ j, c j • v j)) := by
  simp [map_sum, map_smul]

theorem formal_deformation : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  intro k A _ _ _ _ _ _ _ N I _ V D P₀ Q f₀ hN hP₀ hyp
  obtain ⟨hVfin, hVD, hQmax, hQinj, hQP, hDQ, hDP, hf₀V, hf₀, hspan, hsurj⟩ := hyp
  classical
  have hne : Ideal.span {f₀} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf₀
  have hf₀P : f₀ ∈ P₀ := by
    have : Ideal.span {f₀} ≤ P₀ := hspan ▸ le_trans Ideal.mul_le_left Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self f₀)
  have hf₀Q : ∀ i, f₀ ∈ Q i ^ N := by
    intro i
    have h1 : Ideal.span {f₀} ≤ ∏ i, Q i ^ N := hspan ▸ Ideal.mul_le_right
    have h2 : (∏ i, Q i ^ N) ≤ Q i ^ N :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ N) (Finset.mem_univ i))
    exact h2 (h1 (Ideal.mem_span_singleton_self f₀))
  have hP₀ne : P₀ ≠ ⊥ := by
    rintro rfl; exact hf₀ ((Ideal.mem_bot).mp hf₀P)
  have hQne : ∀ i, Q i ≠ ⊥ := by
    intro i h
    have := hf₀Q i
    rw [h, Ideal.bot_pow (by omega), Ideal.mem_bot] at this
    exact hf₀ this

  obtain ⟨σ₀, π₀, -, hσ₀inj, hσ₀pow, hσ₀surj⟩ := GlobalTheory.T.exists_power_series_completion_embedding k A P₀ hP₀ hP₀ne
  have hcomp := fun i => GlobalTheory.T.exists_power_series_completion_embedding k A (Q i) (hQmax i) (hQne i)
  choose σ π hσπ hσinj hσpow hσsurj using hcomp
  have hzero : ∀ (τ : A →ₐ[k] PowerSeries k) (R : Ideal A),
      (∀ (m : ℕ) (u : A), u ∈ R ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ τ u) →
      ∀ u, u ∈ R ↔ PowerSeries.constantCoeff (τ u) = 0 := by
    intro τ R h u
    rw [← PowerSeries.X_dvd_iff, ← pow_one (PowerSeries.X : PowerSeries k), ← h 1 u, pow_one]

  set b := Module.finBasis k V with hb
  set m := Module.finrank k V with hm
  let v : Fin m → A := fun j => (b j : A)
  have hrepr : ∀ x : V, ∑ j, b.repr x j • v j = (x : A) := by
    intro x
    have h := congrArg Subtype.val (b.sum_repr x)
    rw [Submodule.coe_sum] at h
    simpa [v] using h
  let y₀ : Fin m → k := fun j => b.repr ⟨f₀, hf₀V⟩ j
  have hy₀ : ∑ j, y₀ j • v j = f₀ := hrepr ⟨f₀, hf₀V⟩
  have hlin : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k) (l : ℕ),
      ∑ j, c j * PowerSeries.coeff l (τ (v j)) = PowerSeries.coeff l (τ (∑ j, c j • v j)) :=
    fun τ c l => coeff_map_sum τ v c l
  have hlin0 : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k),
      ∑ j, c j * PowerSeries.constantCoeff (τ (v j)) =
        PowerSeries.constantCoeff (τ (∑ j, c j • v j)) := by
    intro τ c
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hlin τ c 0
  have h1 : ∑ j, y₀ j * PowerSeries.constantCoeff (σ₀ (v j)) = 0 := by
    rw [hlin0, hy₀]; exact (hzero σ₀ P₀ hσ₀pow f₀).mp hf₀P
  have h2 : ∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (σ i (v j)) = 0 := by
    intro i l hl
    rw [hlin, hy₀]
    exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
  have h3 : ∀ i, ∑ j, y₀ j * PowerSeries.coeff N (σ i (v j)) ≠ 0 := by
    intro i hc
    rw [hlin, hy₀] at hc
    apply not_mem_pow_succ hP₀ hQmax hQinj hQP hDQ hf₀ hspan i
    rw [hσpow i (N + 1) f₀, PowerSeries.X_pow_dvd_iff]
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
    · exact hc
  have h4 : ∀ (e₀ : k) (e : I → ℕ → k), ∃ h : Fin m → k,
      ∑ j, h j * PowerSeries.constantCoeff (σ₀ (v j)) = e₀ ∧
        ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (σ i (v j)) = e i l := by
    intro e₀ e
    obtain ⟨u₀, hu₀⟩ := hσ₀surj 1 (PowerSeries.C e₀)
    choose u hu using fun i => hσsurj i (N - 1) (PowerSeries.mk (e i))
    let P : Option I → Ideal A := fun o => o.elim P₀ Q
    let ex : Option I → ℕ := fun o => o.elim 1 (fun _ => N - 1)
    obtain ⟨w, hw⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) P ex
      (by
        rintro (_ | i) -
        exacts [Ideal.prime_of_isPrime hP₀ne hP₀.isPrime,
          Ideal.prime_of_isPrime (hQne i) (hQmax i).isPrime])
      (by
        rintro (_ | i) - (_ | j) - hij
        · exact absurd rfl hij
        · exact (hQP j).symm
        · exact hQP i
        · exact hQinj.ne (fun h => hij (by rw [h])))
      (fun o => o.1.elim u₀ u)
    have hw₀ : w - u₀ ∈ P₀ := by simpa [P, ex] using hw none (Finset.mem_univ _)
    have hwi : ∀ i, w - u i ∈ Q i ^ (N - 1) := fun i => by
      simpa [P, ex] using hw (some i) (Finset.mem_univ _)
    obtain ⟨v', hv'V, hv'⟩ := hsurj w
    have hv'P : v' - u₀ ∈ P₀ := by
      have : w - v' ∈ P₀ := Ideal.mul_le_left hv'
      have e1 : v' - u₀ = (w - u₀) - (w - v') := by ring
      rw [e1]; exact P₀.sub_mem hw₀ this
    have hv'Q : ∀ i, v' - u i ∈ Q i ^ (N - 1) := by
      intro i
      have h5 : (∏ i, Q i ^ (N - 1)) ≤ Q i ^ (N - 1) :=
        Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ (N - 1)) (Finset.mem_univ i))
      have : w - v' ∈ Q i ^ (N - 1) := h5 (Ideal.mul_le_right hv')
      have e1 : v' - u i = (w - u i) - (w - v') := by ring
      rw [e1]; exact Ideal.sub_mem _ (hwi i) this
    refine ⟨fun j => b.repr ⟨v', hv'V⟩ j, ?_, ?_⟩
    · rw [hlin0, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ 1 ∣ σ₀ v' - σ₀ u₀ := by
        rw [← map_sub, ← hσ₀pow 1, pow_one]; exact hv'P
      have h7 : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.C e₀ - σ₀ v' := by
        have := dvd_sub hu₀ h6
        rw [pow_one] at this
        convert this using 1; ring
      rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h7
      exact h7.symm
    · intro i l hl
      rw [hlin, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ (N - 1) ∣ σ i v' - σ i (u i) := by
        rw [← map_sub, ← hσpow i]; exact hv'Q i
      have h7 := PowerSeries.X_pow_dvd_iff.mp (dvd_sub (hu i) h6) l (by omega)
      rw [show PowerSeries.mk (e i) - σ i (u i) - (σ i v' - σ i (u i)) =
        PowerSeries.mk (e i) - σ i v' by ring, map_sub, PowerSeries.coeff_mk, sub_eq_zero] at h7
      exact h7.symm
  obtain ⟨y, a, hy0, ha0, hyξ, hyΔ⟩ := GlobalTheory.T.deform_multiple_zeros_linear_family k (Fin m) I N (fun j => σ₀ (v j))
    (fun i j => σ i (v j)) y₀ (by omega) h1 h2 h3 h4
  have hsub : ∀ i, PowerSeries.HasSubst (a i) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (ha0 i)
  let Δ : I → ℕ → A →ₗ[k] PowerSeries k := fun i l =>
    (PowerSeries.substAlgHom (R := k) (hsub i)).toLinearMap ∘ₗ
      ((PowerSeries.derivative k).toLinearMap ^ l) ∘ₗ (σ i).toLinearMap
  have hΔ : ∀ i l u, Δ i l u =
      (((PowerSeries.derivativeFun)^[l] (σ i u)).subst (a i) : PowerSeries k) := by
    intro i l u
    simp only [Δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.End.coe_pow, PowerSeries.coe_substAlgHom]
    rfl
  have hcc : ∀ i u, PowerSeries.constantCoeff (Δ i 0 u) = PowerSeries.constantCoeff (σ i u) := by
    intro i u
    rw [hΔ]
    exact constantCoeff_subst_eq _ _ (ha0 i)
  have hunit : ∀ φ : PowerSeries k, IsUnit φ ↔ PowerSeries.constantCoeff φ ≠ 0 := by
    intro φ; rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hQσ : ∀ i u, u ∈ Q i ↔ PowerSeries.constantCoeff (σ i u) = 0 :=
    fun i => hzero (σ i) (Q i) (hσpow i)
  have hPσ : ∀ u, u ∈ P₀ ↔ PowerSeries.constantCoeff (σ₀ u) = 0 := hzero σ₀ P₀ hσ₀pow
  refine ⟨σ₀, Δ, m, v, y, hσ₀inj, ?_, ?_, ?_, ?_, ?_, ?_, hyξ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hΔ, Function.iterate_zero, id, map_one, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro i l u w
    simp only [hΔ, map_mul]
    exact GlobalTheory.T.iterate_derivativeFun_mul_subst_leibniz k (a i) _ _ l (ha0 i)
  · intro i
    refine ⟨π i, ?_⟩
    have hX : PowerSeries.derivativeFun (PowerSeries.X : PowerSeries k) = 1 :=
      PowerSeries.derivative_X
    rw [hΔ, Function.iterate_one, hσπ, hX, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro j; exact (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · by_contra hcon
    push_neg at hcon
    have hz : ∀ j, y₀ j = 0 := by
      intro j
      have := hcon j
      rwa [hunit, hy0, not_not] at this
    apply hf₀
    rw [← hy₀]
    simp [hz]
  · intro i l hl
    simpa only [hΔ] using hyΔ i l hl
  · intro i i' hii'
    have hle : ¬ Q i' ≤ Q i := fun h =>
      hii' (hQinj ((hQmax i').eq_of_le (hQmax i).ne_top h)).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, hcc, (hQσ i' u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    have hle : ¬ P₀ ≤ Q i := fun h => hQP i (hP₀.eq_of_le (hQmax i).ne_top h).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, (hPσ u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp (hDQ i)
    refine ⟨u, hu', ?_⟩
    rw [hunit, hcc]
    exact fun h => hu ((hQσ i u).mpr h)
  · obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hDP
    refine ⟨u, hu', ?_⟩
    rw [hunit]
    exact fun h => hu ((hPσ u).mpr h)

end GlobalTheory.FormalDeform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGeneratorStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_improved_approx_kummer_generator : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 → (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F → v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤ max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  first | exact @GlobalTheory.AlmostEt.exists_approxRoot_step | exact GlobalTheory.AlmostEt.exists_approxRoot_step | (intros; apply GlobalTheory.AlmostEt.exists_approxRoot_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_int_exponent_cyclotomic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ) (hM : 0 < M) (hd : l ^ n ∣ M) :
    ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧
      (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := rootsOfUnity.integer_power_of_ringEquiv M s.toRingEquiv
  have hs : ∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e := by
    intro ζ hζ
    have h := he hζ.toRootsOfUnity
    simpa [Units.val_zpow_eq_zpow_val] using h
  refine ⟨e, hs, ?_⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hη : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have hsη : s (ζ ^ k) = (ζ ^ k) ^ e := by
    rw [map_pow, hs ζ hζ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  set c := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hc
  have hpow : (ζ ^ k) ^ (l ^ n) = 1 := hη.pow_eq_one
  have hspec := cyclotomicCharacter.spec (L := Ω) l s.toRingEquiv (ζ ^ k) hpow
  have heq : (ζ ^ k) ^ e = (ζ ^ k) ^ (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hsη, zpow_natCast]
    exact hspec
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ e - (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hη.zpow_eq_one_iff_dvd, zpow_sub₀ (hη.ne_zero (NeZero.ne _)), heq, div_self]
    exact zpow_ne_zero _ (pow_ne_zero _ (hζ.ne_zero (NeZero.ne _)))
  have hz : (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ((e : ℤ_[l]) - c) = 0 := by
    rw [map_sub, map_intCast, hc]
    rw [sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at this
    rw [this]
    simp
  have hmem : (e : ℤ_[l]) - c ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := hz
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow] at hmem
  exact hmem

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOneStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  first | exact @GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | exact GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' | (intros; apply GlobalTheory.AlmostEt.exists_integer_coset_trace_eq' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithfulStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  first | exact @GlobalTheory.AlmostEt.exists_lagrange_resolvent | exact GlobalTheory.AlmostEt.exists_lagrange_resolvent | (intros; apply GlobalTheory.AlmostEt.exists_lagrange_resolvent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslateStatement
section
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  first | exact @GlobalTheory.AdelicMatLat.exists_lattice_integral | exact GlobalTheory.AdelicMatLat.exists_lattice_integral | (intros; apply GlobalTheory.AdelicMatLat.exists_lattice_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.FunctionFieldPrimitive

open Polynomial

open scoped MatrixGroups TensorProduct in
open Matrix in
open Polynomial in

theorem _root_.GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive {F : Type} [Field F] [CharZero F]
    {L : Type} [Field L]
    [Algebra F L] (t : L) (ht : Transcendental F t)
    (hfin : FiniteDimensional (IntermediateField.adjoin F {t}) L) :
    ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧
      Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧
      ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F),
        Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  have htK : t ∈ IntermediateField.adjoin F {t} := IntermediateField.mem_adjoin_simple_self F t
  have hne : ∀ p : Polynomial F, p ≠ 0 → Polynomial.aeval t p ≠ 0 := fun p hp h =>
    ht ⟨p, hp, h⟩
  have hden : ∀ y ∈ IntermediateField.adjoin F {t}, ∃ s : Polynomial F, s ≠ 0 ∧
      ∃ r : Polynomial F, Polynomial.aeval t s * y = Polynomial.aeval t r := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff F y).1 hy
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, 0, by simp [hs]⟩
    · exact ⟨s, hs, r, by rw [mul_div_cancel₀ _ (hne s hs)]⟩
  have hcomm : ∀ p : Polynomial F,
      ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p :
        IntermediateField.adjoin F {t}) : L) = Polynomial.aeval t p := fun p =>
    (Polynomial.aeval_algHom_apply (IntermediateField.adjoin F {t}).val
      (⟨t, htK⟩ : IntermediateField.adjoin F {t}) p).symm
  letI algK : Algebra (Polynomial F) (IntermediateField.adjoin F {t}) :=
    (Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t})).toRingHom.toAlgebra
  letI algL : Algebra (Polynomial F) L := (Polynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial F) (IntermediateField.adjoin F {t}) L :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomm p).symm
  haveI : Algebra.IsAlgebraic (Polynomial F) (IntermediateField.adjoin F {t}) := by
    constructor
    intro k
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C r, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun P => Polynomial.coeff P 1) h
      simp at h1
      exact hs h1
    · apply Subtype.val_injective
      rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
      show ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) s :
          IntermediateField.adjoin F {t}) : L) * k -
        ((Polynomial.aeval (⟨t, htK⟩ : IntermediateField.adjoin F {t}) r :
          IntermediateField.adjoin F {t}) : L) = 0
      rw [hcomm, hcomm, hsr, sub_self]
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin F {t}) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (Polynomial F) L :=
    Algebra.IsAlgebraic.trans (Polynomial F) (IntermediateField.adjoin F {t}) L
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (IntermediateField.adjoin F {t}) L
  obtain ⟨y, hy0, hyint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial F) θ).exists_integral_multiple
  have hωdef : y • θ = Polynomial.aeval t y * θ := Algebra.smul_def y θ
  have hyK : Polynomial.aeval t y ∈ IntermediateField.adjoin F {t} := by
    rw [← hcomm]; exact Subtype.property _
  have htop : IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} = ⊤ := by
    rw [eq_top_iff, ← hθ, IntermediateField.adjoin_simple_le_iff]
    have hθeq : θ = (Polynomial.aeval t y)⁻¹ * (y • θ) := by
      rw [hωdef, inv_mul_cancel_left₀ (hne y hy0)]
    have hmem : (Polynomial.aeval t y)⁻¹ * (y • θ) ∈
        IntermediateField.adjoin (IntermediateField.adjoin F {t}) {y • θ} :=
      mul_mem (inv_mem (IntermediateField.algebraMap_mem _
        (⟨Polynomial.aeval t y, hyK⟩ : IntermediateField.adjoin F {t})))
        (IntermediateField.mem_adjoin_simple_self _ (y • θ))
    rwa [← hθeq] at hmem
  refine ⟨minpoly (Polynomial F) (y • θ), y • θ, minpoly.monic hyint,
    minpoly.irreducible hyint, minpoly.aeval _ _, ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin (IntermediateField.adjoin F {t}) {y • θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (y • θ)), htop]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨1, one_ne_zero, Polynomial.X, by simp⟩
  | algebraMap k =>
    obtain ⟨s, hs, r, hsr⟩ := hden k.1 k.2
    exact ⟨s, hs, Polynomial.C r, by rw [Polynomial.eval₂_C]; exact hsr⟩
  | add a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, Polynomial.C Q₂ * R₁ + Polynomial.C Q₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_C, ← h₁, ← h₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨Q₁, hQ₁, R₁, h₁⟩ := ha
    obtain ⟨Q₂, hQ₂, R₂, h₂⟩ := hb
    refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, R₁ * R₂, ?_⟩
    rw [Polynomial.eval₂_mul, ← h₁, ← h₂, map_mul]
    ring

end GlobalTheory.FunctionFieldPrimitive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInteStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  first | exact @GlobalTheory.K5.algSpan_reprInd | exact GlobalTheory.K5.algSpan_reprInd | (intros; apply GlobalTheory.K5.algSpan_reprInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegersStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x} := by
  first | exact @GlobalTheory.K5.ReprSpan.exists_mul_mem_span | exact GlobalTheory.K5.ReprSpan.exists_mul_mem_span | (intros; apply GlobalTheory.K5.ReprSpan.exists_mul_mem_span <;> assumption)
end

