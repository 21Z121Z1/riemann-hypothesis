import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspace
section
open PowerSeries

namespace GlobalTheory

theorem diagonal_entry_of_semilinear_mod_subspace : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  intro F _ n θ A W' W f' e' f e w' w k' k m d α hξ hT hf' hf he hTf hTe
  have hx : ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := F)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  set x : LaurentSeries F := ((PowerSeries.X : PowerSeries F) : LaurentSeries F) with hxdef
  set ξ : LaurentSeries F := ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) with hξdef
  obtain ⟨N, j, hj⟩ : ∃ N j : ℕ, (j : ℤ) = (N : ℤ) + k' := ⟨k'.natAbs, (k'.natAbs + k').toNat, by omega⟩
  set a : PowerSeries F := (w' : PowerSeries F) * PowerSeries.X ^ j with hadef
  have ha : ((a : PowerSeries F) : LaurentSeries F) = (w' : LaurentSeries F) * x ^ N * x ^ k' := by
    rw [hadef, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hx, zpow_natCast, mul_assoc]
  have hθa : ((θ a : PowerSeries F) : LaurentSeries F) = ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ξ ^ N * ξ ^ k' := by
    rw [hadef, map_mul, map_pow, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hξ, zpow_natCast, mul_assoc]
  let y : Fin n → PowerSeries F := fun c => PowerSeries.X ^ N * f' c - a * e' c
  have hy : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) ∈ W' := by
    have : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) = (x ^ N) • ((fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * x ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F))) := by
      funext c
      simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, ha, ← hxdef]
      ring
    rw [this]; exact W'.smul_mem _ hf'
  have hvec : A.mulVec (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • A.mulVec (fun c => θ (f' c)) - θ a • A.mulVec (fun c => θ (e' c)) := by
    have : (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • (fun c => θ (f' c)) - θ a • (fun c => θ (e' c)) := by
      ext c; simp [y]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hTy := hT y hy
  set P : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (f' c)) i : PowerSeries F) : LaurentSeries F) with hP
  set Q : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (e' c)) i : PowerSeries F) : LaurentSeries F) with hQ
  set E : Fin n → LaurentSeries F := fun i => ((e i : PowerSeries F) : LaurentSeries F) with hE
  set Fv : Fin n → LaurentSeries F := fun i => ((f i : PowerSeries F) : LaurentSeries F) with hFv
  have h4 : ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q ∈ W := by
    have : (fun i => ((A.mulVec (fun c => θ (y c)) i : PowerSeries F) : LaurentSeries F)) = ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q := by
      funext i
      simp only [hvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, hP, hQ, hξdef]
    rw [← this]; exact hTy
  set c : LaurentSeries F := ((θ a : PowerSeries F) : LaurentSeries F) * α - x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * x ^ k with hc
  have hcE : c • E ∈ W := by
    have h := W.sub_mem (W.sub_mem (W.add_mem (W.smul_mem (x ^ m * ξ ^ N) hTf) (W.smul_mem (x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F)) hf)) (W.smul_mem (((θ a : PowerSeries F) : LaurentSeries F)) hTe)) (W.smul_mem (x ^ m) h4)
    convert h using 1
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hc, hP, hQ, hE, hFv]
    ring
  have hc0 : c = 0 := by
    by_contra hne
    apply he
    have := W.smul_mem c⁻¹ hcE
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hξN : ξ ^ N ≠ 0 := pow_ne_zero _ hξ
  rw [hc, hθa, sub_eq_zero] at hc0
  apply mul_right_cancel₀ hξN
  linear_combination hc0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
section
open NumberField

namespace GlobalTheory

theorem exists_trace_dual_system (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (m : ℕ) (ω : Fin m → 𝓞 L) (η : Fin m → L),
      (∀ i, η i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ t : L, t = ∑ i, algebraMap K L (Algebra.trace K L (η i * t)) * (ω i : L) := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) L :=
    IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let f : Fin m → Module.Dual K L := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ G)
  have hf : ∀ i (a : 𝓞 L), f i (a : L) = algebraMap (𝓞 K) K (G a i) := fun i a =>
    hbc.lift_eq _ a
  let η : Fin m → L := fun i =>
    ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm (f i)
  have hη : ∀ i t, Algebra.trace K L (η i * t) = f i t := fun i t =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate K L) (f i) t
  refine ⟨m, fun i => F (Pi.single i 1), η, fun i => ?_, fun t => ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨G b i, ?_⟩
    rw [Algebra.traceForm_apply, hη]
    exact (hf i b).symm
  · simp_rw [hη]
    have h := hbc.algHom_ext (LinearMap.id : L →ₗ[K] L)
      (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (fun a => by
        have ha : a = ∑ i, G a i • F (Pi.single i 1) := by
          have h1 : a = F (G a) := (LinearMap.congr_fun hFG a).symm
          conv_lhs => rw [h1, LinearMap.pi_apply_eq_sum_univ]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          ext j
          simp [Pi.single_apply, eq_comm]
        change (a : L) = (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (a : L)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hf, algebraMap_smul]
        conv_lhs => rw [ha]
        change algebraMap (𝓞 L) L _ = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap.map_smul _ _)
    have h2 := LinearMap.congr_fun h t
    simpa [LinearMap.sum_apply, Algebra.smul_def] using h2

open NumberField in
private theorem exists_integral_traceDual_expansion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ (N : ℕ) (e : Fin N → 𝓞 L) (c : Fin N → L),
      (∀ k, c k ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ y : L, y = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) • c k := by
  classical
  obtain ⟨N, F, hF⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  have : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  have hP : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨h, hh⟩ := Module.projective_lifting_property F LinearMap.id hF
  obtain ⟨e, hdec⟩ : ∃ e : Fin N → 𝓞 L, ∀ b : 𝓞 L, b = ∑ k, h b k • e k := by
    refine ⟨fun k => F (Pi.single k 1), fun b => ?_⟩
    have hb := LinearMap.congr_fun hh b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb
    conv_lhs => rw [← hb, ← Finset.univ_sum_single (h b)]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (h b k) : Fin N → 𝓞 K) = h b k • Pi.single k 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  let φ : Fin N → (𝓞 L →ₗ[𝓞 K] 𝓞 K) := fun k => LinearMap.proj k ∘ₗ h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin N → Module.Dual K L,
      ∀ k (b : 𝓞 L), ψ k (algebraMap (𝓞 L) L b) = algebraMap (𝓞 K) K (h b k) :=
    ⟨fun k => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K) K
      (φ k), fun k b => IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K)
      (φ k) b⟩
  have hB := traceForm_nondegenerate K L
  obtain ⟨c, hc⟩ : ∃ c : Fin N → L, ∀ k y, Algebra.trace K L (c k * y) = ψ k y :=
    ⟨fun k => ((Algebra.traceForm K L).toDual hB).symm (ψ k), fun k y => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _⟩
  clear hh hF F this hP
  have hexpO : ∀ b : 𝓞 L,
      algebraMap (𝓞 L) L b = ∑ k, ψ k (algebraMap (𝓞 L) L b) • algebraMap (𝓞 L) L (e k) := by
    intro b
    conv_lhs => rw [hdec b]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.smul_def]
  have hexp : ∀ y : L, y = ∑ k, ψ k y • algebraMap (𝓞 L) L (e k) := by
    intro y
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) y
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hy : y = (algebraMap (𝓞 K) K a)⁻¹ • algebraMap (𝓞 L) L b := by
      rw [← hbs, ← has, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, mul_comm, ← Algebra.smul_def, smul_smul,
        inv_mul_cancel₀ ha0, one_smul]
    clear hbs has
    rw [hy]
    conv_lhs => rw [hexpO b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_assoc]
  refine ⟨N, e, c, fun k => ?_, fun y => ?_⟩
  · rw [Submodule.mem_traceDual]
    rintro _ ⟨b, rfl⟩
    rw [Algebra.traceForm_apply]
    exact ⟨h b k, by simpa [hψ, Algebra.smul_def, mul_comm] using (hc k (algebraMap (𝓞 L) L b)).symm⟩
  · rw [← sub_eq_zero]
    refine hB.1 _ fun u => ?_
    have h1 : Algebra.trace K L (y * u) = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) *
        Algebra.trace K L (c k * u) := by
      conv_lhs => rw [hexp u]
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm y]; ring
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Algebra.traceForm_apply, smul_eq_mul, h1]
    rw [sub_eq_zero]

open NumberField in

theorem _root_.GlobalTheory.differentIdeal_smul_mem_span_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ) (M : Submodule (𝓞 L) (Fin n → L)), (∀ (σ : L ≃ₐ[K] L), ∀ x ∈ M, (fun i => σ (x i)) ∈ M) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∀ x ∈ M, d • x ∈ Submodule.span (𝓞 L) {y : Fin n → L | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K L (y0 i)} := by
  intro K L _ _ _ _ _ _ n M hM d hd x hx
  classical
  obtain ⟨N, e, c, hcD, hswap⟩ := exists_integral_traceDual_expansion K L
  have hdL : algebraMap (𝓞 L) L d ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
    rw [← coeSubmodule_differentIdeal (𝓞 K) K (𝓞 L)]
    exact (IsLocalization.mem_coeSubmodule _ _).mpr ⟨d, hd, rfl⟩
  have hdc : ∀ k, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * c k := fun k =>
    Submodule.mem_one.mp (Submodule.mem_div_iff_forall_mul_mem.mp hdL _ (hcD k))
  choose r hr using hdc
  set t : Fin N → Fin n → L :=
    fun k i => algebraMap K L (Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i)) with ht
  have htM : ∀ k, t k ∈ M := by
    intro k
    have : t k = ∑ σ : L ≃ₐ[K] L, fun i => σ ((e k • x) i) := by
      funext i
      simp only [ht, Finset.sum_apply, Pi.smul_apply, trace_eq_sum_automorphisms, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun σ _ => hM σ _ (M.smul_mem _ hx)
  have hdx : d • x = ∑ k, r k • t k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ht, Algebra.smul_def, hr]
    conv_lhs => rw [hswap (x i)]
    simp only [Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨htM k, fun i => Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i), rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogb
section
namespace GlobalTheory

theorem digit_le_logb_succ (p d : ℕ) (hp : 1 < p) (hd : d < p) :
    (d : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((d : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdle : (d : ℝ) ≤ (p : ℝ) - 1 := by
    have h : ((d : ℝ) + 1) ≤ p := by exact_mod_cast hd
    linarith
  set t : ℝ := (d : ℝ) / ((p : ℝ) - 1) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) hpm.le
  have ht1 : t ≤ 1 := (div_le_one hpm).2 hdle
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simp only [Set.mem_Ioi]; linarith : (p : ℝ) ∈ Set.Ioi 0)
    (sub_nonneg.2 ht1) ht0 (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have heq : (1 - t) + t * p = (d : ℝ) + 1 := by
    rw [ht]; field_simp; ring
  rw [heq] at hconc
  have hmul : (d : ℝ) * Real.log p = ((p : ℝ) - 1) * (t * Real.log p) := by
    rw [ht]; field_simp
  rw [Real.logb, ← mul_div_assoc, le_div_iff₀ hlogp, hmul]
  exact mul_le_mul_of_nonneg_left hconc hpm.le

theorem digits_sum_le_logb (p n : ℕ) (hp : p.Prime) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hp.one_lt hn, List.sum_cons, Nat.cast_add]
      have hdiv := Nat.div_add_mod n p
      have hdp : n % p < p := Nat.mod_lt n hp.pos
      have ihq := ih (n / p) (Nat.div_lt_self hn hp.one_lt)
      have hd := digit_le_logb_succ p (n % p) hp.one_lt hdp
      have hprod : (((n / p : ℕ) : ℝ) + 1) * (((n % p : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
        have h1 : (n / p + 1) * (n % p + 1) ≤ n + 1 := by
          have : (n / p) * (n % p + 1) ≤ (n / p) * p := Nat.mul_le_mul_left _ hdp
          nlinarith
        exact_mod_cast h1
      have hlog : Real.logb p (((n / p : ℕ) : ℝ) + 1) + Real.logb p (((n % p : ℕ) : ℝ) + 1)
          ≤ Real.logb p ((n : ℝ) + 1) := by
        rw [← Real.logb_mul (by positivity) (by positivity)]
        exact Real.logb_le_logb_of_le hp1 (by positivity) hprod
      nlinarith [mul_le_mul_of_nonneg_left hlog hpm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureLeOfSpecializes
section
namespace GlobalTheory.ClosureDimensionSpecialization

open Order TopologicalSpace Topology

theorem dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by
  intro X z w j hzw hne hdim
  have hsub : closure ({w} : Set X) ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw))
      isClosed_closure
  have hind : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  haveI : IrreducibleSpace (closure ({z} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  let top : IrreducibleCloseds (closure ({z} : Set X)) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top := by
    intro a
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro h
    have hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈
        (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) := by
      rw [h]; exact Set.mem_univ _
    have hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} :=
      isClosed_closure.preimage continuous_subtype_val
    have hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆
        {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} := by
      rw [IrreducibleCloseds.coe_map]
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hwz : w ⤳ z := specializes_iff_mem_closure.mpr (hsub' hz)
    exact hne ((hzw.antisymm hwz).eq).symm
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have h1 : height a + 1 ≤ height top :=
    calc height a + 1 ≤ height (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a) + 1 := by
          gcongr
          exact height_le_height_apply_of_strictMono _
            (IrreducibleCloseds.map_strictMono_of_isInducing hind) a
      _ ≤ height top := height_add_one_le (hlt a)
  have h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞) := by
    rw [← hdim]; exact height_le_krullDim top
  have h3 : height top ≤ ((j : ℕ∞) + 1) := by exact_mod_cast h2
  have h4 : height a ≤ (j : ℕ∞) :=
    (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)
  exact_mod_cast h4

end GlobalTheory.ClosureDimensionSpecialization
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
section
namespace GlobalTheory

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  intro K _ _ x hx
  classical
  have hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact Ideal.absNorm_mem _
  have hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hx b
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]
  have hprod := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ
    (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [map_natCast] at hα
  have hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x) := by
    rw [← hα]
    exact α.isIntegral_coe
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h]
    simpa using hint
  · rw [h]
    simpa using hint.neg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivMemOfMulPowDivMemOfRegularPair
section
namespace GlobalTheory

theorem div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by
  induction N with
  | zero => intro g _ hg; simpa using hg
  | succ N ih =>
    intro g hg hgN
    apply ih g hg
    apply h _ (O.mul_mem hg (O.pow_mem ht N))
    rwa [mul_assoc, ← pow_succ]

theorem regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by
  intro K _ O s t hs ht hs0 h m N
  induction m with
  | zero => intro g hg _; simpa using hg
  | succ m ih =>
    intro g hg hgN
    have h1 : g * t ^ N / s ∈ O := by
      have h2 := O.mul_mem hgN (O.pow_mem hs m)
      have e : g * t ^ N / s ^ (m + 1) * s ^ m = g * t ^ N / s := by
        field_simp
        ring
      rwa [e] at h2
    have h3 := div_mem_of_mul_pow_div_mem_of_regularPair K O s t ht h N g hg h1
    have e1 : g / s * t ^ N / s ^ m = g * t ^ N / s ^ (m + 1) := by
      field_simp
      ring
    have e2 : g / s / s ^ m = g / s ^ (m + 1) := by
      field_simp
      ring
    rw [← e2]
    exact ih _ h3 (by rwa [e1])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionAlgebraOrderNoSmallLattice
section
open NumberField

namespace GlobalTheory

theorem divAlg_clear_denominators {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (v : B) (hv : v ∈ Submodule.span ℚ (Set.range ι)) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : O, ι c = (n : ℚ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    exact ⟨1, one_pos, o, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, c₁, hc₁⟩ := hx
    obtain ⟨n₂, hn₂, c₂, hc₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul,
      smul_smul, smul_add]
    push_cast
    rw [mul_comm (n₂ : ℚ) (n₁ : ℚ)]
  | smul q x _ hx =>
    obtain ⟨n, hn, c, hc⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩
    rw [map_mul, map_intCast, hc, smul_smul]
    rw [show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]
    congr 1
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

theorem divAlg_smul_injective {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (hunit : ∀ x : B, x ≠ 0 → IsUnit x) (hinj : Function.Injective ι)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (ρ : O →+* Module.End ℤ X)
    (x : X) (hx : x ≠ 0) (a : O) (ha : ρ a x = 0) : a = 0 := by
  by_contra h0
  have hιa : ι a ≠ 0 := fun h => h0 (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := hunit _ hιa
  obtain ⟨n, hn, c, hc⟩ := divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)
  have hca : c * a = (n : O) := by
    apply hinj
    rw [map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul,
      Algebra.smul_def, mul_one]
    simp
  have h1 : ρ (c * a) x = 0 := by rw [map_mul, Module.End.mul_apply, ha, map_zero]
  rw [hca, map_natCast] at h1
  have h2 : (n : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    simpa [Module.End.natCast_apply] using h1
  rcases smul_eq_zero.mp h2 with h | h
  · omega
  · exact hx h

end GlobalTheory

namespace GlobalTheory

theorem divAlg_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B]
    (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι →
    Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B →
    Module.finrank ℤ X = 0 := by
  intro B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt
  by_contra hne
  have hnt : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)

  let φ : O →ₗ[ℤ] X := (AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha
  let ι' : O →ₗ[ℤ] B := ι.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ι)
  rw [hspan] at hbspan
  let e := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  choose f hf using fun i : b => hbsub i.2
  have li1 : LinearIndependent ℤ (fun i : b => (i : B)) := hbli.restrict_scalars' ℤ
  have li2 : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp ι'
    convert li1 using 1
    funext i
    exact hf i
  have li3 : LinearIndependent ℤ (φ ∘ f) := li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hc := li3.cardinal_le_rank
  rw [Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hc
  have := Nat.cast_le.mp hc
  omega

end GlobalTheory
end

