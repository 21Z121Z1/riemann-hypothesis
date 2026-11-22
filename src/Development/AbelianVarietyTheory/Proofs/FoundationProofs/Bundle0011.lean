import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentVecMulOfSpanRat
section
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem linearIndependent_vecMul_of_span_rat :
    ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  intro E _ _ R _ _ _ τ hτ hrk n ι _ u hcard hu g
  classical
  have hq : ∀ c : ℚ, τ (algebraMap ℚ E c) = algebraMap ℝ R (algebraMap ℚ ℝ c) := by
    intro c
    have : τ.comp (algebraMap ℚ E) = (algebraMap ℝ R).comp (algebraMap ℚ ℝ) :=
      Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* R => f c) this
  set V : Submodule ℝ (Fin n → R) :=
    Submodule.span ℝ (Set.range fun k => (fun i => τ (u k i))) with hV
  have h1 : ∀ x : Fin n → E, (fun i => τ (x i)) ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range u) := by rw [hu]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero =>
      have : (fun i => τ ((0 : Fin n → E) i)) = 0 := by ext i; simp
      rw [this]; exact V.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => τ ((x + y) i)) = (fun i => τ (x i)) + (fun i => τ (y i)) := by
        ext i; simp
      rw [this]; exact V.add_mem hx hy
    | smul c x _ hx =>
      have : (fun i => τ ((c • x) i)) = (algebraMap ℚ ℝ c) • (fun i => τ (x i)) := by
        ext i
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hq]
      rw [this]; exact V.smul_mem _ hx
  have h2 : ∀ (i : Fin n) (r : R), Pi.single i r ∈ V := by
    intro i r
    have hle : Submodule.span ℝ (Set.range τ) ≤
        V.comap (LinearMap.single ℝ (fun _ : Fin n => R) i) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      have := h1 (Pi.single i e)
      have h' : (fun j => τ ((Pi.single i e : Fin n → E) j)) = Pi.single i (τ e) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      rw [h'] at this
      exact this
    have hr : r ∈ Submodule.span ℝ (Set.range τ) := by rw [hτ]; trivial
    exact hle hr
  have h3 : ∀ y : Fin n → R, y ∈ V := by
    intro y
    rw [← Finset.univ_sum_single y]
    exact V.sum_mem fun i _ => h2 i _
  let φ : (Fin n → R) →ₗ[ℝ] (Fin n → R) :=
    { toFun := fun v => v ᵥ* g.1
      map_add' := fun v w => Matrix.add_vecMul _ _ _
      map_smul' := fun c v => Matrix.smul_vecMul _ _ _ }
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro y _
    have hy : y = φ (y ᵥ* (g⁻¹).1) := by
      simp [φ, Matrix.vecMul_vecMul]
    have hm : φ (y ᵥ* (g⁻¹).1) ∈ V.map φ := Submodule.mem_map_of_mem (h3 _)
    rw [hV, Submodule.map_span, ← Set.range_comp] at hm
    rw [hy]
    exact hm
  · rw [hcard, Module.finrank_pi_fintype, ← hrk]
    simp [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwist
section
open Complex Filter Topology

namespace GlobalTheory

theorem lseries_shift_twist (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) :
    LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term]
  split_ifs with hn
  · rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast [Nat.cast_sub he]
    ring
  have h1 : (n : ℂ) ^ (e - 1) ≠ 0 := pow_ne_zero _ hn'
  have h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [key]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSquaresEq
section
open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSquares_term (e : ℕ) (c : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (d : ℕ) :
    LSeries.term (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
        c (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) (d * d)
      = LSeries.term c ((e + 1 : ℕ) + 2 * s) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]
  simp only [Nat.sqrt_eq, if_true]
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc,
    ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]
  congr 2
  have h3 : 1 ≤ 3 * e := by omega
  push_cast [Nat.cast_sub h3]
  ring

theorem lseriesSquares_eq : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  intro e χ ψ θ s he hs hb
  have hinj : Function.Injective (fun d : ℕ => d * d) := fun a b h => Nat.mul_self_inj.mp h
  have hterm := lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he
  set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
    χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) →
      LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0 := by
    intro n hn
    have hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n) := fun h => hn ⟨_, h⟩
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [hf, hn']
  have hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := hb n
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
    · have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp
      linarith
  constructor
  · refine (hinj.summable_iff hzero).mp ?_
    exact (show Summable _ from hsum).congr fun d => (hterm d).symm
  · unfold LSeries
    rw [← hinj.tsum_eq (fun n hn => by
      by_contra h
      exact hn (hzero n h))]
    exact tsum_congr hterm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummable
section
open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSummable_twist_pow_of_sq_summable :
    ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ g s he hs hψ hg
  have h1 := hg s hs
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hx : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
    set x : ℝ := (n : ℝ) with hxdef
    set A : ℝ := ‖g n‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    set p : ℝ := x ^ (-(2 * (k : ℝ) + 3 + s) / 2) with hp
    set q : ℝ := x ^ (-(1 + s) / 2) with hq
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by positivity
    have e1 : A ^ 2 / x ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s) = (A * p) ^ 2 := by
      rw [mul_pow, hp, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, div_eq_mul_inv,
        ← Real.rpow_neg hx.le]
      congr 2
      push_cast
      ring
    have e2 : 1 / x ^ (1 + s) = q ^ 2 := by
      rw [hq, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, one_div,
        ← Real.rpow_neg hx.le]
      congr 1
      push_cast
      ring
    have e3 : x ^ k / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = p * q := by
      rw [hp, hq, ← Real.rpow_natCast x k, ← Real.rpow_sub hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    have e4 : ‖ψ n‖ * x ^ k * A / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = ‖ψ n‖ * (A * p * q) := by
      rw [mul_assoc A, ← e3]; ring
    rw [e4]
    have h3 : ‖ψ n‖ * (A * p * q) ≤ A * p * q :=
      mul_le_of_le_one_left (by positivity) (hψ n)
    have h4 : 0 ≤ A * p * q := by positivity
    nlinarith [sq_nonneg (A * p - q)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixInvEntriesBounded
section
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem matrix_inv_entries_bounded (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ) (hG : Continuous G) (hU : ∀ c, G c ≠ 0 → IsUnit c) (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  haveI : ProperSpace R := FiniteDimensional.proper_real R
  haveI : CompleteSpace R := FiniteDimensional.complete ℝ R
  set K : Set (Matrix (Fin n) (Fin n) R) := Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : R) B)) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hmemK : ∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → c ∈ K := by
    intro c h i _ j _
    simpa [Metric.mem_closedBall, dist_zero_right] using h i j
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn hG.continuousOn
  set K' := K ∩ {c | ε ≤ G c} with hK'
  have hK'c : IsCompact K' := hKc.inter_right (isClosed_le continuous_const hG)
  let f : Matrix (Fin n) (Fin n) R → (Fin n → Fin n → R) := fun c => fun i j => (c⁻¹) i j
  have hf : ContinuousOn f K' := by
    intro c hc
    have hu : IsUnit c := hU c (ne_of_gt (lt_of_lt_of_le hε hc.2))
    have hdet : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hu
    obtain ⟨u, hu'⟩ := hdet
    have h1 : ContinuousAt Ring.inverse c.det := by
      rw [← hu']; exact NormedRing.inverse_continuousAt u
    exact (continuousAt_matrix_inv c h1).continuousWithinAt
  obtain ⟨C2, hC2⟩ := hK'c.exists_bound_of_continuousOn hf
  refine ⟨max C1 C2, ?_, ?_⟩
  · intro c hc
    exact le_trans (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC1 c (hmemK c hc))) (le_max_left _ _)
  · intro c hc hGc i j
    have hm : c.1 ∈ K' := ⟨hmemK _ hc, hGc⟩
    have h2 := hC2 _ hm
    have h3 : ‖f c.1 i j‖ ≤ ‖f c.1‖ := le_trans (norm_le_pi_norm (f c.1 i) j) (norm_le_pi_norm (f c.1) i)
    rw [Matrix.coe_units_inv]
    exact le_trans (le_trans h3 h2) (le_max_right _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
section
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem mem_adjoin_div_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  intro R Ω _ _ _ _ _ _ _ hinj S x hx
  set A := Algebra.adjoin R S with hA
  set F : Subfield Ω := Subfield.closure (A : Set Ω) with hF
  have hAF : ∀ y ∈ A, y ∈ F := fun y hy => Subfield.subset_closure hy
  let φ : R →+* F := (algebraMap R Ω).codRestrict F (fun r => hAF _ (A.algebraMap_mem r))
  have hφ : ∀ r, algebraMap F Ω (φ r) = algebraMap R Ω r := fun r => rfl
  haveI : Algebra.IsAlgebraic F Ω := by
    constructor
    intro y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) y
    refine ⟨p.map φ, ?_, ?_⟩
    · intro h
      apply hp0
      have hφi : Function.Injective φ := by
        intro a b hab
        apply hinj
        have := congrArg (algebraMap F Ω) hab
        simpa [hφ] using this
      exact (Polynomial.map_eq_zero_iff hφi).mp h
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      rw [Polynomial.aeval_def] at hp
      convert hp using 2
      exact RingHom.ext hφ
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfix : ∀ f : Ω ≃ₐ[F] Ω, f x = x := by
    intro f
    have hfF : ∀ y ∈ F, f y = y := fun y hy => f.commutes ⟨y, hy⟩
    let g : Ω ≃ₐ[R] Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => hfF _ (hAF _ (A.algebraMap_mem r)))
    exact hx g (fun s hs => hfF _ (hAF _ (Algebra.subset_adjoin hs)))
  have hxF : x ∈ F := by
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) x).mpr hfix
    rw [← hy]; exact y.2
  obtain ⟨b, hb, c, hc, hbc⟩ := Subfield.mem_closure_iff.mp hxF
  have hcl : ∀ y ∈ Subring.closure (A : Set Ω), y ∈ A := fun y hy =>
    (Subring.closure_le (t := A.toSubring)).mpr (fun z hz => hz) hy
  by_cases hc0 : c = 0
  · refine ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, ?_⟩
    rw [← hbc, hc0]; simp
  · exact ⟨b, hcl _ hb, c, hcl _ hc, hc0, hbc.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMaximalPowOfJetsVanish
section
open Polynomial

namespace GlobalTheory

theorem mem_pow_of_jets_vanish (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) =
      ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w))
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w; rw [hL 0 hN0]; simp
  have halg : ∀ c : k, Δ 0 (algebraMap k A c) = c := by
    intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, h01, smul_eq_mul, mul_one]
  let φ : A →+* k :=
    { toFun := Δ 0, map_one' := h01, map_mul' := hmul0, map_zero' := map_zero _,
      map_add' := map_add _ }
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, halg c⟩
  have hQmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hmemQ : ∀ u, u ∈ RingHom.ker φ ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  set Q := RingHom.ker φ with hQ
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    simp [Finset.sum_range_succ, h01] at this
    linear_combination this
  have ha : ∀ m, ∀ u ∈ Q ^ m, ∀ l < m, l < N → Δ l u = 0 := by
    intro m
    induction m with
    | zero => intro u _ l hl; omega
    | succ m ih =>
      intro u hu l hlm hlN
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun u => Δ l u = 0) hu ?_ ?_
      · intro x hx y hy
        show Δ l (x * y) = 0
        rw [hL l hlN]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        by_cases hpm : p < m
        · rw [ih x hx p hpm (by omega)]; simp
        · have : l - p = 0 := by omega
          rw [this, (hmemQ y).mp hy]; simp
      · intro x y hx hy
        show Δ l (x + y) = 0
        rw [map_add, hx, hy, add_zero]
  set π' : A := π - algebraMap k A (Δ 0 π) with hπ'
  have hπ'Q : π' ∈ Q := by
    rw [hmemQ, hπ', map_sub, halg, sub_self]
  have hπ'1 : Δ 1 π' = 1 := by
    rw [hπ', map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h11, smul_zero, sub_zero, hπ]
  have hb : ∀ m < N, Δ m (π' ^ m) = (m.factorial : k) := by
    intro m
    induction m with
    | zero => intro _; simp [h01]
    | succ m ih =>
      intro hm
      rw [pow_succ', hL (m+1) hm]
      rw [Finset.sum_eq_single 1]
      · simp [hπ'1, ih (by omega), Nat.factorial_succ]
      · intro p hp hp1
        have hp' := Finset.mem_range.mp hp
        rcases Nat.lt_or_gt_of_ne hp1 with h | h
        · have : p = 0 := by omega
          subst this; rw [(hmemQ π').mp hπ'Q]; simp
        · rw [ha m (π' ^ m) (Ideal.pow_mem_pow hπ'Q m) (m + 1 - p) (by omega) (by omega)]; simp
      · intro h; simp at h
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have : π' = 0 := by rw [← Ideal.mem_bot, ← h]; exact hπ'Q
    rw [this, map_zero] at hπ'1; exact zero_ne_one hπ'1
  have hnot : ∀ m < N, π' ^ m ∉ Q ^ (m + 1) := by
    intro m hm hmem
    have := ha (m + 1) _ hmem m (by omega) hm
    rw [hb m hm] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) this
  have hc : ∀ f : A, (∀ l < N, Δ l f = 0) → ∀ m ≤ N, f ∈ Q ^ m := by
    intro f hf m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hfm := ih (by omega)
      have hI : Ideal.span {π' ^ m} ⊔ Q ^ (m + 1) = Q ^ m := by
        apply Ideal.eq_prime_pow_of_succ_lt_of_le hQ0
        · refine lt_of_le_of_ne le_sup_right ?_
          intro h; apply hnot m (by omega); rw [h]
          exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
        · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hπ'Q m))
            (Ideal.pow_le_pow_right (Nat.le_succ m))
      rw [← hI] at hfm
      obtain ⟨y, hy, g, hg, hyg⟩ := Submodule.mem_sup.mp hfm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hdc : d - algebraMap k A (Δ 0 d) ∈ Q := by
        rw [hmemQ, map_sub, halg, sub_self]
      have hrest : (d - algebraMap k A (Δ 0 d)) * π' ^ m ∈ Q ^ (m + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hdc (Ideal.pow_mem_pow hπ'Q m)
      have hrg : (d - algebraMap k A (Δ 0 d)) * π' ^ m + g ∈ Q ^ (m + 1) :=
        Ideal.add_mem _ hrest hg
      have e : f = (Δ 0 d) • π' ^ m + ((d - algebraMap k A (Δ 0 d)) * π' ^ m + g) := by
        rw [← hyg, Algebra.smul_def]; ring
      have hΔ : Δ m f = Δ 0 d * m.factorial := by
        rw [e, map_add, map_smul, hb m (by omega), ha (m + 1) _ hrg m (by omega) (by omega),
          smul_eq_mul, add_zero]
      have hc0 : Δ 0 d = 0 := by
        have := hf m (by omega); rw [hΔ] at this
        exact (mul_eq_zero.mp this).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      rw [e]; exact Ideal.add_mem _ (by rw [hc0, zero_smul]; exact Ideal.zero_mem _) hrg
  exact ⟨Q, hQmax, hmemQ, fun f hf => hc f hf N le_rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpow
section
namespace GlobalTheory

theorem mem_of_sum_mul_pow_mem_of_valuation_zpow (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω) (hN : 0 < N) (hℓ : ℓ ≠ 0)
    (hℓ1 : A.valuation ℓ < 1) (hπ : A.valuation π ^ N = A.valuation ℓ)
    (hc : ∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k)
    (hsum : (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A) : ∀ i < N, c i ∈ A := by
  classical
  set v := A.valuation with hv
  set b := v ℓ with hb
  have hb0 : 0 < b := lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff v).2 hℓ))
  set t : ℕ → A.ValueGroup := fun i => v (c i * π ^ i) with ht

  have hpow : ∀ i (k : ℤ), v (c i) = b ^ k → t i ^ N = b ^ ((N : ℤ) * k + i) := by
    intro i k hk
    simp only [ht, map_mul, map_pow, hk]
    rw [mul_pow, ← pow_mul, mul_comm i N, pow_mul, hπ, zpow_add₀ hb0.ne', mul_comm (N : ℤ) k,
      zpow_mul, zpow_natCast, zpow_natCast]

  have hdist : ∀ i < N, ∀ j < N, c i ≠ 0 → c j ≠ 0 → t i = t j → i = j := by
    intro i hi j hj hci hcj hij
    obtain ⟨k, hk⟩ := hc i hi hci
    obtain ⟨l, hl⟩ := hc j hj hcj
    have e : b ^ ((N : ℤ) * k + i) = b ^ ((N : ℤ) * l + j) := by
      rw [← hpow i k hk, ← hpow j l hl, hij]
    have e2 := (zpow_right_strictAnti₀ hb0 hℓ1).injective e
    have h1 : ((N : ℤ) * k + i) % N = (i : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have h2 : ((N : ℤ) * l + j) % N = (j : ℤ) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have : (i : ℤ) = j := by rw [← h1, ← h2, e2]
    exact_mod_cast this

  have hle : ∀ i ∈ Finset.range N, t i ≤ 1 := by
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range N) t ⟨0, Finset.mem_range.2 hN⟩
    suffices t j ≤ 1 from fun i hi => (hmax i hi).trans this
    by_cases htj : t j = 0
    · rw [htj]; exact zero_le'
    have hcj : c j ≠ 0 := by
      intro h; apply htj; simp [ht, h]
    have hlt : ∀ i ∈ Finset.range N \ {j}, v (c i * π ^ i) < v (c j * π ^ j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      refine lt_of_le_of_ne (hmax i hi.1) ?_
      intro heq
      by_cases hci : c i = 0
      · apply htj; show v (c j * π ^ j) = 0; rw [← heq]; simp [hci]
      · exact hi.2 (hdist i (Finset.mem_range.1 hi.1) j (Finset.mem_range.1 hj) hci hcj heq)
    have := Valuation.map_sum_eq_of_lt v hj hlt
    rw [← (A.valuation_le_one_iff _)] at hsum
    show v (c j * π ^ j) ≤ 1
    rw [← this]; exact hsum
  intro i hi
  by_cases hci : c i = 0
  · rw [hci]; exact A.zero_mem
  obtain ⟨k, hk⟩ := hc i hi hci
  have h1 : t i ^ N ≤ 1 := pow_le_one₀ zero_le' (hle i (Finset.mem_range.2 hi))
  rw [hpow i k hk, zpow_le_one_iff_right_of_lt_one₀ hb0 hℓ1] at h1
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push_neg at hneg
    have : (N : ℤ) * k ≤ -(N : ℤ) := by nlinarith
    omega
  rw [← A.valuation_le_one_iff, hk]
  exact zpow_le_one₀ hb0 hℓ1.le hk0

end GlobalTheory
end

