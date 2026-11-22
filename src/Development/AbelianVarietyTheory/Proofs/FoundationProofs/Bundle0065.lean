import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRoots
section
noncomputable section

namespace GlobalTheory.K5.Dense

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isClosed_eval_mem {K : Type*} [Field K] [Algebra K Ω] [Algebra.IsIntegral K Ω]
    (x : Ω) (s : Set Ω) : IsClosed {σ : Ω ≃ₐ[K] Ω | σ x ∈ s} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)), ?_,
    (stabilizer_isOpen_of_isIntegral x).preimage (by fun_prop), ?_⟩
  · intro τ hτ
    have h : σ.symm (τ x) = x := hτ
    have h' : τ x = σ x := by rw [← σ.symm_apply_eq.1 h]
    simpa [h'] using hσ
  · simp

theorem exists_of_seq (h : IsClo p Ω) (P : ℕ → Ω → Set Ω)
    (hP : ∀ n, ∃ σ : Gal p Ω, ∀ m ≤ n, ∀ x, σ x ∈ P m x) :
    ∃ σ : Gal p Ω, ∀ n x, σ x ∈ P n x := by
  classical
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  have hK : ∀ a : O0 p, algebraMap K Ω (algebraMap (O0 p) K a) = algebraMap (O0 p) Ω a :=
    fun a => IsFractionRing.lift_algebraMap h.inj a
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq (fun a => (hK a).symm)
  haveI : IsAlgClosed Ω := h.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : IsAlgClosure K Ω := ⟨h.clo, inferInstance⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  haveI : CharZero K := RingHom.charZero (algebraMap K Ω)
  haveI : IsGalois K Ω := {}
  have hfix : ∀ σ : Gal p Ω, ∀ y : K, σ (algebraMap K Ω y) = algebraMap K Ω y := by
    intro σ y
    have e : ((σ : Ω →+* Ω).comp (algebraMap K Ω)) = algebraMap K Ω := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (O0 p))
      ext a
      simp only [RingHom.comp_apply, hK]
      exact σ.commutes a
    exact congrArg (fun f : K →+* Ω => f y) e
  let φ : Gal p Ω → (Ω ≃ₐ[K] Ω) := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hφ : ∀ σ x, φ σ x = σ x := fun _ _ => rfl
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun n => {τ | ∀ m ≤ n, ∀ x, τ x ∈ P m x}
  have hcl : ∀ n, IsClosed (G n) := fun n => by
    have e : G n = ⋂ m, ⋂ (_ : m ≤ n), ⋂ x, {τ : Ω ≃ₐ[K] Ω | τ x ∈ P m x} := by
      ext τ; simp [G]
    rw [e]
    exact isClosed_iInter fun m => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_eval_mem x _
  have hdec : ∀ n, G (n + 1) ⊆ G n := fun n τ hτ m hm x => hτ m (hm.trans n.le_succ) x
  have hne : ∀ n, (G n).Nonempty := fun n => by
    obtain ⟨σ, hσ⟩ := hP n
    exact ⟨φ σ, fun m hm x => by rw [hφ]; exact hσ m hm x⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hτ
  exact ⟨τ.restrictScalars (O0 p), fun n x => hτ n n le_rfl x⟩

theorem exists_finset_orbit (h : IsClo p Ω) (x : Ω) : ∃ R : Finset Ω, ∀ σ : Gal p Ω, σ x ∈ R := by
  classical
  obtain ⟨P, hP0, hPx⟩ := h.alg.isAlgebraic x
  refine ⟨(P.aroots Ω).toFinset, fun σ => ?_⟩
  rw [Multiset.mem_toFinset, mem_aroots']
  refine ⟨(Polynomial.map_ne_zero_iff h.inj).2 hP0, ?_⟩
  have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[O0 p] Ω) x P
  simp only [AlgEquiv.coe_algHom] at e
  rw [e, hPx, map_zero]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨X ^ (p ^ n) - C 1, X_pow_sub_C_ne_zero (pow_pos hp.out.pos n) 1, ?_⟩
  simp [(T.prim n).pow_eq_one]

theorem qq_pow_sub (T : Tower p Ω) {n m : ℕ} (h : n ≤ m) : T.qq m ^ p ^ (m - n) = T.qq n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem ggeo_apply {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) {x : Ω} (hx : IsAlgZp p x) : g x = x := hg x hx

theorem tau_pow_qq (T : Tower p Ω) {τ : Gal p Ω} (hτ : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) (n s : ℕ) :
    (τ ^ s) (T.qq n) = T.ζ n ^ s * T.qq n := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih,
      ggeo_apply ((Ggeo p Ω).pow_mem hτ s) (isAlgZp_zeta T n), pow_succ]
    ring

theorem dense_tau_pow_mul (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω] (hΩ : IsClo p Ω) (T : Tower p Ω) (τ : Gal p Ω) (hτ : τ ∈ Ggeo p Ω)
    (hτq : ∀ n, τ (T.qq n) = T.ζ n * T.qq n) :
    ∀ g ∈ Ggeo p Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ x ∈ S, (τ ^ s * h) x = g x := by
  classical
  intro g hg S
  have hs : ∀ n, ∃ s : ℕ, (τ ^ s) (T.qq n) = g (T.qq n) := by
    intro n
    have hq0 := Basic.qq_ne_zero T n
    have hqp : T.qq n ^ p ^ n ≠ 0 := pow_ne_zero _ hq0
    have e : (g (T.qq n) / T.qq n) ^ (p ^ n) = 1 := by
      rw [div_pow, ← map_pow, Basic.qq_pow, AlgEquiv.commutes, ← Basic.qq_pow T n, div_self hqp]
    obtain ⟨i, -, hi⟩ := (T.prim n).eq_pow_of_pow_eq_one e
    exact ⟨i, by rw [tau_pow_qq T hτ hτq, hi, div_mul_cancel₀ _ hq0]⟩
  choose s hs using hs
  let σ : ℕ → Gal p Ω := fun n => (τ ^ s n)⁻¹ * g
  have hσG : ∀ n, σ n ∈ Ggeo p Ω := fun n =>
    (Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem ((Ggeo p Ω).pow_mem hτ _)) hg
  have hσq : ∀ n, σ n (T.qq n) = T.qq n := by
    intro n
    show ((τ ^ s n)⁻¹ * g) (T.qq n) = T.qq n
    rw [AlgEquiv.mul_apply, ← hs n, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  choose R hR using fun x => exists_finset_orbit hΩ x
  let F : ℕ → ((x : S) → ↥(R x.1)) := fun n x => ⟨σ n x, hR x.1 (σ n)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber F
  have hinf : (F ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  obtain ⟨n₁, hn₁⟩ := hinf.nonempty
  have hS : ∀ m ∈ F ⁻¹' {y}, ∀ x ∈ S, σ m x = σ n₁ x := by
    intro m hm x hx
    have e : F m = F n₁ := (Set.mem_preimage.1 hm).trans (Set.mem_preimage.1 hn₁).symm
    exact congrArg Subtype.val (congrFun e ⟨x, hx⟩)
  let P : ℕ → Ω → Set Ω := fun n x =>
    {z | (IsAlgZp p x → z = x) ∧ (x ∈ S → z = σ n₁ x) ∧ (x = T.qq n → z = x)}
  have hP : ∀ n, ∃ ρ : Gal p Ω, ∀ m ≤ n, ∀ x, ρ x ∈ P m x := by
    intro n
    obtain ⟨m, hm, hnm⟩ := hinf.exists_gt n
    refine ⟨σ m, fun m' hm' x => ⟨fun hx => ggeo_apply (hσG m) hx, fun hx => hS m hm x hx, ?_⟩⟩
    rintro rfl
    rw [← qq_pow_sub T (hm'.trans hnm.le), map_pow, hσq m]
  obtain ⟨z, hz⟩ := exists_of_seq hΩ P hP
  refine ⟨s n₁, z, ?_, fun x hx => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨fun x hx => (hz 0 x).1 hx, Subgroup.mem_iInf.2 fun n => ?_⟩
    exact (Basic.mem_gn T n z).2 ⟨(hz 0 _).1 (isAlgZp_zeta T n), (hz n _).2.2 rfl⟩
  · rw [AlgEquiv.mul_apply, (hz 0 x).2.1 hx]
    show (τ ^ s n₁) (((τ ^ s n₁)⁻¹ * g) x) = g x
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

end GlobalTheory.K5.Dense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gl2L2Integrality
section
open Finset Filter Topology MeasureTheory

namespace GlobalTheory.PsiTail

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

lemma pow_le_exp (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial / b ^ n) * Real.exp (b * x) := by
  have h := Real.pow_div_factorial_le_exp (b * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]

lemma one_le_log {Q : ℝ} (hQ : 3 ≤ Q) : 1 ≤ Real.log Q := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma error_terms (c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ Q u : ℝ, 3 ≤ Q → 2 ≤ u →
    (u ≤ Real.exp (Real.log Q ^ 2) → Real.log (u * Q) ^ 2 / Q ≤ K * Q ^ (-c) / Real.log u ^ 2) ∧
    (Real.exp (Real.log Q ^ 2) ≤ u →
      Real.exp (-c₁ * Real.sqrt (Real.log u)) ≤ K * Q ^ (-c) / Real.log u ^ 2) := by
  set K₁ : ℝ := (Nat.factorial 8 : ℝ) / (1 / 2) ^ 8 with hK₁
  set K₂ : ℝ := (Nat.factorial 4 : ℝ) / (c₁ / 2) ^ 4 with hK₂
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 < K₂ := by rw [hK₂]; positivity
  refine ⟨4 * K₁ + K₂, min (1 / 2) (c₁ / 2), by positivity, lt_min (by norm_num) (by positivity), ?_⟩
  intro Q u hQ hu
  have hQ0 : 0 < Q := by linarith
  have hu0 : 0 < u := by linarith
  have hL := one_le_log hQ
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  set L := Real.log Q with hLdef
  set c := min (1 / 2 : ℝ) (c₁ / 2) with hc
  have hQc : Q ^ (-c) = Real.exp (-(c * L)) := by
    rw [Real.rpow_def_of_pos hQ0]; congr 1; ring
  have hE : 0 < Real.exp (-(c * L)) := Real.exp_pos _
  rw [hQc]
  constructor
  · intro h
    have h1 : Real.log u ≤ L ^ 2 := by
      rw [Real.log_le_iff_le_exp hu0]; exact h
    have h2 : Real.log (u * Q) = Real.log u + L := Real.log_mul hu0.ne' hQ0.ne'
    have h3 : Real.log (u * Q) ≤ 2 * L ^ 2 := by rw [h2]; nlinarith
    have h3' : 0 ≤ Real.log (u * Q) := by rw [h2]; linarith
    have h4 : Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := by
      calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ (2 * L ^ 2) ^ 2 * (L ^ 2) ^ 2 := by gcongr
        _ = 4 * L ^ 8 := by ring
    have h5 : L ^ 8 ≤ K₁ * Real.exp (1 / 2 * L) := pow_le_exp (1 / 2) (by norm_num) 8 L (by linarith)
    have h6 : Real.exp (1 / 2 * L) ≤ Real.exp (-(c * L)) * Q := by
      have : Q = Real.exp L := (Real.exp_log hQ0).symm
      conv_rhs => rw [this]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : c ≤ 1 / 2 := min_le_left _ _
      nlinarith
    rw [div_le_div_iff₀ hQ0 (by positivity)]
    have h7 : K₁ * Real.exp (1 / 2 * L) ≤ K₁ * (Real.exp (-(c * L)) * Q) := by gcongr
    have h8 : 0 ≤ K₂ * (Real.exp (-(c * L)) * Q) := by positivity
    calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := h4
      _ ≤ 4 * (K₁ * (Real.exp (-(c * L)) * Q)) + K₂ * (Real.exp (-(c * L)) * Q) := by
        have := h5.trans h7
        linarith
      _ = _ := by ring
  · intro h
    have h1 : L ^ 2 ≤ Real.log u := by
      rw [Real.le_log_iff_exp_le hu0]; exact h
    set s := Real.sqrt (Real.log u) with hs
    have hs2 : s ^ 2 = Real.log u := Real.sq_sqrt hlu.le
    have hLs : L ≤ s := Real.le_sqrt_of_sq_le h1
    have h5 : s ^ 4 ≤ K₂ * Real.exp (c₁ / 2 * s) := pow_le_exp (c₁ / 2) (by positivity) 4 s (by linarith)
    have h6 : Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s) ≤ Real.exp (-(c * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h7 : c ≤ c₁ / 2 := min_le_right _ _
      have h8 : c * L ≤ c₁ / 2 * s := by gcongr
      linarith
    rw [le_div_iff₀ (by positivity), ← hs2]
    calc Real.exp (-c₁ * s) * (s ^ 2) ^ 2 = Real.exp (-c₁ * s) * s ^ 4 := by ring
      _ ≤ Real.exp (-c₁ * s) * (K₂ * Real.exp (c₁ / 2 * s)) := by gcongr
      _ = K₂ * (Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s)) := by ring
      _ ≤ K₂ * Real.exp (-(c * L)) := by gcongr
      _ ≤ (4 * K₁ + K₂) * Real.exp (-(c * L)) := by gcongr; linarith

lemma hasDerivAt_prim (Q E u : ℝ) (hQ : 0 < Q) (hu : 1 < u) :
    HasDerivAt (fun t : ℝ => -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
      ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) u := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-(1 : ℝ) / 400)) ((-(1 : ℝ) / 400) * (u ^ (-(1 : ℝ) / 400) / u)) u := by
    have := Real.hasDerivAt_rpow_const (x := u) (p := -(1 : ℝ) / 400) (Or.inl hu0.ne')
    rwa [Real.rpow_sub_one hu0.ne'] at this
  have h2 : HasDerivAt (fun t : ℝ => Real.log (t * Q)) (1 / u) u := by
    have := ((hasDerivAt_id' u).mul_const Q).log (by positivity)
    refine this.congr_deriv ?_
    field_simp
  have h3 : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
  have h4 := ((h1.fun_mul ((((h2.fun_pow 2).const_mul 400).fun_add (h2.const_mul 320000)).add_const 128000000)).fun_add
    ((hasDerivAt_const u E).fun_div h3 hlu.ne')).fun_neg
  refine h4.congr_deriv ?_
  have := hlu.ne'
  have := hu0.ne'
  generalize u ^ (-(1 : ℝ) / 400) = w
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

theorem psi_tail_bound : PartialSumIntegralBound := by
  intro C₁ c₁ hC₁ hc₁
  obtain ⟨K, c, hK, hc, herr⟩ := error_terms c₁ hc₁
  refine ⟨C₁ * (128320401 + 5 * K), c, by positivity, hc, ?_⟩
  intro Q a hQ h1 h2 Z U hZ hZU
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_log hQ
  set E := K * Q ^ (-c) with hE
  have hE0 : 0 < E := by rw [hE]; positivity
  have hpt : ∀ u : ℝ, 2 ≤ u →
      ‖psum a u‖ / u ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    rw [div_le_iff₀ hu0]
    rcases le_total u (Real.exp (Real.log Q ^ 2)) with h | h
    · have e := (herr Q u hQ hu).1 h
      have e1 : u ^ (1 - (1 : ℝ) / 400) = u ^ (-(1 : ℝ) / 400) * u := by
        rw [← Real.rpow_add_one hu0.ne']; congr 1; ring
      calc ‖psum a u‖ ≤ _ := h1 u hu
        _ = C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + Real.log (u * Q) ^ 2 / Q) * u := by
          rw [e1]; ring
        _ ≤ _ := by gcongr
    · have e := (herr Q u hQ hu).2 h
      have e1 : 0 ≤ u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 := by positivity
      calc ‖psum a u‖ ≤ _ := h2 u h
        _ = C₁ * Real.exp (-c₁ * Real.sqrt (Real.log u)) * u := by ring
        _ ≤ _ := by gcongr; linarith
  set g : ℝ → ℝ := fun u =>
    C₁ * ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) with hg
  have hpt2 : ∀ u ∈ Set.Icc Z U, ‖psum a u‖ / u ^ 2 ≤ g u := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : 0 < u := by linarith
    calc ‖psum a u‖ / u ^ 2 = ‖psum a u‖ / u / u := by field_simp
      _ ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u := by
        gcongr; exact hpt u hu2
      _ = g u := by rw [hg]; ring
  have hgc : ContinuousOn g (Set.Icc Z U) := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlu : Real.log u ^ 2 ≠ 0 := (pow_pos (Real.log_pos (by linarith)) 2).ne'
    have huQ : u * Q ≠ 0 := mul_ne_zero hu0 hQ0.ne'
    apply ContinuousAt.continuousWithinAt
    rw [hg]
    fun_prop (disch := first | assumption | exact Or.inl hu0)
  have hgi : IntervalIntegrable g volume Z U := hgc.intervalIntegrable_of_Icc hZU
  have hmeas : Measurable (fun u : ℝ => ‖psum a u‖ / u ^ 2) := by
    have : Measurable (fun u : ℝ => ‖psum a u‖) :=
      (measurable_from_top (f := fun N : ℕ => ‖∑ n ∈ Icc 1 N, a n‖)).comp Nat.measurable_floor
    exact this.div (measurable_id.pow_const 2)
  have hfi : IntervalIntegrable (fun u : ℝ => ‖psum a u‖ / u ^ 2) volume Z U := by
    refine hgi.mono_fun' hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hZU]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt2 u (Set.Ioc_subset_Icc_self hu)
  have hint := intervalIntegral.integral_mono_on hZU hfi hgi hpt2
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := g)
    (f := fun t : ℝ => C₁ * -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
    (a := Z) (b := U) (fun u hu => by
      rw [Set.uIcc_of_le hZU] at hu
      exact (hasDerivAt_prim Q E u hQ0 (by linarith [hu.1])).const_mul C₁) hgi
  have hZ0 : 0 < Z := by linarith
  have hU0 : 0 < U := by linarith
  have hlU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlUQ : 0 < Real.log (U * Q) := Real.log_pos (by nlinarith)
  have hlZ : 2 / 3 ≤ Real.log Z := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hZ
    linarith
  have hlZQ : 1 ≤ Real.log (Z * Q) := by rw [Real.log_mul hZ0.ne' hQ0.ne']; linarith
  have hUnn : 0 ≤ C₁ * (U ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (U * Q) ^ 2 + 320000 * Real.log (U * Q) + 128000000) + E / Real.log U) := by
    positivity
  have hZpt := hpt Z hZ
  set w := Z ^ (-(1 : ℝ) / 400) with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  set l := Real.log (Z * Q) with hl
  have b1 : 400 * l ^ 2 + 320000 * l + 128000000 ≤ 128320400 * l ^ 2 := by nlinarith
  have b2 : E / Real.log Z ≤ 2 * E := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have b3 : E / Real.log Z ^ 2 ≤ 3 * E := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ 3 * Real.log Z ^ 2 := by nlinarith
    nlinarith
  have hq : 0 < Q ^ (-c) := by positivity
  have hwl : 0 < w * l ^ 2 := by positivity
  calc ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2)
      ≤ C₁ * (w * l ^ 2 + E / Real.log Z ^ 2) +
        C₁ * (w * (400 * l ^ 2 + 320000 * l + 128000000) + E / Real.log Z) := by
        refine add_le_add hZpt (hint.trans ?_)
        rw [hval]
        linarith
    _ ≤ C₁ * (w * l ^ 2 + 3 * E) + C₁ * (w * (128320400 * l ^ 2) + 2 * E) := by gcongr
    _ = C₁ * (128320401 * (w * l ^ 2) + 5 * K * Q ^ (-c)) := by rw [hE]; ring
    _ ≤ C₁ * ((128320401 + 5 * K) * (w * l ^ 2 + Q ^ (-c))) := by
        gcongr
        nlinarith [mul_pos hK hwl]
    _ = _ := by ring

end GlobalTheory.PsiTail
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dif_pos h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiagStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) • (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | exact GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_between | exact GlobalTheory.FinWeil.sumOp_comp_of_between | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_between <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndexStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → idx B A = idx A B ∧ ∀ v, Fixes W A v → sumOp W B A (sumOp W A B v) = (idx A B : ℂ) • v := by
  first | exact @GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | exact GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | (intros; apply GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul <;> assumption)
end

