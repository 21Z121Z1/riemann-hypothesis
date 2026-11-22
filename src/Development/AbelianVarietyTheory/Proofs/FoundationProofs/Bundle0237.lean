import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormOneScalar

theorem exists_of_anti {E : Type} [Field E] [CharZero E] (c : E →+* E) (s : E) (hs : s ≠ 0) (hc : c s = -s)
    (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, z * c z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  have hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0 := by
    intro k h
    have h1 : s = (k : E) + 1 := by linear_combination -h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  have hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0 := by
    intro k h
    have h1 : s = -((k : E) + 1) := by linear_combination h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  let f : ℕ → E := fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)
  have hf : Function.Injective f := by
    intro a b h
    have h' := (div_eq_div_iff (hm a) (hm b)).1 h
    have : (2 : E) * s * ((a : E) - b) = 0 := by linear_combination -h'
    have h3 : (a : E) - b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    exact_mod_cast sub_eq_zero.1 h3
  have hP : γ.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := γ)
    rw [h] at this
    simp at this
  have hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hP
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite hfin
  refine ⟨f k, ?_, ?_, ?_⟩
  · have h1 := hm k
    have h2 := hp k
    simp only [f, map_div₀, map_add, map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp
  · intro h
    have h' := (div_eq_one_iff_eq (hm k)).1 h
    apply hs
    have : (2 : E) * s = 0 := by linear_combination h'
    simpa using this
  · intro h
    apply hz
    show Polynomial.eval (f k) γ.charpolyRev = 0
    rw [← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _

theorem exists_norm_one_det_ne_zero : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E),
    ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  intro D n γ
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := D.host.sqrtMinusD_sq
    rw [h] at h1
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
    exact D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)
  exact exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ

end GlobalTheory.NormOneScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

theorem exists_periodPair_of_im_ne_zero {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (a : 𝓞 K) (ha : (σ (a : K)).im ≠ 0) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem eisG_eq_periodPair_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = L.G (2 * k) := by
  have e1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  refine e1.trans (Eq.trans (tsum_congr fun w => ?_) e2.symm)
  by_cases hw : w = 0
  · subst hw
    simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_ne_zero (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : TaylorLogMetric.discr Λ ≠ 0 := by
  have := g₂_cube_sub_g₃_sq_ne_zero L
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_periodPair_G Λ L h two_ne_zero, eisG_eq_periodPair_G Λ L h three_ne_zero]
  exact this

theorem mem_lamOf_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

theorem exists_periodPair_one (D : D7) {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc 1 ↔ z ∈ L.lattice := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hK : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K hd hb
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : s ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [s] using hb)
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have him : (σ (((⟨s, hint⟩ : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)).im ≠ 0 := by
    intro h0
    change (σ s).im = 0 at h0
    have e : σ s ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hs]; simp
    have e' := congrArg Complex.re e
    simp only [pow_two, Complex.mul_re, h0, Complex.neg_re, Complex.natCast_re] at e'
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (σ s).re]
  obtain ⟨L, hL⟩ := exists_periodPair_of_im_ne_zero hK σ (⟨s, hint⟩ : 𝓞 D.host.K) him hc
  refine ⟨L, fun z => ?_⟩
  rw [hL, mem_lamOf_iff]
  simp only [one_mul]
  rfl

theorem exists_periodPair_lamOf : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  intro D cc δ h
  obtain ⟨L, hL⟩ := exists_periodPair_one D h.1.1
  have hδ : δ ≠ 0 := by
    rintro rfl
    have e : (0 : ℂ) ^ 12 = TaylorLogMetric.discr (lamOf D cc 1) := h.2
    exact discr_ne_zero _ L hL (by rw [← e]; simp)
  have hind : LinearIndependent ℝ ![δ * L.ω₁, δ * L.ω₂] := by
    have h1 := LinearIndependent.pair_iff.1 L.indep
    rw [LinearIndependent.pair_iff]
    intro x y e
    refine h1 x y (mul_left_cancel₀ hδ ?_)
    simp only [Complex.real_smul] at e ⊢
    linear_combination e
  refine ⟨⟨δ * L.ω₁, δ * L.ω₂, hind⟩, fun z => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ((mem_lamOf_iff D cc 1 _).2 ⟨c, hc, rfl⟩))
    exact ⟨m, n, by linear_combination δ * e⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨c, hc, e⟩ := (mem_lamOf_iff D cc 1 _).1 ((hL _).2 (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩))
    exact ⟨c, hc, by linear_combination δ * e⟩

end GlobalTheory.CurveLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HomDual

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← h, ← h, star_star]

theorem pairing_mem (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L)
    {u x : Fin N → D.host.E} (hu : u ∈ L) (hx : x ∈ L) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = ∑ b, D.host.conj (u b) * x b := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨c, hc⟩ := (hL.2.2 x).1 hx u hu
  refine ⟨c, hc.trans ?_⟩
  simp only [stdH, h]

theorem exists_resolution (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : SD D L) : ∃ (m : ℕ) (v w : Fin m → Fin N → D.host.E), (∀ i, v i ∈ L) ∧ (∀ i, w i ∈ L) ∧
      ∀ (u : Fin N → D.host.E) (a : Fin N),
        u a = ∑ i, (∑ b, u b * D.host.conj (w i b)) * v i a := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x := h
  have hh : ∀ x y : Fin N → D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y := by
    intro x y
    rw [GlobalTheory.DualFamily.herm_one_eq]
    simp only [stdH, h, h', mul_comm]
  have hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z :=
    fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨-, m, v, w, hv, hw, he⟩ := GlobalTheory.exists_dual_family L hL.1
    (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy)
    (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)
  refine ⟨m, v, w, hv, hw, fun u a => ?_⟩
  have := congrFun (he u) a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']
    using this

theorem rank_one_mem (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) {c : D.host.E}
    (hc : c ∈ D.host.AA0) {u : Fin N → D.host.E} (hu : u ∈ L) {v : Fin N' → D.host.E}
    (hv : v ∈ L') :
    c • (Matrix.of fun a b => v a * D.host.conj (u b)) ∈ YYl D L L' := by
  refine Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩
  obtain ⟨e, he⟩ := pairing_mem D hL hu hx
  have : (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v := by
    funext a
    change ∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a
    rw [he, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact L'.smul_mem e hv

theorem exists_dual_family_hom : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  rintro D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'
  obtain ⟨m, u, u', hu, hu', eu⟩ := exists_resolution D hL
  obtain ⟨m', v, v', hv, hv', ev⟩ := exists_resolution D hL'
  let Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)
  let Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)
  let e := (Fintype.equivFin (Fin m' × Fin m × Fin r)).symm
  refine ⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _),
    fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩
  refine Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm
  refine Matrix.ext fun s t => ?_
  have eu' : ∀ (z : Fin N → D.host.E) (t : Fin N),
      z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t) := by
    intro z t
    have := congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)
    simpa only [map_sum, map_mul, conj_conj] using this
  have hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E
      ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k)) := by
    intro j i k
    unfold hYY
    congr 1
    simp only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT]
  simp only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]
  congr 1
  ring

end GlobalTheory.HomDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

namespace TraceDualFamily

open scoped nonZeroDivisors

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

lemma conj_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (x : E) : c (c x) = x := by
  apply φ₀.injective
  rw [hc, hc, Complex.conj_conj]

lemma mem_range_iff (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

lemma isIntegral_trace_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (z : E)
    (hz : IsIntegral ℤ (Algebra.trace K E z)) : IsIntegral ℤ (Algebra.trace K E (c z)) := by
  letI : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have h1 : algebraMap K ℂ (Algebra.trace K E (c z)) =
      starRingEnd ℂ (algebraMap K ℂ (Algebra.trace K E z)) := by
    rw [trace_eq_sum_embeddings ℂ, trace_eq_sum_embeddings ℂ, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc (σ : E →+* ℂ) z
  have h2 : IsIntegral ℤ (algebraMap K ℂ (Algebra.trace K E (c z))) := by
    rw [h1]
    exact (hz.map (algebraMap K ℂ).toIntAlgHom).map (starRingEnd ℂ).toIntAlgHom
  exact (isIntegral_algHom_iff (algebraMap K ℂ).toIntAlgHom (algebraMap K ℂ).injective).mp h2

lemma isLocalizedModule_subtype (Λ : Submodule (𝓞 K) E)
    (h : Submodule.span K (Λ : Set E) = ⊤) : IsLocalizedModule (𝓞 K)⁰ Λ.subtype where
  map_units s := by
    have := isLocalizedModule_id (𝓞 K)⁰ E K
    exact IsLocalizedModule.map_units (S := (𝓞 K)⁰) (LinearMap.id : E →ₗ[𝓞 K] _) s
  surj y := by
    have hy : y ∈ Submodule.span K (Λ : Set E) := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 K)⁰ K _ y hy
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨_, ht⟩, t), rfl⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

theorem exists_family (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x))
    (I : FractionalIdeal (𝓞 E)⁰ E)
    (hI : ∀ x : E, x ∈ I ↔ ∀ y ∈ I, Algebra.trace K E (x * c y) ∈ (algebraMap (𝓞 K) K).range) :
    ∃ (r : ℕ) (a a' : Fin r → E), (∀ k, a k ∈ I) ∧ (∀ k, a' k ∈ I) ∧
      ∀ t : E, t = ∑ k, (Algebra.trace K E (t * c (a' k))) • a k := by
  have hI0 : I ≠ 0 := by
    rintro rfl
    have := (hI 1).mpr (by
      intro y hy
      rw [FractionalIdeal.mem_zero_iff] at hy
      subst hy
      simp)
    rw [FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  let Λ : Submodule (𝓞 K) E := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have hsp : Submodule.span K (Λ : Set E) = ⊤ := by
    obtain ⟨x, hx, hx0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI0
    rw [eq_top_iff]
    intro t _
    have hx' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx
    have halg : IsAlgebraic ℤ (t / algebraMap (𝓞 E) E x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hmem : (n : E) * t ∈ Λ := by
      have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hn⟩ : 𝓞 E) hx0
      convert this using 1
      change _ ↔ (n • (t / algebraMap (𝓞 E) E x)) * algebraMap (𝓞 E) E x ∈ _
      rw [zsmul_eq_mul, mul_assoc, div_mul_cancel₀ _ hx']
      rfl
    have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
    have : t = (n : K)⁻¹ • ((n : E) * t) := by
      have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
      rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel_left₀ hnE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.mpr
    (Submodule.FG.restrictScalars (FractionalIdeal.fg_of_isNoetherianRing le_rfl I))
  have : Module.FinitePresentation (𝓞 K) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg'⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) Λ
  have := isLocalizedModule_subtype Λ hsp
  have hext : ∀ i : Fin m, ∃ w : E, ∀ y : Λ, Algebra.trace K E ((y : E) * c w) = (g y i : K) := by
    intro i
    let φ : Λ →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K ∘ₗ LinearMap.proj i ∘ₗ g
    let ψ : E →ₗ[𝓞 K] K := IsLocalizedModule.lift (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K))
    obtain ⟨u, hu⟩ := ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).surjective
      (ψ.extendScalarsOfIsLocalization (𝓞 K)⁰ K)
    refine ⟨c.symm u, fun y => ?_⟩
    have h1 := LinearMap.congr_fun hu (y : E)
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    rw [AlgEquiv.apply_symm_apply, mul_comm, h1]
    exact IsLocalizedModule.lift_apply (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K)) y
  choose w hw using hext
  refine ⟨m, fun i => (f (Pi.single i 1) : E), w, fun i => Subtype.prop (f (Pi.single i 1)),
    fun i => ?_, ?_⟩
  · refine (hI _).mpr fun y hy => (mem_range_iff _).mpr ?_
    have e : w i * c y = c (y * c (w i)) := by rw [map_mul, conj_conj c φ₀ hc, mul_comm]
    rw [e]
    refine isIntegral_trace_conj c φ₀ hc _ ?_
    rw [hw i ⟨y, hy⟩]
    exact RingOfIntegers.isIntegral_coe _
  · intro u
    have hu : u ∈ Submodule.span K (Λ : Set E) := hsp ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      have h1 : f (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hfg' _
      have h2 : g ⟨y, hy⟩ = ∑ i, g ⟨y, hy⟩ i • (Pi.single i 1 : Fin m → 𝓞 K) := by
        ext j; simp [Pi.single_apply]
      rw [h2, map_sum] at h1
      have h3 := congrArg Subtype.val h1
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hw i ⟨y, hy⟩]
      exact (algebraMap_smul K _ _).symm
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      simp [add_mul, Finset.sum_add_distrib, add_smul]
    | smul a x _ hx =>
      conv_lhs => rw [hx]
      simp [Finset.smul_sum, mul_smul]

end TraceDualFamily

theorem exists_trace_dual_family_halfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k :=
  fun D => TraceDualFamily.exists_family D.host.conj D.host.φ₀
    (fun φ x => D.host.conjE_apply φ x) D.host.AA0
    (factMMUnimodular D.R D.host)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaMemSum
section
namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
end

