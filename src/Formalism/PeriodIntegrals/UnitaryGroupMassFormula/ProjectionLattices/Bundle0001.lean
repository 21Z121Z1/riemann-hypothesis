import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.FinrankIntertw
section
noncomputable section

namespace PI.Dv.GLP

open Representation

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem intertw_alg {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (f : V →ₗ[K] W)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) (a : MonoidAlgebra K G) (x : V) :
    f (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (f x) := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, hf]
  | add a b ha hb => simp [map_add, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem exists_end_map {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {x : W} (hx : x ≠ 0) (y : W) : ∃ b : Module.End K W, b x = y := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff K x).1 h)
  refine ⟨(φ x)⁻¹ • LinearMap.smulRight φ y, ?_⟩
  simp [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]

theorem scalar_of_comm (T : GoodSet K G) (s : T.S) (F : Module.End K (T.W s))
    (hF : ∀ g, F * T.tau s g = T.tau s g * F) : ∃ c : K, F = algebraMap K _ c := by
  have hc : F ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    obtain ⟨a, rfl⟩ := T.irr s b
    ext x
    simp only [Module.End.mul_apply]
    exact (intertw_alg (T.tau s) (T.tau s) F (fun g x => LinearMap.congr_fun (hF g) x) a x).symm
  rw [Algebra.IsCentral.center_eq_bot] at hc
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hc
  exact ⟨c, hc.symm⟩

theorem intertw_zero (T : GoodSet K G) {s t : T.S} (hst : s ≠ t) (f : T.W s →ₗ[K] T.W t)
    (hf : ∀ g x, f (T.tau s g x) = T.tau t g (f x)) : f = 0 := by
  by_contra hne
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    apply hne
    ext y
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hx0 y
    obtain ⟨a, rfl⟩ := T.irr s b
    rw [← hb, intertw_alg _ _ f hf a x, LinearMap.mem_ker.1 hx, map_zero]
    rfl
  have hsurj : Function.Surjective f := by
    obtain ⟨y0, hy0⟩ : ∃ y0, f y0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    intro z
    obtain ⟨b, hb⟩ := exists_end_map (K := K) hy0 z
    obtain ⟨a, rfl⟩ := T.irr t b
    exact ⟨(T.tau s).asAlgebraHom a y0, by rw [intertw_alg _ _ f hf a y0, hb]⟩
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  apply hst
  apply T.inj
  funext g
  have : T.tau t g = e.conj (T.tau s g) := by
    ext z
    obtain ⟨x, rfl⟩ := hsurj z
    have hx : e.symm (f x) = x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx]
    rw [← hf g x]
    rfl
  simp only
  rw [this, LinearMap.trace_conj']

theorem finrank_intertw (T : GoodSet K G) (s t : T.S) :
    Module.finrank K (IntertwiningMap (T.tau s) (T.tau t)) = if s = t then 1 else 0 := by
  split_ifs with h
  · subst h
    have hne : (IntertwiningMap.id (T.tau s)) ≠ 0 := by
      intro h0
      obtain ⟨x, hx⟩ := exists_ne (0 : T.W s)
      apply hx
      have := congrArg (fun f : IntertwiningMap (T.tau s) (T.tau s) => f x) h0
      simpa using this
    rw [finrank_eq_one_iff_of_nonzero' _ hne]
    intro f
    obtain ⟨c, hc⟩ := scalar_of_comm T s f.toLinearMap (fun g => f.isIntertwining' g)
    refine ⟨c, ?_⟩
    ext x
    rw [IntertwiningMap.toLinearMap_smul, LinearMap.smul_apply, IntertwiningMap.toLinearMap_id,
      LinearMap.id_apply, hc, Module.algebraMap_end_apply]
  · have : Subsingleton (IntertwiningMap (T.tau s) (T.tau t)) := ⟨fun f g => by
      ext1
      rw [intertw_zero T h f.toLinearMap (fun g x => LinearMap.congr_fun (f.isIntertwining' g) x),
        intertw_zero T h g.toLinearMap (fun g' x => LinearMap.congr_fun (g.isIntertwining' g') x)]⟩
    exact Module.finrank_zero_of_subsingleton

theorem card_ne_zero [CharZero K] : ((Fintype.card G : ℕ) : K) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem char_orth [CharZero K] (T : GoodSet K G) (s t : T.S) :
    ∑ g : G, LinearMap.trace K _ (T.tau t g) * LinearMap.trace K _ (T.tau s g⁻¹) =
      if s = t then ((Fintype.card G : ℕ) : K) else 0 := by
  have hG : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact card_ne_zero
  haveI : Invertible ((Nat.card G : ℕ) : K) := invertibleOfNonzero hG
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (T.tau s) (T.tau t)
  rw [finrank_intertw] at h
  simp only [Representation.character] at h
  rw [inv_mul_eq_iff_eq_mul₀ hG] at h
  rw [h, Nat.card_eq_fintype_card]
  split_ifs <;> simp

def cS (T : GoodSet K G) (s : T.S) (x : G) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)

theorem eS_eq (T : GoodSet K G) (s : T.S) :
    eS T s = ∑ x : G, cS T s x • MonoidAlgebra.of K G x := rfl

theorem asAlg_eS {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (T : GoodSet K G) (s : T.S) :
    ρ.asAlgebraHom (eS T s) = ∑ x : G, cS T s x • ρ x := by
  rw [eS_eq, map_sum]
  simp [map_smul, Representation.asAlgebraHom_of]

theorem cS_conj (T : GoodSet K G) (s : T.S) (h x : G) : cS T s (h * x * h⁻¹) = cS T s x := by
  have := Representation.char_conj (T.tau s) x⁻¹ h
  simp only [Representation.character] at this
  simp only [cS]
  rw [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, this]

theorem tau_eS_comm (T : GoodSet K G) (s t : T.S) (g : G) :
    (T.tau t).asAlgebraHom (eS T s) * T.tau t g = T.tau t g * (T.tau t).asAlgebraHom (eS T s) := by
  rw [asAlg_eS, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  have hc := cS_conj T s g⁻¹ x
  rw [inv_inv] at hc
  rw [hc]
  congr 2
  group

theorem finrank_pos' (T : GoodSet K G) (s : T.S) : (0 : ℕ) < Module.finrank K (T.W s) :=
  Module.finrank_pos

theorem tau_eS [CharZero K] (T : GoodSet K G) (s t : T.S) :
    (T.tau t).asAlgebraHom (eS T s) = if s = t then 1 else 0 := by
  obtain ⟨c, hc⟩ := scalar_of_comm T t _ (tau_eS_comm T s t)
  have htr : LinearMap.trace K _ ((T.tau t).asAlgebraHom (eS T s)) =
      ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        (if s = t then ((Fintype.card G : ℕ) : K) else 0) := by
    rw [asAlg_eS, map_sum, ← char_orth T s t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, cS]
    ring
  rw [hc, Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (finrank_pos' T t).ne'
  rw [hc]
  split_ifs with h
  · subst h
    rw [if_pos rfl, div_mul_cancel₀ _ (card_ne_zero (K := K) (G := G))] at htr
    have : c = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, map_one]
  · rw [if_neg h, mul_zero] at htr
    have : c = 0 := by
      rcases mul_eq_zero.1 htr with h1 | h1
      · exact h1
      · exact absurd h1 hd
    rw [this, map_zero]

theorem coef_mul [CharZero K] (T : GoodSet K G) (s t : T.S) (z : G) :
    ∑ x : G, cS T s x * cS T t (x⁻¹ * z) = if s = t then cS T s z else 0 := by
  have key : ∑ x : G, cS T s x * cS T t (x⁻¹ * z) =
      ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
        LinearMap.trace K _ (T.tau t z⁻¹ * (T.tau t).asAlgebraHom (eS T s)) := by
    rw [asAlg_eS, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, ← map_mul]
    simp only [cS, mul_inv_rev, inv_inv]
    ring
  rw [key, tau_eS]
  split_ifs with h
  · subst h
    rw [mul_one, cS]
  · rw [mul_zero, map_zero, mul_zero]

theorem eS_mul_eS [CharZero K] (T : GoodSet K G) (s t : T.S) :
    eS T s * eS T t = if s = t then eS T s else 0 := by
  have h1 : eS T s * eS T t =
      ∑ z : G, (∑ x : G, cS T s x * cS T t (x⁻¹ * z)) • MonoidAlgebra.of K G z := by
    rw [eS_eq, eS_eq, Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm, ← map_mul]
    simp_rw [Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun y => by simp)
  rw [h1]
  simp_rw [coef_mul]
  split_ifs with h
  · rw [eS_eq]
  · simp

theorem eG_mul_eG [CharZero K] (T : GoodSet K G) : eG T * eG T = eG T := by
  rw [eG, Finset.sum_mul_sum]
  simp_rw [eS_mul_eS]
  simp

end PI.Dv.GLP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.IsIntegralTraceOfPow
section
noncomputable section

namespace PI.Dv.GLP

open Polynomial

theorem eigen_pow_eq_one {L : Type} [Field L] {d : Type} [Fintype d] [DecidableEq d]
    (M : Matrix d d L) (n : ℕ) (hM : M ^ n = 1) (μ : L) (hμ : M.charpoly.IsRoot μ) : μ ^ n = 1 :=
  _root_.UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one M n hM μ hμ

theorem isIntegral_trace_of_pow {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  let L := AlgebraicClosure K
  let M := LinearMap.toMatrix b b f
  have hMn : M ^ n = 1 := by
    show LinearMap.toMatrix b b f ^ n = 1
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  let M' : Matrix _ _ L := M.map (algebraMap K L)
  have hM'n : M' ^ n = 1 := by
    have : M' ^ n = (M ^ n).map (algebraMap K L) :=
      (RingHom.map_pow (algebraMap K L).mapMatrix M n).symm
    rw [this, hMn]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have htr : algebraMap K L (LinearMap.trace K W f) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b]
    exact AddMonoidHom.map_trace (algebraMap K L) M
  have hint : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun μ hμ => ?_
    have h1 : μ ^ n = 1 := eigen_pow_eq_one M' n hM'n μ (Polynomial.isRoot_of_mem_roots hμ)
    exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  rw [← htr] at hint
  exact (isIntegral_algebraMap_iff (algebraMap K L).injective).1 hint

end PI.Dv.GLP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.StarMapTraceOfPowEqOne
section
noncomputable section

namespace PI.Dv.GLPTr

open Matrix
open scoped ComplexOrder

theorem star_trace_of_pow_eq_one {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (n : ℕ) (hn : 0 < n) (hA : A ^ n = 1) :
    star A.trace = (A ^ (n - 1)).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set Q : Matrix d d ℂ := ∑ k ∈ Finset.range (m + 1), (A ^ k)ᴴ * A ^ k with hQdef
  have hQpd : Q.PosDef := by
    rw [hQdef, Finset.sum_range_succ']
    simp only [pow_zero, conjTranspose_one, one_mul]
    rw [add_comm]
    exact (PosDef.one).add_posSemidef
      (posSemidef_sum _ fun k _ => posSemidef_conjTranspose_mul_self _)
  have hAQ : Aᴴ * Q * A = Q := by
    rw [hQdef, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k, Aᴴ * ((A ^ k)ᴴ * A ^ k) * A = (A ^ (k + 1))ᴴ * A ^ (k + 1) := by
      intro k
      rw [pow_succ, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [this]
    have key : ∀ F : ℕ → Matrix d d ℂ, F (m + 1) = F 0 →
        ∑ x ∈ Finset.range (m + 1), F (x + 1) = ∑ x ∈ Finset.range (m + 1), F x := by
      intro F hF
      rw [Finset.sum_range_succ, Finset.sum_range_succ' F, hF]
    exact key (fun k => (A ^ k)ᴴ * A ^ k) (by simp [hA])
  have hAQ' : Aᴴ * Q = Q * A ^ m := by
    have h2 : Aᴴ * Q * A * A ^ m = Q * A ^ m := by rw [hAQ]
    rw [Matrix.mul_assoc, ← pow_succ', hA, Matrix.mul_one] at h2
    exact h2
  have hU : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQpd.isUnit
  have hinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hU
  have hinv' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hU
  calc star A.trace = (Aᴴ).trace := (trace_conjTranspose A).symm
    _ = (Aᴴ * (Q * Q⁻¹)).trace := by rw [hinv, Matrix.mul_one]
    _ = (Q⁻¹ * (Aᴴ * Q)).trace := by rw [← Matrix.mul_assoc, trace_mul_comm]
    _ = (A ^ m).trace := by rw [hAQ', ← Matrix.mul_assoc, hinv', Matrix.one_mul]

theorem star_map_trace_of_pow_eq_one {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : K →+* ℂ) (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    star (σ (LinearMap.trace K W f)) = σ (LinearMap.trace K W (f ^ (n - 1))) := by
  classical
  let b := Module.finBasis K W
  obtain ⟨A, hAdef⟩ : ∃ A, LinearMap.toMatrix b b f = A := ⟨_, rfl⟩
  have hpow : ∀ k, LinearMap.toMatrix b b (f ^ k) = A ^ k := fun k => by
    rw [← LinearMap.toMatrix_pow, hAdef]
  have hmap : ∀ B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K,
      σ B.trace = (B.map σ).trace := fun B => AddMonoidHom.map_trace σ B
  have hmp : ∀ k, (A ^ k).map σ = (A.map σ) ^ k := fun k => RingHom.map_pow σ.mapMatrix A k
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b, hAdef, hpow, hmap,
    hmap, hmp]
  refine star_trace_of_pow_eq_one (A.map σ) n hn ?_
  rw [← hmp, ← hpow, hf, LinearMap.toMatrix_one]
  exact Matrix.map_one σ (map_zero σ) (map_one σ)

theorem star_map_trace_rep {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (σ : K →+* ℂ)
    (τ : Representation K G W) (g : G) :
    star (σ (LinearMap.trace K W (τ g))) = σ (LinearMap.trace K W (τ g⁻¹)) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [star_map_trace_of_pow_eq_one σ (τ g) (Fintype.card G) hn
    (by rw [← map_pow, pow_card_eq_one, map_one])]
  congr 2
  rw [← map_pow]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn, pow_card_eq_one]

end PI.Dv.GLPTr
end
end

