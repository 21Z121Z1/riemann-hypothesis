import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  first | exact @GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | exact GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | (intros; apply GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement
section
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_conditions_theorem_T_large_prime : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l → 2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧ 8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  first | exact @GlobalTheory.numerical_bounds_of_forty_mul_lt | exact GlobalTheory.numerical_bounds_of_forty_mul_lt | (intros; apply GlobalTheory.numerical_bounds_of_forty_mul_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

def IsUnrExt (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) : Prop :=
  K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧
    @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d

variable {K K' : UQ}

def overExt (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) : InvAlg K' :=
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := by
    obtain ⟨S, hS⟩ := B.fd.fg_top
    refine ⟨⟨S, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.E (S : Set B.A) := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  { A := B.A
    σ := B.σ
    σ_σ := B.σ_σ
    σ_alg := hσ
    g := B.g }

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAlgebraMapInjectiveOfCharZero
section
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem padicInt_algebraMap_injective_of_charZero {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff hx0 : ℤ_[l])) :=
    (PadicInt.unitCoeff hx0).isUnit.map _
  have hp : (l : O) ^ x.valuation = 0 := (mul_eq_zero.1 hx).resolve_left hu.ne_zero
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (pow_eq_zero_iff'.1 hp).1

theorem exists_eq_X_pow_mul_of_ne_zero {O : Type} [CommRing O] {a : O⟦X⟧} (ha : a ≠ 0) :
    ∃ (m : ℕ) (w : O⟦X⟧), a = X ^ m * w ∧ constantCoeff w ≠ 0 := by
  refine ⟨a.order.toNat, a.divXPowOrder, X_pow_order_mul_divXPowOrder.symm, ?_⟩
  rw [constantCoeff_divXPowOrder]
  exact coeff_order ha

theorem X_pow_card_dvd_of_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (a : O⟦X⟧)
    (h0 : constantCoeff a = 0) (ha : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) :
    (X : O⟦X⟧) ^ Nat.card Δ ∣ a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact dvd_zero _
  obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero ha0
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [pow_zero, one_mul] at h0
      exact absurd h0 hw
    · exact h
  have hpow : ∀ δ ∈ Δ, (δ : ℤ_[l]) ^ m = 1 := by
    intro δ hδ
    obtain ⟨v, hv, hv0⟩ := exists_act_X (O := O) (δ : ℤ_[l])
    have e := ha δ hδ
    rw [map_mul, map_pow, hv, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero m X_ne_zero) e
    have e'' := congrArg constantCoeff e'
    rw [map_mul, map_pow, hv0, constantCoeff_act] at e''
    have h1 : (algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m = 1 := by
      have h2 : ((algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m - 1) * constantCoeff w = 0 := by
        rw [sub_mul, one_mul, e'', sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
    apply padicInt_algebraMap_injective_of_charZero O
    rw [map_pow, h1, map_one]
  have hexp : Monoid.exponent Δ ∣ m := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    apply Units.ext
    simp [hpow g g.2]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact (pow_dvd_pow X (Nat.le_of_dvd hm hexp)).trans (dvd_mul_right _ _)

theorem X_pow_dvd_mk_sub_sum {O : Type} [CommRing O] (c : ℕ → O) (N : ℕ) :
    (X : O⟦X⟧) ^ N ∣ PowerSeries.mk c - ∑ k ∈ Finset.range N, C (c k) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [map_sum, hm]

theorem injective_and_range_eq_invariants {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : Associated (j X) (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (j X) = j X) :
    Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a := by
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨u, hu⟩ := hj
  have hjX0 : j X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact pow_ne_zero _ X_ne_zero hu.symm
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have e : j X = X ^ Nat.card Δ * ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact (dvd_pow_self (X : O⟦X⟧) hd.ne').mul_right _
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero hb0
    rw [map_mul, map_pow] at hb
    rcases mul_eq_zero.1 hb with h | h
    · exact pow_ne_zero m hjX0 h
    · apply hw
      rw [← constantCoeff_algHom j hXj w, h, map_zero]
  have hact : ∀ δ ∈ Δ, (act O (δ : ℤ_[l])).comp j = j := fun δ hδ =>
    algHom_ext_X _ _ (by rw [AlgHom.comp_apply, hinv δ hδ]; exact hXj)
      (by rw [AlgHom.comp_apply, hinv δ hδ])
  have hstep : ∀ q : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q) →
      ∃ q' : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q' = q') ∧
        q = C (constantCoeff q) + j X * q' := by
    intro q hq
    have h0 : constantCoeff (q - C (constantCoeff q)) = 0 := by simp
    have hi : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (q - C (constantCoeff q)) = q - C (constantCoeff q) := by
      intro δ hδ
      rw [map_sub, hq δ hδ, act_C]
    obtain ⟨r, hr⟩ := X_pow_card_dvd_of_invariant Δ _ h0 hi
    have hq' : q - C (constantCoeff q) = j X * (↑u * r) := by rw [hr, ← mul_assoc, hu]
    refine ⟨↑u * r, fun δ hδ => ?_, by rw [← hq']; ring⟩
    apply mul_left_cancel₀ hjX0
    rw [← hq', ← hinv δ hδ, ← map_mul, ← hq', hi δ hδ]
  choose f hf1 hf2 using hstep
  refine ⟨hinj, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ δ hδ
    exact DFunLike.congr_fun (hact δ hδ) b
  · intro ha
    let S := {q : O⟦X⟧ // ∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q}
    let nxt : S → S := fun q => ⟨f q.1 q.2, hf1 q.1 q.2⟩
    let sq : ℕ → S := fun n => nxt^[n] ⟨a, ha⟩
    let c : ℕ → O := fun k => constantCoeff (sq k).1
    have hexp : ∀ N, a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := by
      intro N
      induction N with
      | zero => simp [sq]
      | succ N ih =>
        have e1 : (sq (N + 1)).1 = f (sq N).1 (sq N).2 := by
          simp only [sq, Function.iterate_succ_apply']
          rfl
        have e2 : (sq N).1 = C (c N) + j X * (sq (N + 1)).1 := by
          rw [e1]
          exact hf2 _ _
        calc a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := ih
          _ = ∑ k ∈ Finset.range N, C (c k) * j X ^ k +
              j X ^ N * (C (c N) + j X * (sq (N + 1)).1) := by rw [← e2]
          _ = _ := by rw [Finset.sum_range_succ]; ring
    have hjsum : ∀ N, j (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
        ∑ k ∈ Finset.range N, C (c k) * j X ^ k := by
      intro N
      simp [map_sum, algHom_C]
    have hdvd : ∀ N, (X : O⟦X⟧) ^ N ∣ j (PowerSeries.mk c) - a := by
      intro N
      obtain ⟨r, hr⟩ := X_pow_dvd_mk_sub_sum c N
      have e3 : PowerSeries.mk c = ∑ k ∈ Finset.range N, C (c k) * X ^ k + X ^ N * r := by
        rw [← hr]
        ring
      have e4 : j (PowerSeries.mk c) - a = j X ^ N * (j r - (sq N).1) := by
        conv_lhs => rw [e3, map_add, map_mul, map_pow, hjsum, hexp N]
        ring
      rw [e4]
      exact (pow_dvd_pow_of_dvd hXj N).trans (dvd_mul_right _ _)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    have h' := (X_pow_dvd_iff.1 (hdvd (n + 1))) n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at h'
    exact h'

end GlobalTheory.CycFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntContinuousHomNormalizeOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_continuous_hom_normalize_one : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  first | exact @GlobalTheory.padicInt_hom_normalize | exact GlobalTheory.padicInt_hom_normalize | (intros; apply GlobalTheory.padicInt_hom_normalize <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjective
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

theorem image_lattice : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → V →ₗ[k⸨X⸩] W), (∀ i, Function.Surjective (f i)) → (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) → (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) → ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) → let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧); (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]

end GlobalTheory.PhiGam.Img
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubDvdChoosePrimePowOfLtStatement
section
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt : ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  first | exact @GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | exact GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | (intros; apply GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
section
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  first | exact @GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | exact GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | (intros; apply GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOneSubBoundedBelowOfSummableStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_one_sub_bounded_below_of_summable : ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s → ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  first | exact @GlobalTheory.prod_one_sub_bounded_below | exact GlobalTheory.prod_one_sub_bounded_below | (intros; apply GlobalTheory.prod_one_sub_bounded_below <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  first | exact @GlobalTheory.projective_compHom_of_free_of_finite_free | exact GlobalTheory.projective_compHom_of_free_of_finite_free | (intros; apply GlobalTheory.projective_compHom_of_free_of_finite_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCardStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  first | exact @GlobalTheory.quot_pow_maximal_charP_local_card | exact GlobalTheory.quot_pow_maximal_charP_local_card | (intros; apply GlobalTheory.quot_pow_maximal_charP_local_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientEquivRestrictedComponentFamiliesStatement
section
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_equiv_restrictedComponentFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  first | exact @GlobalTheory.quotient_equiv_restrictedFamilies | exact GlobalTheory.quotient_equiv_restrictedFamilies | (intros; apply GlobalTheory.quotient_equiv_restrictedFamilies <;> assumption)
end

