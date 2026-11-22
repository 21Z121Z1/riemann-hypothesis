import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EePosFalseDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEq
section
noncomputable section
open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois.LevelT

theorem vp_cmul {K : Type} [Field K] [CharZero K] (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    vp p (cmul f g) r = cmul (vp p f) (vp p g) r := by
  by_cases h : p ∣ r
  · obtain ⟨r', rfl⟩ := h
    rw [UpSplit.cmul_vp_vp p hp]
    simp [vp, Nat.mul_div_cancel_left _ hp]
  · rw [show vp p (cmul f g) r = 0 by simp [vp, h]]
    unfold cmul
    symm
    apply sum_eq_zero
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    by_cases hpi : p ∣ i
    · have : ¬ p ∣ r - i := by
        intro h2
        apply h
        have := Nat.dvd_add h2 hpi
        rwa [Nat.sub_add_cancel hi'] at this
      simp [vp, this]
    · simp [vp, hpi]

theorem cauchyProduct_fourfold_finsetSum {K : Type} [Field K] {α : Type} (s₁ s₂ s₃ s₄ : Finset α) (f g : α → α → ℕ → K) (r : ℕ) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, cmul (f a b) (g c d) r =
      cmul (fun i => ∑ a ∈ s₁, ∑ b ∈ s₂, f a b i) (fun i => ∑ c ∈ s₃, ∑ d ∈ s₄, g c d i) r := by
  unfold cmul
  simp_rw [Finset.sum_comm (s := s₄) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₃) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₂) (t := range (r + 1))]
  simp_rw [Finset.sum_comm (s := s₁) (t := range (r + 1))]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]; refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]; refine sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

theorem dvd_castHom_val_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_preimage_fibre (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [CommRing K]
    (X : Finset (GL (Fin 2) (ZMod (p ^ n))))
    (hX : ∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val)
    (G : GL (Fin 2) (ZMod (p ^ n)) → K)
    (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K) :
    ∑ γ ∈ (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X),
      G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) =
    ∑ γ ∈ X, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hS : (univ.filter fun γ : GL (Fin 2) (ZMod (p ^ (n + 1))) => Matrix.GeneralLinearGroup.map ρ γ ∈ X) =
      (unitSet p (n + 1)).filter (fun γ => Matrix.GeneralLinearGroup.map ρ γ ∈ X) := by
    ext γ
    simp only [mem_filter, mem_univ, true_and, unitSet]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := hX _ h
      have e1 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) := rfl
      have e2 : ((Matrix.GeneralLinearGroup.map ρ γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0 = ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) := rfl
      rw [e1, hρ, dvd_castHom_val_iff hn] at h1
      rw [e2, hρ, dvd_castHom_val_iff hn] at h2
      exact ⟨⟨h1, h2⟩, h⟩
    · exact fun h => h.2
  have hX' : (unitSet p n).filter (fun γ => γ ∈ X) = X := by
    ext γ
    simp only [mem_filter, unitSet, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hX γ h, h⟩⟩
  rw [hS, Finset.sum_filter]
  have h1 := GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre p n K (fun g => if g ∈ X then G g else 0) Φ hn
  simp only [ite_mul, zero_mul] at h1
  rw [h1, ← Finset.sum_filter, hX']

end GlobalTheory.KummerEisensteinGalois.LevelT

open GlobalTheory.KummerEisensteinGalois.LevelT in

theorem GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  intro p _ N n m k K _ _ ψ c d w w' v v' ζ X hζ hN hpN hm hmn hk hc hd h1 h2 h3 h4 hX r
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hn : 1 ≤ n := le_trans hm hmn
  have hdet : ∀ γ : GL (Fin 2) (ZMod (p ^ (n + 1))),
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) =
      ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) := by
    intro γ
    have hcast : ∀ {a : ℕ} [NeZero a] (y : ZMod a) (h : p ^ m ∣ a),
        ((y.val : ℕ) : ZMod (p ^ m)) = ZMod.castHom h (ZMod (p ^ m)) y := by
      intro a _ y h
      rw [ZMod.castHom_apply, ZMod.natCast_val]
    have e : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) =
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) := rfl
    rw [hcast _ (pow_dvd_pow p (by omega : m ≤ n + 1)), hcast _ (pow_dvd_pow p hmn), e, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have hRHS : vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
        ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    unfold vp pieceT
    split_ifs <;> simp
  rw [hRHS]
  unfold pieceT
  have hsum := sum_preimage_fibre p n hn K X hX (fun γ => ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n)))).det.val : ℕ) : ZMod (p ^ m)))
    (fun y₀₀ y₀₁ y₁₀ y₁₁ => cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r)
  have hL : ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 0 v).1 (rowT N p (n + 1) γ 0 v).2)
           (smF d 1 (N * p ^ (n + 1)) ζ (rowT N p (n + 1) γ 1 v').1 (rowT N p (n + 1) γ 1 v').2) r =
      ∑ γ ∈ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X), ψ ((((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ : GL (Fin 2) (ZMod (p ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
      (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1).val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r := by
    refine sum_congr rfl fun γ _ => ?_
    rw [hdet]
    rfl
  rw [hL, hsum]
  have hp' : (p : K) ≠ 0 := by exact_mod_cast hp0.ne'
  have hj : 1 ≤ k - 1 := by omega
  have hstep : ∀ γ ∈ X,
      (∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)),
        cmul (smF c (k - 1) (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₀₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v.1) ((N : ℤ) * (y₀₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v.2))
          (smF d 1 (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁₀.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.1) ((N : ℤ) * (y₁₁.val : ℤ) + (p : ℤ) ^ (n + 1) * v'.2)) r) =
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) *
        vp p (cmul (smF c (k - 1) (N * p ^ n) (ζ ^ p) (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) (ζ ^ p) (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2)) r := by
    intro γ hγ
    have hu : ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val := by
      exact hX γ hγ
    rw [cauchyProduct_fourfold_finsetSum]
    simp only [GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n (k - 1) K ζ c ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1) v.1 v.2 w.1 w.2 hζ hN hpN hn hj hc hu.1 h1 h2,
      GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution p N n 1 K ζ d ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1) v'.1 v'.2 w'.1 w'.2 hζ hN hpN hn le_rfl hd hu.2 h3 h4]
    rw [vp_cmul p hp0]
    unfold cmul
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rowT]
    ring
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [hstep γ hγ])]
  have hsc : -((p : K) ^ (((n + 1 : ℕ) : ℤ) * ((k : ℤ) - 4))) *
      ((p : K) ^ ((2 : ℤ) - ((k - 1 : ℕ) : ℤ)) * (p : K) ^ ((2 : ℤ) - ((1 : ℕ) : ℤ))) =
      -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) := by
    rw [← zpow_add₀ hp', neg_mul, ← zpow_add₀ hp']
    congr 2
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [← hsc, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun γ _ => ?_
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOneAddXPow
section
noncomputable section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

open PowerSeries in
private theorem one_add_X_pow_eq_sum_fin_choose {R : Type} [CommRing R] (p j : ℕ) (hj : j < p) :
    (1 + X : R⟦X⟧) ^ j = ∑ i : Fin p, ((j.choose i : ℕ) : R⟦X⟧) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((j.choose i : ℕ) : R⟦X⟧) * X ^ i) p, add_comm, add_pow]
  have hsub : Finset.range (j + 1) ⊆ Finset.range p := Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub (fun i _ hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mul_comm]

open PowerSeries in
private theorem subsingleton_of_isUnit_natCast_of_isAdicComplete {R : Type} [CommRing R] (p : ℕ)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (hu : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
  constructor
  intro a b
  have h := hR.toIsHausdorff.haus (a - b) (fun n => by
    rw [htop, Ideal.top_pow, Submodule.top_smul]; exact SModEq.top)
  exact sub_eq_zero.1 h

open PowerSeries in

theorem _root_.GlobalTheory.Col.exists_basis_one_add_X_pow (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) :
    ∃ b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      (@Algebra.toModule _ _ _ _ (_root_.GlobalTheory.Col.phi (R := R) p hp.out.pos).toRingHom.toAlgebra), ∀ i, b i = (1 + X) ^ (i : ℕ) := by
  by_cases hn : (p : R) ∈ nonunits R
  · haveI := hR
    set e := _root_.GlobalTheory.Col.Model.basis (R := R) p hn
    have he : ∀ i, e i = _root_.GlobalTheory.Col.Model.toUp p (X ^ (i : ℕ)) := fun i => by
      show (_root_.GlobalTheory.Col.Model.basis (R := R) p hn) i = _
      unfold _root_.GlobalTheory.Col.Model.basis
      rw [Module.Basis.mk_apply]
      rfl
    let v : Fin p → _root_.GlobalTheory.Col.Model.Up R p :=
      fun j => _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (j : ℕ))
    have hv : ∀ j : Fin p, v j = ∑ i : Fin p, (((j : ℕ).choose i : ℕ) : R⟦X⟧) • e i := by
      intro j
      simp only [he, Algebra.smul_def, map_natCast]
      exact one_add_X_pow_eq_sum_fin_choose p j j.2
    have hrepr : ∀ j i : Fin p, e.repr (v j) i = (((j : ℕ).choose i : ℕ) : R⟦X⟧) := by
      intro j i
      rw [hv, e.repr_sum_self]
    have hdet : e.det v = 1 := by
      rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular]
      · simp [Module.Basis.toMatrix_apply, hrepr]
      · intro i j hij
        simp [Module.Basis.toMatrix_apply, hrepr, Nat.choose_eq_zero_of_lt (show (j : ℕ) < i from hij)]
    obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det e).2 (by rw [hdet]; exact isUnit_one)
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) := Module.Basis.mk hli hspan.ge
    have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hspan.ge i
    exact ⟨b, hb⟩
  · have hu : IsUnit (p : R) := by simpa [mem_nonunits_iff] using hn
    haveI := subsingleton_of_isUnit_natCast_of_isAdicComplete p hR hu
    haveI : Subsingleton R⟦X⟧ := ⟨fun a b => PowerSeries.ext fun n => Subsingleton.elim _ _⟩
    haveI : Subsingleton (_root_.GlobalTheory.Col.Model.Up R p) := ‹Subsingleton R⟦X⟧›
    haveI : Subsingleton (Fin p →₀ R⟦X⟧) := ⟨fun a b => Finsupp.ext fun i => Subsingleton.elim _ _⟩
    let b : Module.Basis (Fin p) R⟦X⟧ (_root_.GlobalTheory.Col.Model.Up R p) :=
      Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
    have hb : ∀ i, b i = _root_.GlobalTheory.Col.Model.toUp p ((1 + X) ^ (i : ℕ)) := fun i => Subsingleton.elim _ _
    exact ⟨b, hb⟩

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroup
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem avg_eig : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V,
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  intro G V _ _ _ _ _ π hπ H θ hD w
  classical
  let Hs : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  have hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1 := fun a ha => by
    rw [← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]
  have hθ0 : ∀ a ∈ H, θ a ≠ 0 := fun a ha h0 => by
    have := hθinv a ha; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hπmul : ∀ a b : G, π (a * b) w = π a (π b w) := fun a b => by rw [map_mul]; rfl
  let T : Subgroup Hs :=
    { carrier := {j | π j w = θ j • w}
      one_mem' := by simp [hD.val_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rw [hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        have h1 : w = θ a • π (a : G)⁻¹ w := by
          rw [← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]; rfl
        have h2 : θ (a : G)⁻¹ = (θ a)⁻¹ := eq_inv_of_mul_eq_one_left (hθinv a a.2)
        rw [h2]
        conv_rhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }
  haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact
  have hopen : IsOpen (T : Set Hs) := by
    apply Subgroup.isOpen_of_mem_nhds T (g := 1)
    rw [nhds_subtype_eq_comap, Filter.mem_comap]
    obtain ⟨U, hU, hUθ⟩ := hD.near
    refine ⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩
    rintro j ⟨hjU, hjw⟩
    show π j w = θ j • w
    rw [hjw, hUθ _ hjU j.2, one_smul]
  haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen
  haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _
  let f : Hs → V := fun j => (θ j)⁻¹ • π j w
  have hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hb : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = s at hab hb
    subst hb
    have hs : π s w = θ s • w := hab
    simp only [f, Subgroup.coe_mul]
    rw [hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hθ0 s s.2), mul_one]
  have hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a) := by
    intro h a
    simp only [f, Subgroup.coe_mul]
    rw [map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (hθ0 h h.2), one_mul]
  let rep : Hs ⧸ T → Hs := fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out
  have hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q := by
    intro q
    simp only [rep]
    split_ifs with hq
    · exact hq.symm
    · exact QuotientGroup.out_eq' q
  have hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q) := by
    intro h
    rw [map_sum, Finset.smul_sum]
    simp_rw [hact]
    have : ∀ q, f (h * rep q) = f (rep (h • q)) := fun q => by
      apply hf
      rw [hrep (h • q)]
      conv_rhs => rw [← hrep q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp_rw [this]
    exact Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))
  refine ⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩
    simp [rep]
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (rep q).2
  · have hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T)) := by
      intro q₁ _ q₂ _ h
      rw [← hrep q₁, ← hrep q₂, Subtype.ext h]
    rw [Finset.sum_image hinj]
    intro h hh
    exact hsum ⟨h, hh⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem exists_cocycle_extension_of_neg_action : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔtriv c hc hk φ hφS hφadd hφinv
  obtain ⟨u, hu⟩ := h2
  have hinv : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; rw [← hmul, inv_mul_cancel, hone]
  have hconj : ∀ g, ∀ δ ∈ Δ, φ (g * δ * g⁻¹) = ρ g⁻¹ (φ δ) := by
    intro g δ hδ
    rw [← hφinv g δ hδ, ← hmul, mul_inv_cancel, hone]
  have hkmul : ∀ g h : G, c * (g * h) * c⁻¹ * (g * h)⁻¹
      = (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by
    intro g h; group
  have hw : ∀ g h : G, ρ (g * h) (φ (c * (g * h) * c⁻¹ * (g * h)⁻¹))
      = ρ h (ρ g (φ (c * g * c⁻¹ * g⁻¹))) + ρ h (φ (c * h * c⁻¹ * h⁻¹)) := by
    intro g h
    rw [hkmul, hφadd _ (hk g) _ (hΔ.conj_mem _ (hk h) g), hconj g _ (hk h), hmul,
      map_add, map_add, hinv]
  have h1 : φ 1 = 0 := by
    have := hφadd 1 Δ.one_mem 1 Δ.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hneg : ∀ δ ∈ Δ, φ δ⁻¹ = -φ δ := by
    intro δ hδ
    have := hφadd δ hδ δ⁻¹ (Δ.inv_mem hδ)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  refine ⟨fun g => -(↑u⁻¹ : R) • ρ g (φ (c * g * c⁻¹ * g⁻¹)), ?_, ?_, ?_⟩
  · intro g
    exact S.smul_mem _ (hS g _ (hφS _ (hk g)))
  · intro g h
    simp only
    rw [hw, smul_add, map_smul]
  · intro δ hδ
    simp only
    have hcδ : c * δ * c⁻¹ ∈ Δ := hΔ.conj_mem _ hδ c
    have hc' : φ (c * δ * c⁻¹) = -φ δ := by
      have e1 := hφinv c δ hδ
      rw [hc _ (hφS _ hcδ)] at e1
      rw [← e1, neg_neg]
    rw [hΔtriv δ hδ, hφadd _ hcδ _ (Δ.inv_mem hδ), hc', hneg δ hδ,
      show -φ δ + -φ δ = -((2 : R) • φ δ) by rw [two_smul, neg_add],
      smul_neg, neg_smul, neg_neg, smul_smul, ← hu, Units.inv_mul, one_smul]

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_eq_exp_of_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  set n := x.den with hn
  have hn0 : 0 < n := x.den_pos
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω hn0).ne'
  have hp : IsPrimitiveRoot ζ n := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hp' : IsPrimitiveRoot (ε ζ) n := hp.map_of_injective hε
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have h := Rat.mul_den_eq_num x
    have h' : ((x : ℂ) * (n : ℂ)) = (x.num : ℂ) := by exact_mod_cast h
    rw [← h']; ring
  obtain ⟨i, -, hi⟩ := hp'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (hε : Function.Injective ε) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_eq_exp_of_rat ε hε x)

theorem eOm_props : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε → (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ k : ℤ, eOm ε (k : ℚ) = 1) ∧ (∀ x : ℚ, eOm ε x = 1 → ∃ k : ℤ, x = k) := by
  intro Ω _ _ _ ε hε
  refine ⟨eOm_spec ε hε, ?_, ?_, ?_⟩
  · intro x y
    apply hε
    rw [map_mul, eOm_spec ε hε, eOm_spec ε hε, eOm_spec ε hε, ← Complex.exp_add]
    congr 1; push_cast; ring
  · intro k
    apply hε
    rw [map_one, eOm_spec ε hε, Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  · intro x hx
    have h := eOm_spec ε hε x
    rw [hx, map_one] at h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
    refine ⟨k, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ hne
      rw [hk]; ring
    exact_mod_cast this

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem isIntegral_int_mem_every_valuationSubring {F : Type} [Field F] (V : ValuationSubring F)
    {y : F} (hy : IsIntegral ℤ y) : y ∈ V := by
  have hV : IsIntegral V y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hz]
  exact z.2

theorem valuationSubring_valuation_intCast_coprime_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    {q : ℕ} (hq : ((q : ℕ) : F) ∈ V.nonunits) {n : ℤ} (hn : IsCoprime n (q : ℤ)) :
    V.valuation (n : F) = 1 := by
  obtain ⟨a, b, hab⟩ := hn
  have hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1 := fun m =>
    (V.valuation_le_one_iff _).2 (by simp)
  have hq' : V.valuation ((q : ℕ) : F) < 1 := V.mem_nonunits_iff.1 hq
  refine le_antisymm (hint n) (not_lt.1 fun hlt => ?_)
  have hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1 := by
    have := congrArg (fun t : ℤ => (t : F)) hab
    simpa using this
  have h1 : V.valuation ((a : F) * n) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt
  have h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'
  have h3 := Valuation.map_add_lt _ h1 h2
  rw [hsum, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_finset_primes_forall_mem_valuationSubring :
    ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F),
      ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
        ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  intro F _ _ _ s
  have : Algebra.IsAlgebraic ℤ F :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩
  have hndvd : ¬ q ∣ d.natAbs := fun h =>
    hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)
  have hcop : IsCoprime d (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using this
  have hdx : (d : F) * x ∈ V := by
    have := isIntegral_int_mem_every_valuationSubring V (hd x hx)
    simpa [zsmul_eq_mul] using this
  have hv1 := valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop
  rw [← V.valuation_le_one_iff]
  have := (V.valuation_le_one_iff _).2 hdx
  rwa [map_mul, hv1, one_mul] at this

end GlobalTheory
end

