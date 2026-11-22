import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinct
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosets
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.TqPerm

theorem sl_det (g : SL(2, ℤ)) : mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0 = 1 := by
  have h := g.det_coe
  rw [Matrix.det_fin_two] at h
  exact h

theorem mem_lev (N l : ℕ) (g : SL(2, ℤ)) :
    g ∈ Lev N l ↔ (N : ℤ) ∣ mat g 0 0 - 1 ∧ (N : ℤ) ∣ mat g 1 0 ∧ (l : ℤ) ∣ mat g 1 0 := by
  have hd := sl_det g
  simp only [Lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, _, h3⟩, h4⟩
    exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨⟨h1, ?_, h3⟩, h4⟩
    have h := congrArg (Int.cast : ℤ → ZMod N) hd
    push_cast at h
    rw [h1, h3] at h
    simpa using h

theorem diam_facts {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) :
    (N : ℤ) ∣ mat σ 1 0 ∧ (l : ℤ) ∣ mat σ 1 0 ∧ (N : ℤ) ∣ mat σ 1 1 - q := by
  obtain ⟨h1, h2⟩ := h
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  refine ⟨(dvd_mul_right _ _).trans h1, (dvd_mul_left _ _).trans h1, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h2, sub_self]

def InDelta (N l q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 = q ∧ (N : ℤ) ∣ M 0 0 - 1 ∧ (N : ℤ) ∣ M 1 0 ∧ (l : ℤ) ∣ M 1 0

theorem tqFam_inDelta {N l q : ℕ} {σ : SL(2, ℤ)} (h : IsDiam N l (q : ZMod N) σ) (i : Fin (q + 1)) :
    InDelta N l q (tqFam q σ i) := by
  obtain ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩⟩ := diam_facts h
  have hd := sl_det σ
  unfold tqFam InDelta
  split_ifs with hi
  · simp
  · simp only [dg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨by linear_combination (q : ℤ) * hd, ⟨mat σ 0 1 * c1 - mat σ 0 0 * c3, ?_⟩, ⟨c1 * q, ?_⟩, ⟨c2 * q, ?_⟩⟩
    · linear_combination hd + mat σ 0 1 * h1 - mat σ 0 0 * h3
    · linear_combination (q : ℤ) * h1
    · linear_combination (q : ℤ) * h2

theorem InDelta.mul {N l q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) {g : SL(2, ℤ)}
    (hg : g ∈ Lev N l) : InDelta N l q (M * mat g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := (mem_lev N l g).1 hg
  have hd := sl_det g
  unfold InDelta
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨by linear_combination (mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0) * h0 + (q : ℤ) * hd, ?_, ?_, ?_⟩
  · have : M 0 0 * mat g 0 0 + M 0 1 * mat g 1 0 - 1
        = (M 0 0 - 1) * mat g 0 0 + (mat g 0 0 - 1) + M 0 1 * mat g 1 0 := by ring
    rw [this]
    exact dvd_add (dvd_add (h1.mul_right _) g1) (g2.mul_left _)
  · exact dvd_add (h2.mul_right _) (g2.mul_left _)
  · exact dvd_add (h3.mul_right _) (g3.mul_left _)

theorem exists_res {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : ¬ (q : ℤ) ∣ x) (y : ℤ) :
    ∃ j : ℕ, j < q ∧ (q : ℤ) ∣ y - j * x := by
  haveI := Fact.mk hq
  have hx' : (x : ZMod q) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((y : ZMod q) / x).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hx', sub_self]

theorem exists_upper {N l q : ℕ} (hq : q.Prime) (σ : SL(2, ℤ)) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : InDelta N l q M) {j : ℕ} (hj : j < q) (ha : (q : ℤ) ∣ M 0 1 - j * M 0 0)
    (hb : (q : ℤ) ∣ M 1 1 - j * M 1 0) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  obtain ⟨h0, h1, h2, h3⟩ := hM
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdet : (!![M 0 0, u; M 1 0, v] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    apply mul_left_cancel₀ hq0
    linear_combination h0 - M 0 0 * hv + M 1 0 * hu
  refine ⟨⟨j, by omega⟩, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨h1, h2, h3⟩⟩, ?_⟩
  show M = !![M 0 0, u; M 1 0, v] * _
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tqFam, hj, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hu
  · linear_combination hv

theorem exists_rep {N l q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N * l) {σ : SL(2, ℤ)}
    (hσ : IsDiam N l (q : ZMod N) σ) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : InDelta N l q M) :
    ∃ (k : Fin (q + 1)) (g : Lev N l), M = mat g * tqFam q σ k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have h0 := hM.1
  by_cases hα : (q : ℤ) ∣ M 0 0
  · by_cases hγ : (q : ℤ) ∣ M 1 0
    · obtain ⟨-, h1, h2, h3⟩ := hM
      obtain ⟨u, hu⟩ := hα
      obtain ⟨v, hv⟩ := hγ
      obtain ⟨s1, s2, s3⟩ := diam_facts hσ
      have hd := sl_det σ
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hcN : IsCoprime (N : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right _)).symm
      have hcl : IsCoprime (l : ℤ) q := Nat.isCoprime_iff_coprime.2
        ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_left _)).symm
      have hNv : (N : ℤ) ∣ v := hcN.dvd_of_dvd_mul_left (hv ▸ h2)
      have hlv : (l : ℤ) ∣ v := hcl.dvd_of_dvd_mul_left (hv ▸ h3)
      have hd' : u * M 1 1 - M 0 1 * v = 1 := by
        apply mul_left_cancel₀ hq0
        linear_combination h0 - M 1 1 * hu + M 0 1 * hv
      have hdet : (!![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] :
          Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination (u * M 1 1 - M 0 1 * v) * hd + hd'
      refine ⟨Fin.last q, ⟨⟨_, hdet⟩, (mem_lev N l _).2 ⟨?_, ?_, ?_⟩⟩, ?_⟩
      · show (N : ℤ) ∣ u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
        have : u * mat σ 1 1 - M 0 1 * mat σ 1 0 - 1
            = u * (mat σ 1 1 - q) - M 0 1 * mat σ 1 0 + (M 0 0 - 1) := by rw [hu]; ring
        rw [this]
        exact dvd_add (dvd_sub (s3.mul_left _) (s1.mul_left _)) h1
      · exact dvd_sub (hNv.mul_right _) (s1.mul_left _)
      · exact dvd_sub (hlv.mul_right _) (s2.mul_left _)
      · show M = !![u * mat σ 1 1 - M 0 1 * mat σ 1 0, -u * mat σ 0 1 + M 0 1 * mat σ 0 0;
          v * mat σ 1 1 - M 1 1 * mat σ 1 0, -v * mat σ 0 1 + M 1 1 * mat σ 0 0] * _
        ext a b
        fin_cases a <;> fin_cases b <;> simp [tqFam, dg, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination hu - q * u * hd
        · linear_combination (-M 0 1) * hd
        · linear_combination hv - q * v * hd
        · linear_combination (-M 1 1) * hd
    · obtain ⟨j, hj, hb⟩ := exists_res hq hγ (M 1 1)
      refine exists_upper hq σ hM hj ?_ hb
      have : (q : ℤ) ∣ M 1 0 * (M 0 1 - j * M 0 0) := by
        have e : M 1 0 * (M 0 1 - j * M 0 0) = M 0 0 * (M 1 1 - j * M 1 0) - q := by linear_combination -h0
        rw [e]
        exact dvd_sub (hb.mul_left _) dvd_rfl
      exact (hp.dvd_or_dvd this).resolve_left hγ
  · obtain ⟨j, hj, ha⟩ := exists_res hq hα (M 0 1)
    refine exists_upper hq σ hM hj ha ?_
    have : (q : ℤ) ∣ M 0 0 * (M 1 1 - j * M 1 0) := by
      have e : M 0 0 * (M 1 1 - j * M 1 0) = M 1 0 * (M 0 1 - j * M 0 0) + q := by linear_combination h0
      rw [e]
      exact dvd_add (ha.mul_left _) dvd_rfl
    exact (hp.dvd_or_dvd this).resolve_left hα

theorem tqFam_inj {q : ℕ} (hq : q.Prime) (σ h : SL(2, ℤ)) {i k : Fin (q + 1)}
    (e : tqFam q σ i = mat h * tqFam q σ k) : i = k := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hd := sl_det h
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have hi := i.2
  have hk := k.2
  by_cases a : (i : ℕ) < q <;> by_cases b : (k : ℕ) < q
  · simp [tqFam, a, b, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    have hdv : (q : ℤ) ∣ ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) := ⟨mat h 0 1, by linear_combination e01 - ((k : ℕ) : ℤ) * e00⟩
    have := Int.eq_zero_of_abs_lt_dvd hdv (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00
    exact hp.not_dvd_one ⟨mat h 0 0 * mat σ 0 0 + mat h 0 1 * mat σ 1 0, by linear_combination e00⟩
  · exfalso
    simp [tqFam, a, b, dg, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
    exact hp.not_dvd_one ⟨mat σ 0 0 * mat h 1 1 - mat h 0 1 * mat σ 1 0,
      by linear_combination -hd - mat h 1 1 * e00 + mat h 0 1 * e10⟩
  · exact Fin.ext (by omega)

theorem tqFam_perm : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ),
    IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l,
      tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  intro N l q _ _ _ hq hqN σ hσ γ
  choose f g hf using fun i => exists_rep hq hqN hσ ((tqFam_inDelta hσ i).mul γ.2)
  have hinj : Function.Injective f := by
    intro i k hik
    refine tqFam_inj hq σ ((g i : SL(2, ℤ)) * (g k : SL(2, ℤ))⁻¹) ?_
    have h1 : mat γ * mat (γ : SL(2, ℤ))⁻¹ = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : mat (g k : SL(2, ℤ))⁻¹ * mat (g k) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc tqFam q σ i = tqFam q σ i * mat γ * mat (γ : SL(2, ℤ))⁻¹ := by rw [mul_assoc, h1, mul_one]
      _ = mat (g i) * (mat (g k : SL(2, ℤ))⁻¹ * mat (g k)) * tqFam q σ (f k) * mat (γ : SL(2, ℤ))⁻¹ := by
          rw [hf i, hik, h2, mul_one]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * (mat (g k) * tqFam q σ (f k)) * mat (γ : SL(2, ℤ))⁻¹ := by
          simp only [mul_assoc]
      _ = mat (g i) * mat (g k : SL(2, ℤ))⁻¹ * tqFam q σ k := by
          rw [← hf k, mul_assoc, mul_assoc (tqFam q σ k), h1, mul_one]
      _ = _ := by rw [← Matrix.SpecialLinearGroup.coe_mul]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => ⟨g i, hf i⟩⟩

end GlobalTheory.TqPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatrix
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section
namespace GlobalTheory.Hk.UDia

def gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a*d - b*q*c - a*j*c, a*b + b*j'*c + a*Y; c*d - c^2*j - c*d*q, a*d + c*d*j' + c*Y]

theorem det_gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) : (gam a b c d j j' q Y).det = 1 := by
  rw [gam, Matrix.det_fin_two_of]
  subst hY
  linear_combination (a*d - (a*j + j*j'*c - j'*d - q*Y)*c + 1) * hdet

theorem alg (a b c d Y t w z j j' q : ℂ) (hq : q ≠ 0) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) (hwq : w*q = t + j)
    (hzq : z*q*(c*t+d) = a*t + b + j'*(c*t+d)) :
    a*w + b = (c*t+d) * ((a*d - b*q*c - a*j*c) * z + (a*b + b*j'*c + a*Y)) ∧
    c*w + d = (c*t+d) * ((c*d - c^2*j - c*d*q) * z + (a*d + c*d*j' + c*Y)) := by
  subst hY
  constructor
  · apply mul_left_cancel₀ hq
    linear_combination a*hwq - (a*d - (a*j + j*j'*c - j'*d - q*Y)*q*c - a*j*c)*hzq
      - (a*(t+j) + (a*j + j*j'*c - j'*d - q*Y)*q)*hdet
  · apply mul_left_cancel₀ hq
    linear_combination c*hwq - (c*d - c^2*j - c*d*q)*hzq - (c*(t+j) + d*q)*hdet

theorem key {N l q : ℕ} {k : ℤ} (f : ModularForm (GlobalTheory.Hk.lev N l) k) (ρ : SL(2, ℤ))
    (hcN : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) (hq : 0 < q) (j j' : ℕ) (Y : ℤ)
    (hY : ρ 0 1 = ρ 0 0 * j + j * j' * ρ 1 0 - j' * ρ 1 1 - q * Y) (τ : ℍ) :
    (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + j) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q)) * denom ρ τ ^ (-k) := by
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set γ : SL(2, ℤ) := ⟨gam (ρ 0 0) (ρ 0 1) (ρ 1 0) (ρ 1 1) j j' q Y,
    det_gam _ _ _ _ _ _ _ _ hdetZ hY⟩ with hγdef
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hN : ((ρ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdiv)
  have hl : ((ρ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdiv)
  have hγ : γ ∈ GlobalTheory.Hk.lev N l := by
    refine Subgroup.mem_inf.mpr ⟨(Gamma1_mem _ _).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩
    · have e : γ 0 0 = 1 + ρ 1 0 * (ρ 0 1 - ρ 0 1 * q - ρ 0 0 * j) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 1 = 1 + ρ 1 0 * (ρ 0 1 + ρ 1 1 * j' + Y) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hl]; ring
  have hpos : ∀ x : ℍ, ∀ n : ℕ, 0 < (((x : ℂ) + n) / q).im := by
    intro x n
    have := x.im_pos
    rw [Complex.div_natCast_im]; simp; positivity
  set w : ℍ := ofComplex (((τ : ℂ) + j) / q) with hwdef
  set z : ℍ := ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q) with hzdef
  have hwc : (w : ℂ) = ((τ : ℂ) + j) / q := by rw [hwdef, ofComplex_apply_of_im_pos (hpos τ j)]
  have hzc : (z : ℂ) = (((ρ • τ : ℍ) : ℂ) + j') / q := by
    rw [hzdef, ofComplex_apply_of_im_pos (hpos (ρ • τ) j')]
  have hu : ((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero ρ τ; rwa [ModularGroup.denom_apply] at this
  have hρτ : ((ρ • τ : ℍ) : ℂ) = (((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ)) /
      (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hwq : (w : ℂ) * q = τ + j := by rw [hwc]; field_simp
  have hzq : (z : ℂ) * q * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) =
      ((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ) + (j' : ℂ) * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [hzc, div_mul_cancel₀ _ hqC, hρτ, add_mul, div_mul_cancel₀ _ hu]
  have hdetC : ((ρ 0 0 : ℤ) : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - ((ρ 0 1 : ℤ) : ℂ) * ((ρ 1 0 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hdetZ
  have hYC : ((ρ 0 1 : ℤ) : ℂ) = ((ρ 0 0 : ℤ) : ℂ) * (j : ℂ) + (j : ℂ) * (j' : ℂ) * ((ρ 1 0 : ℤ) : ℂ)
      - (j' : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - (q : ℂ) * (Y : ℂ) := by exact_mod_cast hY
  obtain ⟨hA, hB⟩ := alg _ _ _ _ (Y : ℂ) (τ : ℂ) (w : ℂ) (z : ℂ) (j : ℂ) (j' : ℂ) (q : ℂ) hqC hdetC hYC hwq hzq
  have hγ10 : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero γ z; rwa [ModularGroup.denom_apply] at this
  have hsm : ρ • w = γ • z := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [hγdef, gam, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hA, hB, mul_div_mul_left _ _ hu]
  have hden : denom ρ w = denom ρ τ * denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularGroup.denom_apply, hB]
    simp only [hγdef, gam]
    simp
  rw [ModularForm.SL_slash_apply, hsm, SlashInvariantForm.slash_action_eqn_SL'' f hγ z, hden, mul_zpow]
  have h1 := denom_ne_zero ρ τ
  have h2 := denom_ne_zero γ z
  rw [zpow_neg, zpow_neg]
  field_simp

theorem cast_toNat_emod {q : ℕ} (hq : 0 < q) (x : ℤ) :
    (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (x : ZMod q) := by
  have h0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  rw [show (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (((x % (q : ℤ)).toNat : ℤ) : ZMod q) by
    push_cast; rfl, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem toNat_emod_lt {q : ℕ} (hq : 0 < q) (x : ℤ) : (x % (q : ℤ)).toNat < q := by
  have h1 : x % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  omega

theorem eq_of_cast_eq {q : ℕ} {i i' : ℕ} (hi : i < q) (hi' : i' < q)
    (h : (i : ZMod q) = (i' : ZMod q)) : i = i' := by
  haveI : NeZero q := ⟨by omega⟩
  rw [← ZMod.val_cast_of_lt hi, ← ZMod.val_cast_of_lt hi', h]

end GlobalTheory.Hk.UDia

open GlobalTheory.Hk.UDia in

theorem GlobalTheory.Hk.uOp_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime →
    q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q k d ρ _ _ hqp hqNl hρ f
  have hq : 0 < q := hqp.pos
  have hcN := hρ.1
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hcq : ((ρ 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by exact_mod_cast hqNl) hdiv)
  have had : ((ρ 0 0 : ℤ) : ZMod q) * ((ρ 1 1 : ℤ) : ZMod q) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod q)) hdetZ
    push_cast at h; rw [hcq] at h; linear_combination h
  set a : ℤ := ρ 0 0
  set b : ℤ := ρ 0 1
  set dd : ℤ := ρ 1 1
  let φ : ℕ → ℕ := fun i => ((a * (a * i - b)) % (q : ℤ)).toNat
  let ψ : ℕ → ℕ := fun i => ((dd * (dd * i + b)) % (q : ℤ)).toNat
  funext τ
  simp only [GlobalTheory.Hk.dia]
  rw [ModularForm.SL_slash_apply]
  simp only [GlobalTheory.Hk.uOp]
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range q, (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + i) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + (φ i : ℕ)) / q)) * denom ρ τ ^ (-k) := by
    intro i _
    have hX : ((q : ℕ) : ℤ) ∣ a * i + i * (φ i) * ρ 1 0 - (φ i) * dd - b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [cast_toNat_emod hq, hcq]
      push_cast
      linear_combination (-(((a : ℤ) : ZMod q) * i - b)) * had
    obtain ⟨Y, hY⟩ := hX
    exact key f ρ hcN hq i (φ i) Y (by linear_combination -hY) τ
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' φ ψ ?_ ?_ ?_ ?_ ?_
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i - dd * b) * had
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i + a * b) * had
  · intro i _; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem inert_fixes_root_of_unit_ratio (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω) :
    0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N →
      B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  intro hN hvN hin hgc hc hgθ hvθ
  set v := B.valuation
  by_cases hθ : θ = 0
  · simp [hθ]
  set u := θ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hθ hc
  have hvu : v u = 1 := by
    have h1 : v u ^ N = 1 := by rw [← map_pow, hu, div_pow]; exact hvθ
    exact (pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1
  have hgu : g u = g θ / c := by rw [hu, map_div₀, hgc]
  have hguN : (g u) ^ N = u ^ N := by
    rw [← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]
  set ξ := g u / u with hξ
  have hξN : ξ ^ N = 1 := by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]
  have hvξ1 : v (ξ - 1) < 1 := by
    have h2 : ξ - 1 = (g u - u) / u := by rw [hξ, sub_div, div_self hu0]
    rw [h2, map_div₀, hvu, div_one]
    exact hin u hvu.le
  have hvξ : v ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))
  have hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1 := by
    intro j
    have h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1) := (geom_sum_mul ξ j).symm
    rw [h3, map_mul]
    have h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 :=
      Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)
    calc v (∑ i ∈ Finset.range j, ξ ^ i) * v (ξ - 1) ≤ 1 * v (ξ - 1) := mul_le_mul_left h4 _
      _ = v (ξ - 1) := one_mul _
      _ < 1 := hvξ1
  set S := ∑ i ∈ Finset.range N, ξ ^ i with hS
  have hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [hS, Finset.sum_sub_distrib]; simp
  have hvSN : v (S - (N : Ω)) < 1 := by
    rw [hSN]; exact Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hvN] at hvSN
    exact lt_irrefl _ hvSN
  have hmul : S * (ξ - 1) = 0 := by rw [hS, geom_sum_mul, hξN, sub_self]
  have hξ1 : ξ = 1 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hS0
    · exact sub_eq_zero.mp h
  have : g u = u := by
    rw [hξ, div_eq_one_iff_eq hu0] at hξ1; exact hξ1
  rw [hgu, hu] at this
  exact (div_left_inj' hc).mp this

end GlobalTheory
end

