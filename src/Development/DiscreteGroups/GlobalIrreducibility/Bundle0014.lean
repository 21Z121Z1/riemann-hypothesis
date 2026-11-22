import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Development.DiscreteGroups.GlobalIrreducibility.LConvKMCore

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFpSupp
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k]

theorem eq_zero_of_eq_inv_mul {ψ : AddChar k Circle} {s : k} (hs : ψ s ≠ 1) {z : ℂ}
    (h : z = (((ψ s)⁻¹ : Circle) : ℂ) * z) : z = 0 := by
  have hc : ((ψ s)⁻¹ : Circle) ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have hc' : (((ψ s)⁻¹ : Circle) : ℂ) ≠ 1 := fun h' => hc (Circle.ext (by rw [h', Circle.coe_one]))
  have h0 : ((((ψ s)⁻¹ : Circle) : ℂ) - 1) * z = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hc')

theorem vanish_perm {k' : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin (k' + 1)) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin (k' + 1)), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k (k' + 1), ∀ x, W (x * b) = W x)
    (π : Equiv.Perm (Fin (k' + 1))) (hπ : π ≠ 1) (b : GL (Fin (k' + 1)) k) (hb : b ∈ lowB k (k' + 1)) :
    W (GroundTheory.Automorphic.permGL k π * b) = 0 := by
  obtain ⟨i, hi⟩ := exists_descent π⁻¹ (inv_ne_one.2 hπ)
  obtain ⟨s, hs⟩ := AddChar.ne_one_iff.1 hψ
  have hne : i.succ ≠ i.castSucc := (ne_of_lt Fin.castSucc_lt_succ).symm
  have ha : (Pi.single i.castSucc s : Fin (k' + 1) → k) i.succ = 0 := by rw [Pi.single_apply, if_neg hne]
  have hemem : colElt (Pi.single i.castSucc s) i.succ ha ∈ unipB k (Fin (k' + 1)) := colElt_mem _ _ ha fun r hr => by
    rw [Pi.single_apply, if_neg (ne_of_gt (lt_trans Fin.castSucc_lt_succ hr))]
  have hesd : superDiag (colElt (Pi.single i.castSucc s) i.succ ha) = s := by
    rw [superDiag_colElt, Pi.single_eq_same]
  have hf : (GroundTheory.Automorphic.permGL k π)⁻¹ * colElt (Pi.single i.castSucc s) i.succ ha *
      GroundTheory.Automorphic.permGL k π ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply, colElt_apply, Matrix.one_apply_ne (π.injective.ne (ne_of_lt hrc))]
    by_cases hc : π c = i.succ
    · have hr : π r ≠ i.castSucc := by
        intro hr
        have h1' : π⁻¹ i.succ = c := by rw [← hc]; simp
        have h2' : π⁻¹ i.castSucc = r := by rw [← hr]; simp
        rw [h1', h2'] at hi
        exact absurd hrc (not_lt.2 hi.le)
      rw [if_pos hc, Pi.single_apply, if_neg hr, zero_add]
    · rw [if_neg hc, zero_add]
  have key : W (GroundTheory.Automorphic.permGL k π * b) =
      (((ψ s)⁻¹ : Circle) : ℂ) * W (GroundTheory.Automorphic.permGL k π * b) := by
    have e1 : colElt (Pi.single i.castSucc s) i.succ ha * (GroundTheory.Automorphic.permGL k π * b) =
        GroundTheory.Automorphic.permGL k π * (((GroundTheory.Automorphic.permGL k π)⁻¹ *
          colElt (Pi.single i.castSucc s) i.succ ha * GroundTheory.Automorphic.permGL k π) * b) := by group
    have := h1 _ hemem (GroundTheory.Automorphic.permGL k π * b)
    rw [hesd, e1, h2 _ (mul_mem hf hb), ← h2 b hb (GroundTheory.Automorphic.permGL k π)] at this
    exact this
  exact eq_zero_of_eq_inv_mul hs key

theorem supp {m : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin m) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin m), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k m, ∀ x, W (x * b) = W x) (x : GL (Fin m) k) (hx : W x ≠ 0) :
    ∃ u ∈ unipB k (Fin m), ∃ b ∈ lowB k m, x = u * b := by
  cases m with
  | zero => exact ⟨1, one_mem _, x, mem_lowB.2 fun i => i.elim0, (one_mul x).symm⟩
  | succ k' =>
  have hww : ∀ z, longElt (k' + 1) k * (longElt (k' + 1) k * z) = z := fun z => by
    rw [← mul_assoc, longElt_mul_self, one_mul]
  obtain ⟨σ, hσ⟩ := GroundTheory.Automorphic.exists_mem_doubleCoset_permGL (x * longElt (k' + 1) k)
  obtain ⟨b1, hb1, b2, hb2, he⟩ := DoubleCoset.mem_doubleCoset.1 hσ
  have hb2' : longElt (k' + 1) k * b2 * longElt (k' + 1) k ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun i j hij => ?_
    rw [Units.val_mul, Units.val_mul, mul_longElt_apply, longElt_mul_apply]
    exact (GroundTheory.Automorphic.mem_borel_iff b2).1 hb2 _ _ (Fin.rev_lt_rev.2 hij)
  have hd : ∀ i, (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i ≠ 0 :=
    GroundTheory.Automorphic.borel_diag_ne_zero hb1
  let t : GL (Fin (k' + 1)) k := ⟨diagonal fun i => (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i,
    diagonal fun i => ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd i)⟩
  have hu : b1 * t⁻¹ ∈ unipB k (Fin (k' + 1)) := by
    refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i j = 0
      rw [mul_diagonal, (GroundTheory.Automorphic.mem_borel_iff b1).1 hb1 i j hji, zero_mul]
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i i = 1
      rw [mul_diagonal, mul_inv_cancel₀ (hd i)]
  have hPw : GroundTheory.Automorphic.permGL k σ * longElt (k' + 1) k = GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) := by
    rw [longElt_eq_permGL, map_mul]
  have ht : (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) ∈
      lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply]
    exact diagonal_apply_ne _ ((σ * Fin.revPerm).injective.ne (ne_of_lt hrc))
  have hx' : x = b1 * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) * (longElt (k' + 1) k * b2 * longElt (k' + 1) k) := by
    calc x = x * longElt (k' + 1) k * longElt (k' + 1) k := by rw [mul_assoc, longElt_mul_self, mul_one]
    _ = b1 * GroundTheory.Automorphic.permGL k σ * b2 * longElt (k' + 1) k := by rw [he]
    _ = _ := by rw [← hPw]; simp only [mul_assoc, hww]
  have hx'' : x = (b1 * t⁻¹) * (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) *
      (((GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm)) *
        (longElt (k' + 1) k * b2 * longElt (k' + 1) k))) := by
    rw [hx']; group
  by_cases hπ : σ * Fin.revPerm = 1
  · refine ⟨b1 * t⁻¹, hu, _, mul_mem ht hb2', ?_⟩
    rw [hx'', hπ, map_one, one_mul]
  · exfalso
    apply hx
    have h0 := vanish_perm ψ hψ W h1 h2 _ hπ _ (mul_mem ht hb2')
    rw [hx'', h1 _ hu, h0, mul_zero]

end DiscreteGroups.sglob.DzFp
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFpVec
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_ne_zero_of_ne {l : Module.Dual ℂ V} (h0 : l ≠ 0) : ∃ v, l v ≠ 0 := by
  by_contra h
  push_neg at h
  exact h0 (LinearMap.ext h)

theorem chi_mul {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) {u u' : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    (hu' : u' ∈ unipB k (Fin n)) :
    (ψ (superDiag (u * u')) : ℂ) = ψ (superDiag u) * ψ (superDiag u') := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_ne h0
  have e1 := hl (u * u') (mul_mem hu hu') v
  rw [map_mul, Module.End.mul_apply, hl u hu, hl u' hu'] at e1
  have : ((ψ (superDiag (u * u')) : ℂ) - ψ (superDiag u) * ψ (superDiag u')) * l v = 0 := by
    rw [sub_mul, ← e1]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)

theorem exists_eigen [Fintype k] [DecidableEq k] {n : ℕ} {ψ : AddChar k Circle}
    {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) :
    ∃ v, l v ≠ 0 ∧ ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v := by
  classical
  obtain ⟨v0, hv0⟩ := exists_ne_zero_of_ne h0
  refine ⟨∑ u : unipB k (Fin n), ((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0, ?_, fun u' hu' => ?_⟩
  · have hterm : ∀ u : unipB k (Fin n), l (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0) = l v0 := fun u => by
      rw [map_smul, hl _ u.2, smul_eq_mul, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    rw [map_sum]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨1⟩).ne') hv0
  · have hχ : ∀ w : unipB k (Fin n), (ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
        GL (Fin n) k)) : ℂ) = (ψ (superDiag u') : ℂ)⁻¹ * ψ (superDiag (w : GL (Fin n) k)) := fun w => by
      have := chi_mul hl h0 hu' (mul_mem (inv_mem hu') w.2)
      rw [mul_inv_cancel_left] at this
      rw [this, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
      rfl
    rw [map_sum, Finset.smul_sum]
    set a : unipB k (Fin n) := ⟨u', hu'⟩ with ha
    set F : unipB k (Fin n) → V := fun w =>
      ((ψ (superDiag ((a⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 with hF
    calc ∑ u : unipB k (Fin n), ρ u' (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0)
        = ∑ u : unipB k (Fin n), (fun w : unipB k (Fin n) =>
            ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ •
              ρ w v0) (⟨u', hu'⟩ * u) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      _ = ∑ w : unipB k (Fin n), ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
            GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 := Fintype.sum_equiv (Equiv.mulLeft a) (fun u => F (a * u)) F (fun _ => rfl)
      _ = _ := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hχ, mul_inv, inv_inv, mul_smul]

theorem vanish_of_comm {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v) {Y u₁ u₂ : GL (Fin n) k}
    (h1 : u₁ ∈ unipB k (Fin n)) (h2 : u₂ ∈ unipB k (Fin n)) (hc : u₁ * Y = Y * u₂)
    (hne : ψ (superDiag u₁) ≠ ψ (superDiag u₂)) : l (ρ Y v) = 0 := by
  have e1 : l (ρ (u₁ * Y) v) = ψ (superDiag u₁) * l (ρ Y v) := by rw [map_mul, Module.End.mul_apply, hl u₁ h1]
  have e2 : l (ρ (Y * u₂) v) = ψ (superDiag u₂) * l (ρ Y v) := by
    rw [map_mul, Module.End.mul_apply, hv u₂ h2, map_smul, map_smul, smul_eq_mul]
  rw [hc, e2] at e1
  have hne' : (ψ (superDiag u₁) : ℂ) ≠ ψ (superDiag u₂) := fun h => hne (Circle.ext h)
  have : ((ψ (superDiag u₂) : ℂ) - ψ (superDiag u₁)) * l (ρ Y v) = 0 := by rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne'.symm)

theorem vanish_lower {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) {ρ : Representation ℂ (GL (Fin (m + 1)) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin (m + 1)), ρ u v = (ψ (superDiag u) : ℂ) • v) (Y : GL (Fin (m + 1)) k)
    (hlow : ∀ r c : Fin (m + 1), r < c → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = 0)
    (hlast : ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c) (hY : Y ≠ 1) : l (ρ Y v) = 0 := by
  classical
  set S := Finset.univ.filter fun r : Fin (m + 1) =>
    ∃ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c ≠ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c with hSdef
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hY
    ext r c
    have := h (Finset.mem_univ r)
    push_neg at this
    rw [this c, Units.val_one]
  have hr₀ := Finset.max'_mem S hS
  have hle : ∀ r ∈ S, r ≤ S.max' hS := fun r hr => Finset.le_max' S r hr
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, S.max' hS = r₀ := ⟨_, rfl⟩
  rw [hr₀def] at hr₀ hle
  have hmax : ∀ r, r₀ < r → ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c := fun r hr c => by
    by_contra h
    exact absurd (hle r (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, c, h⟩)) (not_le.2 hr)
  rw [hSdef, Finset.mem_filter] at hr₀
  obtain ⟨j, hj⟩ := hr₀.2
  have hr₀last : r₀ ≠ Fin.last m := fun h => by rw [h] at hj; exact hj (hlast j)
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hr₀last
  have hjle : j ≤ r₀ := by
    by_contra h
    push_neg at h
    exact hj (by rw [hlow _ _ h, Matrix.one_apply_ne (ne_of_lt h)])
  have hcgt : r₀ < i.succ := by rw [← hi]; exact Fin.castSucc_lt_succ
  have hrow := hmax _ hcgt
  have hcol : ∀ r, r₀ < r → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r j = 0 := fun r hr => by
    rw [hmax r hr j, Matrix.one_apply_ne (lt_of_le_of_lt hjle hr).ne']
  have hd : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j ≠ 0 :=
    sub_ne_zero.2 hj
  obtain ⟨s₀, hs₀⟩ := AddChar.ne_one_iff.1 hψ
  have h1' : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j = 0 := by rw [hcol _ hcgt, mul_zero]
  have h2' : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) i.succ = 0 := by
    rw [Pi.single_apply, if_neg (lt_of_le_of_lt hjle hcgt).ne']
  refine vanish_of_comm hl hv
    (colElt_mem _ _ h1' fun r hr => by rw [hcol r (lt_trans hcgt hr), mul_zero])
    (colElt_mem _ _ h2' fun r hr => by rw [Pi.single_apply, if_neg (lt_trans (lt_of_le_of_lt hjle hcgt) hr).ne'])
    (colElt_comm Y i.succ j _ hrow h1' h2') ?_
  rw [superDiag_colElt, superDiag_colElt, hi]
  have hsY : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j + s₀ := by
    field_simp
    ring
  have hsing : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) r₀ =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j := by
    by_cases h : r₀ = j
    · subst h; simp
    · rw [Pi.single_apply, if_neg h, Matrix.one_apply_ne h, mul_zero]
  rw [hsY, hsing, AddChar.map_add_eq_mul]
  intro h
  exact hs₀ (by simpa using h)

end DiscreteGroups.sglob.DzFp
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalUnr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

theorem isTotallyComplex_of_algebra {E L : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field L]
    [NumberField L] [Algebra E L] : IsTotallyComplex L :=
  NumberField.isTotallyComplex_of_algebra E L

set_option linter.deprecated false in

theorem unram_place {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E L]
    [Algebra E Ω] [Algebra L Ω] [IsScalarTower E L Ω] [IsAlgClosure E Ω] [IsAlgClosure L Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (v : HeightOneSpectrum (𝓞 L))
    (hv : IsPlaceOver A v) (hL : IsLocalExt L h)
    (hI : ∀ σ ∈ Ine (F := E) A, ∀ x : L, (σ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x)
    (hgw : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) (hN : normV w = g) :
    ((g : ℕ) : 𝓞 L) ∈ v.asIdeal ∧ ((g : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧ normV v = g ^ Module.finrank E L := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : w.asIdeal.IsMaximal := w.isMaximal

  have hvw : ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ v.asIdeal := fun x => by
    rw [← h x, ← hv (algebraMap (𝓞 E) (𝓞 L) x)]
    have e1 : algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E L Ω (x : E)).symm
    rw [e1]
  have : v.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => (hvw x).trans Iff.rfl⟩
  have hgmem : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 Nat.one_pos (by rw [hN, pow_one])
  have hgv : ((g : ℕ) : 𝓞 L) ∈ v.asIdeal := by
    have := (hvw _).1 hgmem
    rwa [map_natCast] at this

  set f := w.asIdeal.inertiaDeg' v.asIdeal with hf_def
  have hnorm : normV v = normV w ^ f := by
    have hn : ∀ {K : Type} [Field K] [NumberField K] (u : HeightOneSpectrum (𝓞 K)), normV u = Ideal.absNorm u.asIdeal :=
      fun u => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [hn, hn]
    exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal w.asIdeal w.isPrime w.ne_bot
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · have := one_lt_normV v
      rw [hnorm, hf, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact hf

  let S : Subgroup (Weil h) :=
    { carrier := {τ | ∀ x : L, (τ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x}
      mul_mem' := fun {a b} ha hb x => by
        show ((a * b : Weil h) : G E Ω) (algebraMap L Ω x) = _
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb x, ha x]
      one_mem' := fun x => rfl
      inv_mem' := fun {a} ha x => by
        show ((a⁻¹ : Weil h) : G E Ω) (algebraMap L Ω x) = _
        rw [Subgroup.coe_inv]
        conv_lhs => rw [← ha x]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] }
  have hS : ∀ τ : Weil h, τ ∈ S ↔ ∀ x : L, (τ : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun _ => Iff.rfl
  have hIS : ∀ τ : Weil h, deg τ = 0 → τ ∈ S := fun τ hτ x => hI _ (deg_eq_zero_iff.1 hτ) x

  obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hv
  have hφA : ActsAs A (normV w) (AlgEquiv.restrictScalars E φ) f 0 := by
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.restrictScalars E φ • A = A
      have hd : φ • A = A := hφ.1
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      conv_rhs => rw [← hd]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    · have := hφ.2 x hx
      rw [hnorm] at this
      simpa using this
  let φW : Weil h := ⟨_, ⟨f, 0, hφA⟩⟩
  have hφdeg : deg φW = f := by rw [deg_eq hφA]; simp
  have hφS : φW ∈ S := fun x => φ.commutes x

  let Φ : Weil h → (L →ₐ[E] Ω) := fun τ => ((τ : G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E L Ω)
  have hΦS : ∀ τ s : Weil h, s ∈ S → Φ (τ * s) = Φ τ := fun τ s hs => AlgHom.ext fun x => by
    show ((τ * s : Weil h) : G E Ω) (algebraMap L Ω x) = (τ : G E Ω) (algebraMap L Ω x)
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hs x]
  have hΦsurj : ∀ ψ : L →ₐ[E] Ω, ∃ τ : Weil h, Φ τ = ψ := fun ψ => by
    let σ : G E Ω := AlgEquiv.ofBijective (ψ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)
    obtain ⟨τ, hτ⟩ := hL σ
    refine ⟨τ, AlgHom.ext fun x => ?_⟩
    show (τ : G E Ω) (algebraMap L Ω x) = ψ x
    rw [hτ x]
    show ψ.liftNormal Ω (algebraMap L Ω x) = ψ x
    rw [AlgHom.liftNormal_commutes]
    rfl

  let φ₀ := frob h
  have hφ₀f : φ₀ ^ (f : ℤ) ∈ S := by
    have hk : deg (φW⁻¹ * φ₀ ^ (f : ℤ)) = 0 := by
      rw [deg_mul, deg_inv, deg_zpow, hφdeg, deg_frob]; ring
    have := S.mul_mem hφS (hIS _ hk)
    rwa [mul_inv_cancel_left] at this
  have hcover : ∀ ψ : L →ₐ[E] Ω, ∃ j : Fin f, Φ (φ₀ ^ (j : ℕ)) = ψ := fun ψ => by
    obtain ⟨τ, rfl⟩ := hΦsurj ψ
    obtain ⟨ι, hι⟩ := exists_eq_zpow_mul (deg_frob (h := h)) τ
    have hfz : (0 : ℤ) < f := by exact_mod_cast hf0
    set d := deg τ
    have hd : d = d % f + f * (d / f) := by have := Int.emod_def d f; linarith
    have hj0 : 0 ≤ d % f := Int.emod_nonneg d hfz.ne'
    have hjf : d % f < f := Int.emod_lt_of_pos d hfz
    refine ⟨⟨(d % f).toNat, by omega⟩, ?_⟩
    show Φ (φ₀ ^ (d % f).toNat) = Φ τ
    have hs : (φ₀ ^ (f : ℤ)) ^ (d / f) * ineIncl h ι ∈ S :=
      S.mul_mem (S.zpow_mem hφ₀f _) (hIS _ (deg_ineIncl ι))
    have e1 : φ₀ ^ d = φ₀ ^ ((d % f).toNat : ℕ) * (φ₀ ^ (f : ℤ)) ^ (d / f) := by
      conv_lhs => rw [hd]
      rw [zpow_add, zpow_mul, ← zpow_natCast, Int.toNat_of_nonneg hj0]
    have e : τ = φ₀ ^ ((d % f).toNat : ℕ) * ((φ₀ ^ (f : ℤ)) ^ (d / f) * ineIncl h ι) := by
      rw [← mul_assoc, ← e1]
      exact hι
    have key : Φ τ = Φ (φ₀ ^ ((d % f).toNat : ℕ)) := by
      rw [e]
      exact hΦS _ _ hs
    exact key.symm
  have hcard : Module.finrank E L ≤ f := by
    have h1 := Fintype.card_le_of_surjective (fun j : Fin f => Φ (φ₀ ^ (j : ℕ))) hcover
    rw [AlgHom.card] at h1
    simpa using h1

  have hw0 : w.asIdeal ≠ ⊥ := w.ne_bot
  have hmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset w.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hw0 _).2 ⟨v.isPrime, inferInstance⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) E L hw0
  have hle : Ideal.ramificationIdx' w.asIdeal v.asIdeal * f ≤ Module.finrank E L := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun P => Ideal.ramificationIdx' w.asIdeal P * Ideal.inertiaDeg' w.asIdeal P)
      (fun _ _ => Nat.zero_le _) hmem
  have he0 : Ideal.ramificationIdx' w.asIdeal v.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hw0
  have hfn : f = Module.finrank E L := by
    have : f ≤ Ideal.ramificationIdx' w.asIdeal v.asIdeal * f := Nat.le_mul_of_pos_left f (Nat.pos_of_ne_zero he0)
    omega
  have he1 : Ideal.ramificationIdx' w.asIdeal v.asIdeal = 1 := by
    rw [hfn] at hle
    have hn0 : 0 < Module.finrank E L := Module.finrank_pos
    have : Ideal.ramificationIdx' w.asIdeal v.asIdeal ≤ 1 := by
      by_contra hc
      rw [not_le] at hc
      have := Nat.mul_le_mul_right (Module.finrank E L) hc
      omega
    omega
  refine ⟨hgv, fun hg2 => ?_, by rw [hnorm, hN, hfn]⟩

  obtain ⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgmem)
  have hJw : ¬ J ≤ w.asIdeal := fun hJle => hgw (by
    have : Ideal.span {((g : ℕ) : 𝓞 E)} ≤ w.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hJle
    exact this (Ideal.mem_span_singleton_self _))
  have hmapJ : ¬ v.asIdeal ∣ Ideal.map (algebraMap (𝓞 E) (𝓞 L)) J := fun hd => hJw (by
    intro y hy
    have := Ideal.dvd_iff_le.1 hd (Ideal.mem_map_of_mem _ hy)
    exact (hvw y).2 this)
  have hdiv : v.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal *
      Ideal.map (algebraMap (𝓞 E) (𝓞 L)) J := by
    rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hg2)
  have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hw2 := Ideal.dvd_iff_le.1 (hprime.pow_dvd_of_dvd_mul_right 2 hmapJ hdiv)

  by_cases hb : ∀ k : ℕ, Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal ≤ v.asIdeal ^ k
  · have := Ideal.ramificationIdx'_eq_zero (p := w.asIdeal) (P := v.asIdeal) fun k => ⟨k + 1, hb (k + 1), by omega⟩
    omega
  · obtain ⟨k0, hk0⟩ := not_forall.1 hb
    have hbdd : BddAbove {k | Ideal.map (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal ≤ v.asIdeal ^ k} := by
      refine ⟨k0, fun k hk => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hk0 (hk.trans (Ideal.pow_le_pow_right hlt.le))
    have h2 : 2 ≤ Ideal.ramificationIdx' w.asIdeal v.asIdeal := le_csSup hbdd hw2
    omega

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKM
section
namespace DiscreteGroups.sglob.LConv

theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvUnitOf
section
noncomputable section

open ValuativeRel

namespace DiscreteGroups.sglob.LConv

theorem countable_quotient_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : Countable (G ⧸ K) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ K)) fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have ho : IsOpen ((fun x => x⁻¹ * g) ⁻¹' (K : Set G)) := hK.preimage (continuous_inv.mul continuous_const)
  obtain ⟨d, hd, hdD⟩ := hDd.inter_open_nonempty _ ho ⟨g, by simp⟩
  exact ⟨⟨d, hdD⟩, QuotientGroup.eq.2 hd⟩

theorem separableSpace_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) : TopologicalSpace.SeparableSpace (GL (Fin m) k) := by
  have : SecondCountableTopology (GL (Fin m) k) := inferInstance
  infer_instance

theorem unitOfUnif : UnitOfUnif := by
  intro hAlt hFin hUnif k _ _ _ _ m K hKo hKc H _ _ _ π hπ hcomm
  have := separableSpace_GL k m
  obtain ⟨N, hN⟩ := hUnif k m K hKo
  let F : Submodule ℂ H :=
    { carrier := {x | ∀ κ ∈ K, π κ x = x}
      add_mem' := fun {a b} ha hb κ hκ => by rw [map_add, ha κ hκ, hb κ hκ]
      zero_mem' := fun κ _ => map_zero _
      smul_mem' := fun c x hx κ hκ => by rw [map_smul, hx κ hκ] }
  have hF : IsClosed (F : Set H) := by
    have : (F : Set H) = ⋂ κ ∈ K, {x | π κ x = x} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun κ _ => isClosed_eq (π κ).continuous continuous_id
  have : CompleteSpace F := hF.completeSpace_coe
  have h1 : ∀ x, F.starProjection x ∈ F := fun x => F.starProjection_apply_mem x
  have h2 : ∀ x ∈ F, F.starProjection x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  obtain ⟨s, hs⟩ := hFin _ H π hπ hcomm F.starProjection (by ext x; exact h2 _ (h1 x)) (N ^ 2 + 1)
    (hAlt _ K hKo hKc (countable_quotient_of_isOpen K hKo) N hN H π hπ F.starProjection
      (isSelfAdjoint_starProjection F) h1 h2 _ (Nat.lt_succ_self _))
  exact ⟨s, fun x hx => h2 x hx ▸ hs x⟩

end DiscreteGroups.sglob.LConv

end
end

