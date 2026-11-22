import Mathlib

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.InvSubOneBd
section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {n : ℕ} {K : Type*} [Field K]

def Bd (m : ℕ) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < j + m → A i j = 0

theorem Bd.mono {m m' : ℕ} {A : Matrix (Fin n) (Fin n) K} (h : m' ≤ m) (hA : Bd m A) : Bd m' A :=
  fun i j hij => hA i j (by omega)

theorem Bd.mul {m m' m'' : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m' B)
    (h : m'' ≤ m + m') : Bd m'' (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (i : ℕ) < l + m
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem Bd.add {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A + B) :=
  fun i j h => by rw [Matrix.add_apply, hA i j h, hB i j h, add_zero]

theorem Bd.sub {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A - B) :=
  fun i j h => by rw [Matrix.sub_apply, hA i j h, hB i j h, sub_zero]

theorem Bd.neg {m : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Bd m A) : Bd m (-A) :=
  fun i j h => by rw [Matrix.neg_apply, hA i j h, neg_zero]

theorem Bd_zero (m : ℕ) : Bd m (0 : Matrix (Fin n) (Fin n) K) :=
  fun i j _ => by rw [Matrix.zero_apply]

theorem Bd_one : Bd 0 (1 : Matrix (Fin n) (Fin n) K) := by
  intro i j h
  rw [Matrix.one_apply_ne]
  intro e
  rw [e] at h
  omega

theorem Bd.pow {A : Matrix (Fin n) (Fin n) K} (hA : Bd 1 A) (k : ℕ) : Bd k (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact Bd_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA le_rfl

theorem Bd.sum {ι : Type*} {m : ℕ} {s : Finset ι} {f : ι → Matrix (Fin n) (Fin n) K}
    (h : ∀ i ∈ s, Bd m (f i)) : Bd m (∑ i ∈ s, f i) :=
  fun i j hij => by
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun l hl => h l hl i j hij

theorem Bd.eq_zero {A : Matrix (Fin n) (Fin n) K} (h : Bd n A) : A = 0 := by
  ext i j
  have := i.2
  exact h i j (by omega)

theorem inv_sub_one_bd (a : Matrix.GeneralLinearGroup (Fin n) K) (k : ℕ)
    (h : Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)) :
    Bd (k + 1) (((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := by
  have hN1 : Bd 1 (-((a : Matrix (Fin n) (Fin n) K) - 1)) := (h.mono (by omega)).neg
  have hpow : (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ n = 0 := (hN1.pow n).eq_zero
  have hba : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
      (a : Matrix (Fin n) (Fin n) K) = 1 := by
    have e := geom_sum_mul_neg (-((a : Matrix (Fin n) (Fin n) K) - 1)) n
    rw [hpow, sub_zero, sub_neg_eq_add, add_sub_cancel] at e
    exact e
  have hinv : ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i := by
    calc ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
            (a : Matrix (Fin n) (Fin n) K) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hba, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hb0 : Bd 0 (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) :=
    Bd.sum fun i _ => (hN1.pow i).mono (Nat.zero_le _)
  have e2 : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) - 1 =
      -((∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
        ((a : Matrix (Fin n) (Fin n) K) - 1)) := by
    rw [mul_sub, hba, mul_one]; abel
  rw [hinv, e2]
  exact (hb0.mul h (by omega)).neg

def FG (n : ℕ) (K : Type*) [Field K] (k : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {a | Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)}
  one_mem' := by
    show Bd _ (((1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    rw [Units.val_one, sub_self]; exact Bd_zero _
  mul_mem' := by
    intro a b ha hb
    show Bd _ (((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    have e : ((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        ((a : Matrix (Fin n) (Fin n) K) - 1) * ((b : Matrix (Fin n) (Fin n) K) - 1) +
          ((a : Matrix (Fin n) (Fin n) K) - 1) + ((b : Matrix (Fin n) (Fin n) K) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]; exact ((Bd.mul ha hb (by omega)).add ha).add hb
  inv_mem' := fun {a} ha => inv_sub_one_bd a k ha

theorem mem_FG {k : ℕ} {a : Matrix.GeneralLinearGroup (Fin n) K} :
    a ∈ FG n K k ↔ Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1) := Iff.rfl

theorem FG_mono (k : ℕ) : FG n K (k + 1) ≤ FG n K k := fun _ ha => Bd.mono (by omega) ha

theorem FG_eq_one {a : Matrix.GeneralLinearGroup (Fin n) K} (ha : a ∈ FG n K n) : a = 1 := by
  have h0 := (Bd.mono (by omega) ha : Bd n _).eq_zero
  apply Units.ext
  rw [Units.val_one]
  exact sub_eq_zero.mp h0

theorem FG_comm (k : ℕ) (g a : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ FG n K 0)
    (ha : a ∈ FG n K k) : g * a * g⁻¹ * a⁻¹ ∈ FG n K (k + 1) := by
  rw [mem_FG] at hg ha ⊢
  have hgi := inv_sub_one_bd g 0 hg
  have hai := inv_sub_one_bd a k ha
  have h1 : Bd 0 ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := (hgi.mono (Nat.zero_le _)).add Bd_one
    rwa [sub_add_cancel] at this
  have h2 : Bd 0 ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := (hai.mono (Nat.zero_le _)).add Bd_one
    rwa [sub_add_cancel] at this
  have hC : Bd (k + 1 + 1) (((g : Matrix (Fin n) (Fin n) K) - 1) * ((a : Matrix (Fin n) (Fin n) K) - 1) -
      ((a : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)) :=
    (Bd.mul hg ha (by omega)).sub (Bd.mul ha hg (by omega))
  have hg1 : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1 : (a : Matrix (Fin n) (Fin n) K) *
      ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ((g * a * g⁻¹ * a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (((g : Matrix (Fin n) (Fin n) K) - 1) * ((a : Matrix (Fin n) (Fin n) K) - 1) -
        ((a : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)) *
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    calc _ = (g : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) -
          (a : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hg1, mul_one, ha1]
      _ = _ := by noncomm_ring
  rw [e]
  exact hC.mul (h1.mul h2 le_rfl) (by omega)

theorem closure_le_FG :
    Subgroup.closure {a : Matrix.GeneralLinearGroup (Fin n) K |
      ∀ i j, (i < j → (a : Matrix (Fin n) (Fin n) K) i j = 0) ∧
        (i = j → (a : Matrix (Fin n) (Fin n) K) i j = 1)} ≤ FG n K 0 := by
  rw [Subgroup.closure_le]
  intro a ha i j hij
  rw [Matrix.sub_apply]
  have hle : (i : ℕ) ≤ j := by omega
  rcases Nat.lt_or_eq_of_le hle with h | h
  · have hij' : i < j := Fin.lt_def.mpr h
    rw [(ha i j).1 hij', Matrix.one_apply_ne (ne_of_lt hij'), sub_zero]
  · have e : i = j := Fin.ext h
    subst e
    rw [(ha i i).2 rfl, Matrix.one_apply_eq, sub_self]

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.RelIndexEqIndexOfMul
section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]

theorem relIndex_eq_index_of_mul (A R : Subgroup G)
    (h : ∀ y : G, ∃ r ∈ R, ∃ a ∈ A, y = r * a) : A.relIndex R = A.index := by
  have hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
  have ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, rfl⟩ := h y
      refine ⟨⟨r, hr⟩, ?_⟩
      change ((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)
      rw [mul_one, QuotientGroup.eq]
      simpa using ha
  rw [Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ,
    Subgroup.index_eq_card]

theorem relIndex_eq_of_mul (A B B' : Subgroup G) (hBB : B ≤ B')
    (h : ∀ y ∈ B', ∃ b ∈ B, ∃ a ∈ A, y = b * a) : A.relIndex B = A.relIndex B' := by
  rw [← Subgroup.relIndex_subgroupOf hBB]
  refine relIndex_eq_index_of_mul (A.subgroupOf B') (B.subgroupOf B') ?_
  intro y
  obtain ⟨b, hb, a, ha, hy⟩ := h y.1 y.2
  have haB : a ∈ B' := by
    have : a = b⁻¹ * y.1 := by rw [hy]; group
    rw [this]; exact B'.mul_mem (B'.inv_mem (hBB hb)) y.2
  refine ⟨⟨b, hBB hb⟩, ?_, ⟨a, haB⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact hb
  · rw [Subgroup.mem_subgroupOf]; exact ha
  · apply Subtype.ext; simp [hy]

theorem inf_relIndex_of_le (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩

theorem relIndex_split (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X
  rw [show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left] at e1
  have e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N) := by
    refine relIndex_eq_of_mul _ _ _ le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_right).1 hy
    exact ⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩
  have e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X) := by
    refine relIndex_eq_of_mul _ _ _ ?_ ?_
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy.2, hy.1⟩
    · intro y hy
      obtain ⟨h, hh, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hy.1
      refine ⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩
      rw [← hyz]
      have : h * z * h⁻¹ ∈ N := hN.conj_mem z hz h
      simpa [mul_assoc] using this
  rw [← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem mem_cj (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by
  simp [cj, Subgroup.mem_map, MulAut.conj_apply]

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.RelIndexInfRightNeZero
section
noncomputable section

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

variable {G : Type*} [Group G]

def ratio (A S : Subgroup G) : ℝ := (A.relIndex S : ℝ) / (S.relIndex A : ℝ)

theorem real_ratio_eq (a e c f β δ : ℕ) (hβ : β ≠ 0) (hδ : δ ≠ 0) (h1 : β * a = δ * c)
    (h2 : β * e = δ * f) : (a : ℝ) / e = c / f := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  have hδ' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have h1' : (β : ℝ) * a = δ * c := by exact_mod_cast h1
  have h2' : (β : ℝ) * e = δ * f := by exact_mod_cast h2
  rw [← mul_div_mul_left (a : ℝ) (e : ℝ) hβ', h1', h2', mul_div_mul_left _ _ hδ']

theorem relIndex_inf_right_ne_zero {T S : Subgroup G} (h : T.relIndex S ≠ 0) (B : Subgroup G) :
    T.relIndex (S ⊓ B) ≠ 0 := by
  have h1 := Subgroup.relIndex_inter_ne_zero h B
  rw [← Subgroup.inf_relIndex_right] at h1 ⊢
  have e : T ⊓ B ⊓ (S ⊓ B) = T ⊓ (S ⊓ B) := by
    ext x; simp only [Subgroup.mem_inf]; tauto
  rwa [e] at h1

theorem ratio_eq_of_comm (S T B : Subgroup G) (hk : T.relIndex S = S.relIndex T)
    (hk0 : T.relIndex S ≠ 0) : ratio B S = ratio B T := by
  have hk0' : S.relIndex T ≠ 0 := hk ▸ hk0
  have hβ : T.relIndex (S ⊓ B) ≠ 0 := relIndex_inf_right_ne_zero hk0 B
  have hδ : S.relIndex (T ⊓ B) ≠ 0 := relIndex_inf_right_ne_zero hk0' B

  have e1 := Subgroup.relIndex_inf_mul_relIndex B T S
  have e2 := Subgroup.relIndex_inf_mul_relIndex B S T
  have eP : (B ⊓ T).relIndex S = (B ⊓ S).relIndex T := by
    rw [← e1, ← e2, inf_comm T S, hk]
  have e3 := Subgroup.relIndex_inf_mul_relIndex T B S
  have e4 := Subgroup.relIndex_inf_mul_relIndex S B T
  have e5 := Subgroup.relIndex_inf_mul_relIndex T S B
  have e6 := Subgroup.relIndex_inf_mul_relIndex S T B
  unfold ratio
  refine real_ratio_eq _ _ _ _ (T.relIndex (S ⊓ B)) (S.relIndex (T ⊓ B)) hβ hδ ?_ ?_
  · rw [inf_comm S B, inf_comm T B, e3, e4, inf_comm T B, inf_comm S B, eP]
  · rw [e5, e6, inf_comm]

theorem ratio_map_equiv (φ : G ≃* G) (A S : Subgroup G) :
    ratio (A.map φ.toMonoidHom) (S.map φ.toMonoidHom) = ratio A S := by
  unfold ratio
  rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective,
    Subgroup.relIndex_map_map_of_injective _ _ φ.injective]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem ratio_cj_of (A S : Subgroup G) (g : G)
    (hA1 : A.relIndex S ≠ 0) (hA2 : S.relIndex A ≠ 0)
    (hB1 : (cj g A).relIndex S ≠ 0) (hB2 : S.relIndex (cj g A) ≠ 0)
    (hU : S.relIndex (cj g S) ≠ 0 → (cj g S).relIndex S ≠ 0 →
      S.relIndex (cj g S) = (cj g S).relIndex S) :
    ratio (cj g A) S = ratio A S := by
  have m1 : (cj g S).relIndex (cj g A) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA2
  have m2 : (cj g A).relIndex (cj g S) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA1
  have hTS : (cj g S).relIndex S ≠ 0 := Subgroup.relIndex_ne_zero_trans m1 hB1
  have hST : S.relIndex (cj g S) ≠ 0 := Subgroup.relIndex_ne_zero_trans hB2 m2
  have hk := (hU hST hTS).symm
  rw [ratio_eq_of_comm S (cj g S) (cj g A) hk hTS]
  exact ratio_map_equiv (MulAut.conj g) A S

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

