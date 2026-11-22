import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.CNeZeroOfSame
section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

section Basics

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem fvec_castSucc (F : FlagG S r T) (k : Fin r) : F.fvec k.castSucc = F.e k := by
  simp [FlagG.fvec]

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi h : i.1 < b))

theorem e_mem_Xa (F : FlagG S r T) {k : Fin r} {a : ℕ} (hk : k.val < a) : F.e k ∈ F.Xa a := Submodule.subset_span ⟨k, hk, rfl⟩

theorem Xa_r (F : FlagG S r T) : F.Xa r = F.X := by
  simp [FlagG.Xa, FlagG.X]

theorem fXa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := Submodule.span_mono (Set.image_subset_range _ _)

theorem fe_mem_X (F : FlagG S r T) (k : Fin r) : F.e k ∈ F.X := Submodule.subset_span (Set.mem_range_self k)

theorem hT_Xa_of (F : FlagG S r T) (v : S.V) (a : ℕ)
    (hv : ∀ j : Fin r, j.val < a → S.hT v (F.e j) = 0) : ∀ y ∈ F.Xa a, S.hT v y = 0 := by
  have h1 : F.Xa a ≤ LinearMap.ker (S.hT v) :=
    Submodule.span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact hv j hj)
  intro y hy
  exact LinearMap.mem_ker.1 (h1 hy)

theorem hT_e_X (F : FlagG S r T) (j : Fin r) : ∀ y ∈ F.X, S.hT (F.e j) y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT (F.e j)) :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact F.e_iso j k)
  intro y hy
  exact LinearMap.mem_ker.1 (h1 hy)

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip y) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hT_e_X F j y hy)
  simpa using h1 hx

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have h1 : F.X ≤ LinearMap.ker (S.hT.flip F.z) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact F.z_orth j)
  simpa using h1 hx

theorem hT_X_fvec (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) (m : Fin (r + 1)) :
    S.hT x (F.fvec m) = 0 := by
  induction m using Fin.lastCases with
  | last => rw [fvec_last]; exact hT_X_alt F hx
  | cast k => rw [fvec_castSucc]; exact hT_X_X F hx (fe_mem_X F k)

theorem fvec_indep (F : FlagG S r T) (hT0 : T ≠ 0) : LinearIndependent E F.fvec := by
  rw [FlagG.fvec, linearIndependent_fin_snoc]
  refine ⟨F.e_indep, fun hz => hT0 ?_⟩
  have h1 := hT_X_alt F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1

theorem fvec_mem_Xa (F : FlagG S r T) (m : Fin (r + 1)) (hm : m.val < r) :
    F.fvec m ∈ F.Xa (m.val + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin r, k.castSucc = m := ⟨⟨m.val, hm⟩, rfl⟩
  rw [fvec_castSucc]
  exact e_mem_Xa F (Nat.lt_succ_self _)

end Basics

section TwoFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem Xa_le_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (a : ℕ) : F'.Xa a ≤ F.Xa a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k.1 < a := hk
  have h := hs k.castSucc
  rw [fvec_castSucc, fvec_castSucc] at h
  have h2 := Submodule.add_mem _ (Xa_mono F (le_of_lt hk') h)
    (Submodule.smul_mem _ (c k.castSucc) (e_mem_Xa F hk'))
  simpa using h2

theorem le_Xa_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) :
    ∀ a : ℕ, a ≤ r → F.Xa a ≤ F'.Xa a ∧ ∀ k : Fin r, k.val < a → c k.castSucc ≠ 0
  | 0, _ => by
    refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    have h0 : F.Xa 0 = ⊥ := by simp [FlagG.Xa]
    rw [h0]
    exact bot_le
  | a + 1, ha => by
    obtain ⟨ih1, ih2⟩ := le_Xa_of_same F F' c hs a (by omega)
    obtain ⟨ka, hka⟩ : ∃ ka : Fin r, ka.val = a := ⟨⟨a, by omega⟩, rfl⟩
    have hsa := hs ka.castSucc
    rw [fvec_castSucc, fvec_castSucc, Fin.val_castSucc, hka] at hsa
    have hmem : F'.e ka - c ka.castSucc • F.e ka ∈ F'.Xa a := ih1 hsa
    have hc : c ka.castSucc ≠ 0 := by
      intro h0
      rw [h0, zero_smul, sub_zero] at hmem
      exact F'.e_indep.notMem_span_image (s := {i : Fin r | i.val < a}) (x := ka)
        (by simp [hka]) hmem
    refine ⟨?_, ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, hk, rfl⟩
      have hk' : k.val < a + 1 := hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
      · exact Xa_mono F' (Nat.le_succ a) (ih1 (e_mem_Xa F h))
      · have hkk : k = ka := Fin.ext (h.trans hka.symm)
        subst hkk
        have h1 : F'.e k ∈ F'.Xa (a + 1) := e_mem_Xa F' (by omega)
        have h2 := Xa_mono F' (Nat.le_succ a) hmem
        have h3 := Submodule.smul_mem _ (c k.castSucc)⁻¹ (sub_mem h1 h2)
        rwa [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact ih2 k h
      · have hkk : k = ka := Fin.ext (h.trans hka.symm)
        rw [hkk]
        exact hc

theorem Xa_eq_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (a : ℕ) (ha : a ≤ r) : F'.Xa a = F.Xa a := le_antisymm (Xa_le_of_same F F' c hs a) ((le_Xa_of_same F F' c hs a ha).1)

theorem X_eq_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) : F'.X = F.X := by
  rw [← Xa_r, ← Xa_r]
  exact Xa_eq_of_same F F' c hs r le_rfl

theorem c_ne_zero_of_same (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E)
    (hs : SameFlag F F' c) (k : Fin r) : c k.castSucc ≠ 0 := (le_Xa_of_same F F' c hs r le_rfl).2 k k.2

end TwoFlags

end PI.FRS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.CoefXOfMem
section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_of_mem (F : FlagG S r T) (x : S.V) (hx : x ∈ Submodule.span E (Set.range F.e))
    (k : Fin r) : F.coefX x k = F.e_indep.repr ⟨x, hx⟩ k := by
  unfold FlagG.coefX
  exact dif_pos hx

theorem coefX_add' (F : FlagG S r T) (x y : S.V) (k : Fin r) (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) k = F.coefX x k + F.coefX y k := by
  rw [coefX_of_mem F _ (F.X.add_mem hx hy), coefX_of_mem F _ hx, coefX_of_mem F _ hy]
  have : (⟨x + y, F.X.add_mem hx hy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add, Finsupp.add_apply]

theorem coefX_smul' (F : FlagG S r T) (a : E) (x : S.V) (k : Fin r) (hx : x ∈ F.X) :
    F.coefX (a • x) k = a * F.coefX x k := by
  rw [coefX_of_mem F _ (F.X.smul_mem a hx), coefX_of_mem F _ hx]
  have : (⟨a • x, F.X.smul_mem a hx⟩ : Submodule.span E (Set.range F.e)) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem e_mem_X (F : FlagG S r T) (j : Fin r) : F.e j ∈ F.X :=
  Submodule.subset_span ⟨j, rfl⟩

theorem coefX_e' (F : FlagG S r T) (j k : Fin r) :
    F.coefX (F.e j) k = if j = k then 1 else 0 := by
  rw [coefX_of_mem F _ (e_mem_X F j), F.e_indep.repr_eq_single j _ rfl, Finsupp.single_apply]

theorem coefX_zero' (F : FlagG S r T) (k : Fin r) : F.coefX 0 k = 0 := by
  rw [coefX_of_mem F _ F.X.zero_mem]
  have : (⟨0, F.X.zero_mem⟩ : Submodule.span E (Set.range F.e)) = 0 := rfl
  rw [this, map_zero, Finsupp.zero_apply]

theorem Xa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

theorem coefX_low' (F : FlagG S r T) (a : ℕ) (x : S.V) (k : Fin r) (hx : x ∈ F.Xa a)
    (hk : a ≤ k.val) : F.coefX x k = 0 := by
  have key : x ∈ F.X ∧ F.coefX x k = 0 := by
    unfold FlagG.Xa at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      refine ⟨e_mem_X F i, ?_⟩
      rw [coefX_e']
      have hne : i ≠ k := by
        intro h
        have : i.val < a := hi
        rw [h] at this
        omega
      simp [hne]
    | zero => exact ⟨F.X.zero_mem, coefX_zero' F k⟩
    | add y z _ _ hy hz =>
      exact ⟨F.X.add_mem hy.1 hz.1, by rw [coefX_add' F y z k hy.1 hz.1, hy.2, hz.2, add_zero]⟩
    | smul b y _ hy =>
      exact ⟨F.X.smul_mem b hy.1, by rw [coefX_smul' F b y k hy.1, hy.2, mul_zero]⟩
  exact key.2

end Local

theorem coefAdd : CoefAdd := by
  intro E _ _ _ S r T F x y k hx hy
  exact coefX_add' F x y k hx hy

theorem coefSmul : CoefSmul := by
  intro E _ _ _ S r T F a x k hx
  exact coefX_smul' F a x k hx

theorem coefE : CoefE := by
  intro E _ _ _ S r T F j k
  exact coefX_e' F j k

theorem coefLow : CoefLow := by
  intro E _ _ _ S r T F a x k hx hk
  exact coefX_low' F a x k hx hk

end PI.FRS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExistsAlt
section
noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

theorem dualExists : DualExists := by
  intro E _ _ _ S m u hu t
  classical
  let L : S.V →ₗ[E] (Fin m → E) := LinearMap.pi (fun k => S.hT (u k))
  have hL : ∀ v k, L v k = S.hT (u k) v := fun v k => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set lam : Fin m → E := fun k => f (fun j => if k = j then 1 else 0) with hlam
    have hfv : ∀ v : S.V, ∑ k, S.hT (u k) v * lam k = 0 := by
      intro v
      have h1 : f (L v) = 0 := hf (LinearMap.mem_range_self L v)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [hL, smul_eq_mul, hlam] using h1
    set w : S.V := ∑ k, star (lam k) • u k with hw
    have hw0 : w = 0 := by
      refine S.nondeg.1 w (fun v => ?_)
      rw [hw, map_sum, LinearMap.sum_apply]
      rw [← hfv v]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star,
        mul_comm]
    have hlam0 : ∀ k, lam k = 0 := by
      intro k
      have := (Fintype.linearIndependent_iff.1 hu) (fun k => star (lam k)) hw0 k
      simpa using this
    apply hf0
    refine LinearMap.pi_ext (fun i x => ?_)
    have hs : (Pi.single i x : Fin m → E) = x • (fun j => if i = j then 1 else 0) := by
      ext j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hs, map_smul]
    have := hlam0 i
    simp only [hlam] at this
    simp [this]
  obtain ⟨v, hv⟩ := hsurj t
  exact ⟨v, fun k => by rw [← hL, hv]⟩

end PI.FRS
end
end

