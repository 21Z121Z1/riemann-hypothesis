import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0011
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0012

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem ioBlock_wh' (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : ∀ (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' s
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL)) :
    IsWeightedHomogeneous ω (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (TD C0 CE1 CE2 X j b ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ := fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) + ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU l
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hS := hs ω' ωL ⟨h1, h2, h3⟩
  have hA := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) s _ hS
  have hDg : IsWeightedHomogeneous ω (digitMon (KK O) C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (b.rz i c • ω ((topOdd X j i, true), c) + b.ry i c • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have hSt : IsWeightedHomogeneous ω (sTopMon (KK O) X.p C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) • ω ((topOdd X j i, true), 0) +
          ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i) • ω ((topOdd X j i, false), 0) else 0) := by
    refine IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?_)
    split_ifs
    · exact ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)
    · exact isWeightedHomogeneous_one _ _
  have hall := (hDg.mul hSt).mul hA
  refine wh_congr hall ?_
  have E1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ω' (Sum.inr (Fin.castSucc l, false)) =
      ∑ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0 := by
    rw [← sum_uTop (X.seg C0 CE1 CE2 j) (fun i => (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ]
    rfl
  have E3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      b.oPlus * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU, chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl, chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl]
  unfold OmB TD
  rw [E1, E3, hx, hXi]
  simp only [smul_eq_mul, Bool.not_false]
  have key : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0))) =
      (∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          (X.seg C0 CE1 CE2 j).P X.p i * b.sg i * ω ((topOdd X j i, false), 0) else 0) +
      (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0) +
      ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    intro i
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, if_neg (not_le.2 h), if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_pos (not_lt.1 h), if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  ring

theorem leading_exponent_weighted_homog (b : SegBlock (segS X.TT j) X.m) (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ)
    (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ) (hB : Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL) :
    IsWeightedHomogeneous ω' (monomial (mu0 C0 CE1 CE2 X j b) (1 : KK ℤ))
      (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL) := by
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω' i) (fun _ => zero_smul _ _)]
  simpa [smul_eq_mul] using leading_exponent_homogeneous C0 CE1 CE2 X j b ω' ωL hB

theorem tdeg_eq (b : SegBlock (segS X.TT j) X.m) (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (ho : b.oPlus ≤ segAPlus X.TT X.aT j) (x : X.TT × Bool) :
    tdeg C0 CE1 CE2 X j b x = (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have hwh := ioBlock_wh' C0 CE1 CE2 X j ℤ 0 b (wLet X x) (fun _ _ _ => rfl) (fun _ => rfl) rfl
    (monomial (mu0 C0 CE1 CE2 X j b) 1) (fun ω' ωL hB => leading_exponent_weighted_homog C0 CE1 CE2 X j b ω' ωL hB)
  rw [ioBlock_monomial] at hwh
  have h1 := hwh (by rw [coeff_monomial, if_pos rfl]; exact one_ne_zero)
  rw [weight_wLet] at h1
  unfold tdeg
  rw [h1, TD_wLet C0 CE1 CE2 X j x b hk ho]

theorem segPos_inj : Function.Injective (segPos X.TT j) := by
  intro i i' h
  exact topOdd_inj X j (Subtype.ext h)

@[to_additive]
theorem prod_tdeg {M : Type} [CommMonoid M] (g : ℕ → M) (hg : g 0 = 1) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    ∏ x : X.TT × Bool, g (tdeg C0 CE1 CE2 X j b x) =
      (∏ i : Fin (segS X.TT j), g (X.bT (segPos X.TT j i)) * g (X.aT (segPos X.TT j i))) *
        g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j)) := by
  classical
  set T : Fin X.n' → Bool → ℕ := fun t β => (if segNext X.TT j = t then hhDeg X.aT X.bT t β else 0) +
    ∑ i, (if segPos X.TT j i = t then hhDeg X.aT X.bT t β else 0) with hT
  have e : ∀ x : X.TT × Bool, tdeg C0 CE1 CE2 X j b x = T x.1.val x.2 := fun x => tdeg_eq C0 CE1 CE2 X j b hk ho x
  simp only [e]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [Finset.prod_coe_sort X.TT (fun t => g (T t true) * g (T t false))]
  have hnp : ∀ i, segPos X.TT j i ≠ segNext X.TT j := fun i h => (pos_mem X.TT j i).2 (h ▸ (next_mem X.TT j).2)
  have hS : insert (segNext X.TT j) (Finset.univ.image (segPos X.TT j)) ⊆ X.TT := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact (next_mem X.TT j).1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
      exact (pos_mem X.TT j i).1
  rw [← Finset.prod_subset hS (fun t _ ht => by
    have h1 : segNext X.TT j ≠ t := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have h2 : ∀ i, segPos X.TT j i ≠ t := fun i h => ht (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
    simp only [hT, if_neg h1, if_neg (h2 _), Finset.sum_const_zero, add_zero, hg, mul_one])]
  rw [Finset.prod_insert (fun h => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
    exact hnp i hi), Finset.prod_image (fun i _ i' _ h => segPos_inj X j h)]
  have hnext : ∀ β, T (segNext X.TT j) β = hhDeg X.aT X.bT (segNext X.TT j) β := by
    intro β
    show (if segNext X.TT j = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) +
      ∑ i, (if segPos X.TT j i = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) = _
    rw [if_pos rfl, Finset.sum_eq_zero (fun i _ => if_neg (hnp i)), add_zero]
  have hpos : ∀ i β, T (segPos X.TT j i) β = hhDeg X.aT X.bT (segPos X.TT j i) β := by
    intro i β
    show (if segNext X.TT j = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) +
      ∑ i', (if segPos X.TT j i' = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) = _
    rw [if_neg (fun h : segNext X.TT j = segPos X.TT j i => hnp i h.symm), zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (fun h => hi' (segPos_inj X j h))) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
  have hev := (next_mem X.TT j).2
  simp only [hnext, hpos, hhDeg, if_true, Bool.false_eq_true, if_false, if_pos hev]
  have hodd : ∀ i, ¬ Even (segPos X.TT j i).val := fun i => (pos_mem X.TT j i).2
  simp only [hodd, if_false]
  rw [mul_comm (g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j))), mul_assoc]

end

theorem trueDegAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD1 hH hc j b hb
  have ho := hO X hD1 hH hc j b hb
  constructor
  · rw [prod_tdeg C0 CE1 CE2 X j Nat.factorial rfl b hb ho]
    rfl
  · rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
    unfold lgSeg
    rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ChainEmbInj
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section NV

variable {K σ : Type} [Field K]

theorem nv_mul {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F * G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_add {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F + G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_pow {v : σ} {F : MvPolynomial σ K} (h1 : v ∉ F.vars) (n : ℕ) : v ∉ (F ^ n).vars := by
  intro h
  exact h1 (MvPolynomial.vars_pow F n h)

theorem nv_prod {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∏ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.vars_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact nv_mul (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_sum {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∑ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact nv_add (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_X {v u : σ} (h : v ≠ u) : v ∉ (X u : MvPolynomial σ K).vars := by
  classical
  rw [MvPolynomial.vars_X, Finset.mem_singleton]
  exact h

theorem nv_rename {τ : Type} {v : σ} (f : τ → σ) (h : ∀ x, f x ≠ v) (y : MvPolynomial τ K) : v ∉ (rename f y).vars := by
  classical
  intro hv
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename f y hv)
  exact h x hx

theorem cth_rename {τ : Type} (f : τ → σ) (hf : Function.Injective f) (x : τ) (n : ℕ) (y : MvPolynomial τ K) :
    cth (f x) n (rename f y) = rename f (cth x n y) := by
  induction y using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [rename_monomial, cth_monomial, cth_monomial, rename_monomial, Finsupp.mapDomain_apply hf]
  | add p q hp hq => rw [map_add, cth_add, cth_add, map_add, hp, hq]

theorem cth_X_pow (v : σ) (b z : ℕ) : cth v b ((X v : MvPolynomial σ K) ^ z) = (z.choose b) • (X v : MvPolynomial σ K) ^ z := by
  rw [X_pow_eq_monomial, cth_monomial, Finsupp.single_eq_same, one_mul, ← Nat.cast_smul_eq_nsmul K,
    smul_monomial, smul_eq_mul, mul_one]

end NV

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem chainEmb_inj (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  intro a b h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem Ehat_eq {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      ∑ c, X (chainEmb N r D.T.t (tieW hT i, c)) * X (chainEmb N r D.T.t (tieE hT i, c)) := by
  have e1 : finPos N (D.T.pos i) = Fin.castSucc (tieW hT i) := by
    apply Fin.ext
    simp only [finPos, tieW, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  have e2 : finPos N (D.T.pos i + 1) = Fin.castSucc (tieE hT i) := by
    apply Fin.ext
    simp only [finPos, tieE, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  rw [BlockData.Ehat, e1, e2]
  rfl

def pairP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    MvPolynomial (Fin N × Fin r) (KK O) :=
  ∑ c, X (tieW hT i, c) * X (tieE hT i, c)

theorem Ehat_eq' {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      rename (chainEmb N r D.T.t) (pairP O r hT i) := by
  rw [Ehat_eq hT i]
  simp [pairP, map_sum, rename_X]

theorem tieW_ne_tieE {D : BlockData N} (hT : TieOK D) (i i' : Fin D.T.t) : tieW hT i ≠ tieE hT i' := by
  intro h
  have := congrArg Fin.val h
  simp only [tieW, tieE] at this
  exact hT.sep i' i this.symm

theorem nv_Ehat {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.castSucc i)) (h2 : v ≠ scalS N r D.T.t (Fin.castSucc i))
    (h3 : ∀ c, v ≠ chainEmb N r D.T.t (tieW hT i, c)) (h4 : ∀ c, v ≠ chainEmb N r D.T.t (tieE hT i, c)) :
    v ∉ (D.Ehat O (r := r) i).vars := by
  rw [Ehat_eq hT i]
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_Eplus (D : BlockData N) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.last D.T.t)) (h2 : v ≠ scalS N r D.T.t (Fin.last D.T.t))
    (h3 : ∀ c, v ≠ Sum.inl (Fin.castSucc D.uPos, c)) (h4 : ∀ c, v ≠ xiVar N r D.T.t c) :
    v ∉ (D.Eplus O (r := r)).vars := by
  unfold BlockData.Eplus
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_xi {t b : ℕ} {v : BVar N r t} (h : ∀ c, v ≠ xiVar N r t c) {g : MvPolynomial (BVar N r t) (KK O)}
    (hg : g ∈ XiPolZ O N r t b) : v ∉ g.vars := by
  intro hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars v).1 hv
  have h1 := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 (Submodule.mem_inf.1 hg).1 hm
  obtain ⟨c, hc⟩ := h1.1 v hvm
  exact h c hc

def OddV (D : BlockData N) : BVar N r D.T.t → Prop
  | Sum.inl (a, _) => a ≠ Fin.castSucc D.uPos ∧ a ≠ Fin.last N
  | Sum.inr (l, _) => l ≠ Fin.last D.T.t

theorem tail_chain (D : BlockData N) (jp : ℕ) (a0 : Fin N) (ha0 : a0 ≠ D.uPos) (c : Fin r) (b : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = tailP O r D jp (cth (a0, c) b y) g := by
  have hfree : ∀ F : MvPolynomial (BVar N r D.T.t) (KK O), chainEmb N r D.T.t (a0, c) ∉ F.vars →
      ∀ μ ∈ F.support, μ (chainEmb N r D.T.t (a0, c)) = 0 := by
    intro F h μ hμ
    by_contra hne
    exact h ((MvPolynomial.mem_vars _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hne⟩)
  have hE : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r)).vars := by
    refine nv_Eplus D ?_ ?_ ?_ ?_
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalS]
    · intro c' h
      simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
      exact ha0 (Fin.castSucc_injective _ h.1)
    · intro c' h
      simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact Fin.castSucc_ne_last _ h.1
  have hP : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
      X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) (KK O)).vars := by
    refine nv_mul (nv_mul (nv_pow hE jp) (nv_prod _ fun i _ => nv_pow (nv_X ?_) _)) (nv_pow (nv_X ?_) _)
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalZ]
  have hg' : chainEmb N r D.T.t (a0, c) ∉ g.vars := by
    refine nv_xi (fun c' h => ?_) hg
    simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Fin.castSucc_ne_last _ h.1
  have key : ∀ Y : MvPolynomial (Fin N × Fin r) (KK O), tailP O r D jp Y g =
      (D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
        X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus) * (g * rename (chainEmb N r D.T.t) Y) := by
    intro Y
    unfold tailP
    ring
  rw [key, key, cth_mul_free _ _ (hfree _ hP), cth_mul_free _ _ (hfree _ hg'),
    cth_rename _ (chainEmb_inj N r D.T.t)]

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LiftSubstStart
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]
  simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

