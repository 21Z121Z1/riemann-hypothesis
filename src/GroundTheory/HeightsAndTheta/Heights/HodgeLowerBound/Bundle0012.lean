import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FsInvPow

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_h_eq (a : K → ℤ) (z : (Σ k, ι k) → ℂ) :
    (fsHerm ι a).h z = (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h z := by
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h : (fsHerm ι a).h = (HermLine.ofMetrics (fun k => fsMetric (ι k)) a).h := funext (fsHerm_h_eq a)
  unfold IsSmoothHerm
  rw [h]
  exact Inter.isSmoothHerm_ofMetrics_fs a

theorem isSmoothHerm_fsMulti : IsSmoothHerm (GroundTheory.Heights₂.Heights.fsMulti ι) := by
  unfold GroundTheory.Heights₂.Heights.fsMulti
  exact Inter.isSmoothHerm_ofMetrics_fs _

abbrev invTensor (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsHerm ι (fun _ => -1)).tensor (GroundTheory.Heights₂.Heights.fsMulti ι)

theorem isSmoothHerm_invTensor : IsSmoothHerm (invTensor ι) := by
  show ContDiffOn ℝ _ (fun z => (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z) _
  exact (isSmoothHerm_fsHerm _).mul isSmoothHerm_fsMulti

theorem invTensor_a (k : K) : (invTensor ι).a k = ((0 : K → ℕ) k : ℤ) := by
  show (-1 : ℤ) + 1 = _
  simp

theorem invTensor_h {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (invTensor ι).h z = 1 := by
  show (fsHerm ι (fun _ => -1)).h z * (GroundTheory.Heights₂.Heights.fsMulti ι).h z = 1
  rw [fsHerm_h_eq]
  unfold GroundTheory.Heights₂.Heights.fsMulti
  rw [Inter.ofMetrics_fs_h, Inter.ofMetrics_fs_h, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hS : Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩)).ne'
  show Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (-1 : ℤ) * Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ (1 : ℤ) = 1
  rw [zpow_neg_one, zpow_one]
  exact inv_mul_cancel₀ hS

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_eq_zero {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem snoc_invTensor (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    II K ι P (n + 1) (Fin.snoc L (invTensor ι)) = 0 := by
  have h1 : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
    classical
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hne : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [(hII K ι).2.2 P n L (invTensor ι) 1 0 hP hL isSmoothHerm_invTensor invTensor_a h1 hne]
  unfold recR
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    unfold divSupp
    rw [Ideal.span_singleton_one, sup_top_eq, Ideal.minimalPrimes_top]
    simp
  have hint : arInt P 1 (invTensor ι) L = 0 := by
    unfold arInt
    refine ptsIntegral_eq_zero P _ _ fun z hz => ?_
    simp [logNorm, invTensor_h hz.1]
  simp [hsupp, hint]

theorem intersection_update_fsHerm_neg_one (II : IntersectionSystem) (hII : IsIntersectionSystem II) (P : Ideal (MRing ι)) (n : ℕ)
    (M : Fin (n + 1) → HermLine ι) (hP : IsArithVar P (n + 1)) (hM : ∀ i, IsSmoothHerm (M i))
    (j : Fin (n + 1)) :
    II K ι P (n + 1) (Function.update M j (fsHerm ι fun _ => -1)) =
      -II K ι P (n + 1) (Function.update M j (GroundTheory.Heights₂.Heights.fsMulti ι)) := by
  let σ := Equiv.swap j (Fin.last n)
  let L : Fin n → HermLine ι := fun i => M (σ (Fin.castSucc i))
  have hL : ∀ i, IsSmoothHerm (L i) := fun i => hM _
  have key : ∀ C, Function.update M j C ∘ σ = Fin.snoc L C := by
    intro C
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp only [Function.comp_apply, Fin.snoc_castSucc, L]
      rw [Function.update_of_ne]
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact (Fin.castSucc_lt_last i).ne h
  have hsm : ∀ C, IsSmoothHerm C → ∀ i, IsSmoothHerm (Function.update M j C i) := by
    intro C hC i
    by_cases h : i = j
    · subst h
      simpa using hC
    · rw [Function.update_of_ne h]
      exact hM i
  have hsym : ∀ C, IsSmoothHerm C →
      II K ι P (n + 1) (Function.update M j C) = II K ι P (n + 1) (Fin.snoc L C) := by
    intro C hC
    rw [← key C]
    exact ((hII K ι).1 P (n + 1) _ σ hP (hsm C hC)).symm
  rw [hsym _ (isSmoothHerm_fsHerm _), hsym _ isSmoothHerm_fsMulti]
  have hadd := (hII K ι).2.1 P n L (fsHerm ι fun _ => -1) (GroundTheory.Heights₂.Heights.fsMulti ι) hP hL
    (isSmoothHerm_fsHerm _) isSmoothHerm_fsMulti
  rw [snoc_invTensor II hII P n L hP hL] at hadd
  linarith

theorem proof : FsInvPow.Statement := by
  intro II K _ ι _ P d hII hP
  cases d with
  | zero =>
    rw [pow_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ n =>
    let M : ℕ → Fin (n + 1) → HermLine ι := fun k i =>
      if (i : ℕ) < k then GroundTheory.Heights₂.Heights.fsMulti ι else fsHerm ι fun _ => -1
    have hM : ∀ k i, IsSmoothHerm (M k i) := by
      intro k i
      dsimp only [M]
      split_ifs
      · exact isSmoothHerm_fsMulti
      · exact isSmoothHerm_fsHerm _
    have step : ∀ k, (hk : k < n + 1) →
        II K ι P (n + 1) (M k) = -II K ι P (n + 1) (M (k + 1)) := by
      intro k hk
      have h1 : Function.update (M k) ⟨k, hk⟩ (fsHerm ι fun _ => -1) = M k := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
      have h2 : Function.update (M k) ⟨k, hk⟩ (GroundTheory.Heights₂.Heights.fsMulti ι) = M (k + 1) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp [M]
        · rw [Function.update_of_ne h]
          have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          dsimp only [M]
          by_cases hi : (i : ℕ) < k
          · rw [if_pos hi, if_pos (by omega)]
          · rw [if_neg hi, if_neg (by omega)]
      rw [← h1, ← h2]
      exact intersection_update_fsHerm_neg_one II hII P n (M k) hP (hM k) ⟨k, hk⟩
    have hpow : ∀ k, k ≤ n + 1 → II K ι P (n + 1) (M 0) = (-1) ^ k * II K ι P (n + 1) (M k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [ih (by omega), step k (by omega), pow_succ]
        ring
    have h0 : M 0 = fun _ => fsHerm ι fun _ => -1 := by
      funext i
      simp [M]
    have hd : M (n + 1) = fun _ => GroundTheory.Heights₂.Heights.fsMulti ι := by
      funext i
      simp [M, i.isLt]
    rw [← h0, ← hd]
    exact hpow (n + 1) le_rfl

end FsInvPow

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagHeightMultilinear

theorem exists_perm_toList {α : Type} [DecidableEq α] {d : ℕ} (r : Fin d → α) :
    ∃ σ : Equiv.Perm (Fin d), ∀ (k : Fin d) (h : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length),
      (Multiset.map r Finset.univ.val).toList.get ⟨k, h⟩ = r (σ k) := by
  set l := (Multiset.map r Finset.univ.val).toList with hl
  have hlen : l.length = d := by simp [hl, Multiset.length_toList]
  let r' : Fin d → α := fun k => l.get ⟨k, by rw [hlen]; exact k.2⟩
  have hmap : Multiset.map r' Finset.univ.val = Multiset.map r Finset.univ.val := by
    rw [Fin.univ_val_map]
    have hof : List.ofFn r' = l := List.ext_get (by simp [hlen]) (fun k h1 h2 => by simp [r'])
    rw [hof, hl, Multiset.coe_toList]
  have hcard : ∀ a, Fintype.card {k // r' k = a} = Fintype.card {k // r k = a} := by
    intro a
    have h := congrArg (Multiset.count a) hmap
    rw [Multiset.count_map, Multiset.count_map] at h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    convert h using 3 <;> exact eq_comm
  refine ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hcard a)), fun k h => ?_⟩
  exact (Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (hcard a)) k).symm

section FS

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h := Inter.isSmoothHerm_ofMetrics_fs (ι := ι) a
  unfold IsSmoothHerm at h ⊢
  refine h.congr fun z _ => ?_
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem refNorm_mul {a b : K → ℤ} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    refNorm a z * refNorm b z = refNorm (a + b) z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem I_snoc_congr (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (ha : A.a = B.a) (hh : ∀ z ∈ mcPts P, A.h z = B.h z) :
    I P (n + 1) (Fin.snoc L A) = I P (n + 1) (Fin.snoc L B) := by
  have hBi := Inter.isSmoothHerm_hermZpow hB (-1)
  have h0 := Inter.DiagRAux.I_snoc_triv hI hP hL (Inter.isSmoothHerm_tensor hA hBi)
    (by
      show A.a + (Inter.hermZpow B (-1)).a = 0
      rw [Inter.DiagRAux.hermZpow_neg_one_a, ha, add_neg_cancel])
    (fun z hz => by
      show A.h z * (Inter.hermZpow B (-1)).h z = 1
      rw [Inter.DiagRAux.hermZpow_neg_one_h, hh z hz, mul_inv_cancel₀ (B.pos z hz.1).ne'])
  have h1 := hI.2.1 P n L A (Inter.hermZpow B (-1)) hP hL hA hBi
  have h2 := Inter.fam_snoc_zpow hI hP L hL hB (-1)
  rw [h0, h2] at h1
  push_cast at h1
  linarith

theorem I_snoc_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc L (fsHerm ι (a + b))) =
      I P (n + 1) (Fin.snoc L (fsHerm ι a)) + I P (n + 1) (Fin.snoc L (fsHerm ι b)) := by
  rw [← hI.2.1 P n L _ _ hP hL (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)]
  exact I_snoc_congr hI hP L hL (isSmoothHerm_fsHerm _)
    (Inter.isSmoothHerm_tensor (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)) rfl
    (fun z hz => (refNorm_mul hz.1).symm)

theorem I_update_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (a b : K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (Function.update v j (a + b) i)) =
      I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)) +
        I P (n + 1) (fun i => fsHerm ι (Function.update v j b i)) := by
  have hL : ∀ i, IsSmoothHerm (fsHerm ι (v i)) := fun i => isSmoothHerm_fsHerm _
  have e : ∀ c : K → ℤ, (fun i => fsHerm ι (Function.update v j c i)) =
      Function.update (fun i => fsHerm ι (v i)) j (fsHerm ι c) := by
    intro c
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Function.update_of_ne h]
  rw [e, e, e, Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _)]
  exact I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b

def fsMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    MultilinearMap ℤ (fun _ : Fin (n + 1) => K → ℤ) ℝ where
  toFun v := I P (n + 1) (fun i => fsHerm ι (v i))
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    exact I_update_fsHerm_add hI hP v j a b
  map_update_smul' := by
    intro inst v j c a
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk' (fun a => I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)))
      (fun a b => I_update_fsHerm_add hI hP v j a b)
    exact map_zsmul g c a

theorem fsMultilin_apply (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin (n + 1) → K → ℤ) :
    fsMultilin hI hP v = I P (n + 1) (fun i => fsHerm ι (v i)) := rfl

theorem I_fsHerm_sum (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin (n + 1) → α → ℤ) (x : α → K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (∑ p, ℓ i p • x p)) =
      ∑ r : Fin (n + 1) → α, (∏ i, (ℓ i (r i) : ℝ)) * I P (n + 1) (fun i => fsHerm ι (x (r i))) := by
  rw [← fsMultilin_apply hI hP, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ (fsMultilin hI hP) (fun i => ℓ i (r i)) (fun i => x (r i)),
    fsMultilin_apply, zsmul_eq_mul, Int.cast_prod]

end FS

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

theorem hFl_sum_monomial (II : IntersectionSystem) {β : Type} (s : Finset β) (m : β → (Ψ × Fin N) →₀ ℕ)
    (a : β → ℚ) :
    hFl Ψ N II (∑ b ∈ s, monomial (m b) (a b)) = ∑ b ∈ s, (a b : ℝ) * hFlMono Ψ N II (m b) := by
  classical
  have hsub : ∀ (F : RootPoly Ψ N) (S : Finset ((Ψ × Fin N) →₀ ℕ)), F.support ⊆ S →
      hFl Ψ N II F = ∑ m ∈ S, ((coeff m F : ℚ) : ℝ) * hFlMono Ψ N II m := by
    intro F S hS
    unfold hFl
    exact Finset.sum_subset hS fun m _ hm => by rw [notMem_support_iff.mp hm]; simp
  have hadd : ∀ F G : RootPoly Ψ N, hFl Ψ N II (F + G) = hFl Ψ N II F + hFl Ψ N II G := by
    intro F G
    rw [hsub (F + G) (F.support ∪ G.support) support_add,
      hsub F (F.support ∪ G.support) Finset.subset_union_left,
      hsub G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_add]
    push_cast
    ring
  have hmono : ∀ (m : (Ψ × Fin N) →₀ ℕ) (a : ℚ), hFl Ψ N II (monomial m a) = (a : ℝ) * hFlMono Ψ N II m := by
    intro m a
    rw [hsub _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  induction s using Finset.induction_on with
  | empty => simp [hsub 0 ∅ (by simp)]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hadd, hmono, ih]

omit [DecidableEq Ψ] in

theorem C_mul_prod_linForm (c : ℚ) {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    (C c * ∏ i, linForm Ψ N (ℓ i) : RootPoly Ψ N) =
      ∑ r : Fin d → Ψ × Fin N, monomial (∑ i, Finsupp.single (r i) 1) (c * ∏ i, (ℓ i (r i) : ℚ)) := by
  unfold linForm
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← C_mul_monomial]
  congr 1
  rw [show (∏ i, (ℓ i (r i) : ℚ)) = (∏ i, (ℓ i (r i) : ℚ)) * 1 from (mul_one _).symm, ← C_mul_monomial,
    monomial_sum_one]
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rfl

theorem hFlMono_sum_single (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)) (r : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    hFlMono Ψ N II (∑ i, Finsupp.single (r i) 1) =
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun i => xLine Ψ N (r i)) := by
  have hdeg : (∑ i, Finsupp.single (r i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  have hm : Finsupp.toMultiset (∑ i, Finsupp.single (r i) (1 : ℕ)) = Multiset.map r Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({r i} : Multiset (Ψ × Fin N))) = (fun p => {p}) ∘ r := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨σ, hσ⟩ := exists_perm_toList r
  have hML : monoLines Ψ N (∑ i, Finsupp.single (r i) 1) (dimFl Ψ N + 1) = (fun i => xLine Ψ N (r i)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
      omega
    unfold monoLines
    rw [hm, dif_pos hk, hσ k hk]
    rfl
  unfold hFlMono
  rw [if_pos hdeg, hML]
  exact (hII (FlBlock Ψ N) (FlIdx Ψ N)).1 _ _ _ σ hP fun j => isSmoothHerm_fsHerm _

end FlagHeightMultilinear

open FlagHeightMultilinear in

theorem HFlProdLinear.proof (hA : FlagArithVar.Statement) : HFlProdLinear.Statement := by
  intro II Ψ _ _ _ N d c ℓ hII hN hd
  subst hd
  have hP := hA Ψ N hN
  have hI := hII (FlBlock Ψ N) (FlIdx Ψ N)
  rw [C_mul_prod_linForm, hFl_sum_monomial]
  have hlin : (fun i => linLine Ψ N (ℓ i)) =
      fun i => fsHerm (FlIdx Ψ N) (∑ p, ℓ i p • xDeg Ψ N p) := by
    funext i
    unfold linLine linDeg
    congr 1
    funext q
    simp [Finset.sum_apply]
  rw [hlin, I_fsHerm_sum hI hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hFlMono_sum_single Ψ N II hII hP r]
  simp only [xLine]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

