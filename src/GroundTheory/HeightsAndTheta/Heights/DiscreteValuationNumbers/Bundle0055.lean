import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem subring_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R₁ R₂ : Subring F}
    (h₁ : B ≤ R₁) (h₂ : B ≤ R₂) (𝔭 : Ideal B) [𝔭.IsPrime]
    (hl₁ : letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭)
    (hl₂ : letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) : R₁ = R₂ := by
  have key : ∀ (R₁ R₂ : Subring F) (h₁ : B ≤ R₁) (h₂ : B ≤ R₂),
      (letI := (Subring.inclusion h₁).toAlgebra; IsLocalization.AtPrime R₁ 𝔭) →
      (letI := (Subring.inclusion h₂).toAlgebra; IsLocalization.AtPrime R₂ 𝔭) → R₁ ≤ R₂ := by
    intro R₁ R₂ h₁ h₂ hl₁ hl₂ z hz
    let _ := (Subring.inclusion h₁).toAlgebra
    let _ := (Subring.inclusion h₂).toAlgebra
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔭.primeCompl (⟨z, hz⟩ : R₁)
    obtain ⟨t, ht⟩ := (IsLocalization.map_units R₂ s).exists_right_inv
    have e₁ : z * ((s : B) : F) = ((b : B) : F) := congrArg Subtype.val hbs
    have e₂ : ((s : B) : F) * (t : F) = 1 := congrArg Subtype.val ht
    have hzt : z = (b : F) * t := by
      calc z = z * (((s : B) : F) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : B) : F)) * t := by ring
        _ = (b : F) * t := by rw [e₁]
    rw [hzt]
    exact R₂.mul_mem (h₂ b.2) t.2
  exact le_antisymm (key R₁ R₂ h₁ h₂ hl₁ hl₂) (key R₂ R₁ h₂ h₁ hl₂ hl₁)

theorem prime_eq_of_isLocalization_atPrime {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMax.proof (h₁ : BlowUpOverLocMaxPoint.Statement.{u})
    (h₂ : BlowUpOverLocPointMax.Statement.{u}) (h₃ : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  have hpt := h₁ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hmx := h₂ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  choose f hfT hfloc hfdeg using
    fun 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} => hpt 𝔫.1 𝔫.2

  have hmh : ∀ W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes, IsMultiHomogIdeal W' :=
    fun W' hW' => MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  refine ⟨Equiv.ofBijective (fun 𝔫 => ⟨f 𝔫, hfT 𝔫⟩) ⟨?_, ?_⟩, fun 𝔫 => ⟨hfloc 𝔫, hfdeg 𝔫⟩⟩
  ·
    intro 𝔫₁ 𝔫₂ h12
    have hf : f 𝔫₁ = f 𝔫₂ := congrArg Subtype.val h12
    have hl₁ := hfloc 𝔫₁
    rw [hf] at hl₁
    obtain ⟨k₁, l₁⟩ := hl₁
    obtain ⟨k₂, l₂⟩ := hfloc 𝔫₂
    have := 𝔫₁.2.isPrime
    have := 𝔫₂.2.isPrime
    exact Subtype.ext (prime_eq_of_isLocalization_atPrime k₂ 𝔫₁.1 𝔫₂.1 l₁ l₂)
  ·
    rintro ⟨W', hW'⟩
    obtain ⟨k, 𝔫, h𝔫, hl⟩ := hmx W' hW'.1 hW'.2.1 hW'.2.2
    refine ⟨⟨𝔫, h𝔫⟩, Subtype.ext ?_⟩
    obtain ⟨k', hl'⟩ := hfloc ⟨𝔫, h𝔫⟩
    have := h𝔫.isPrime
    have hring : blowUpLocRing P u (f ⟨𝔫, h𝔫⟩) = blowUpLocRing P u W' :=
      subring_eq_of_isLocalization_atPrime k' k 𝔫 hl' hl
    have hT := hfT ⟨𝔫, h𝔫⟩
    exact h₃ O K ι J P u _ _ hT.1.1.1 (hmh _ hT.1) hT.2.1 (le_trans le_sup_left hT.1.1.2)
      hW'.1.1.1 (hmh _ hW'.1) hW'.2.1 (le_trans le_sup_left hW'.1.1.2) hring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PChartsInColon
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

open scoped Pointwise

section

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

theorem ChartsInColon.prod_mem_pow {ι : Type*} (M : Submodule A L) (s : Finset ι) (x : ι → L)
    (hx : ∀ i ∈ s, x i ∈ M) : ∏ i ∈ s, x i ∈ M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.one_le.mp (le_refl (1 : Submodule A L))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact Submodule.mul_mem_mul (hx i (Finset.mem_insert_self i s))
      (ih fun k hk => hx k (Finset.mem_insert_of_mem hk))

theorem ChartsInColon.exists_mul_pow_mem {J : Type*} (a : J → A) (j : J) (hj : algebraMap A L (a j) ≠ 0)
    {g : L} (hg : g ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) :
    ∃ m : ℕ, g * algebraMap A L (a j) ^ m ∈
      (Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a))) ^ m := by
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hmem : ∀ k, algebraMap A L (a k) ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨1, ?_⟩
    simpa only [pow_one, div_mul_cancel₀ _ hj] using hmem k
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, pow_zero, mul_one]; exact Submodule.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := Submodule.mul_mem_mul hm (Submodule.pow_mem_pow I (hmem j) n)
    have h2 := Submodule.mul_mem_mul hn (Submodule.pow_mem_pow I (hmem j) m)
    rw [← pow_add] at h1 h2
    rw [add_comm n m] at h2
    convert add_mem h1 h2 using 1
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h := Submodule.mul_mem_mul hm hn
    rw [← pow_add] at h
    convert h using 1
    ring

end

theorem ChartsInColon.proof : ChartsInColon.Statement.{u} := by
  classical
  intro A _ L _ _ J _ a f hf
  unfold blowUpColon
  set b : J → L := fun k => algebraMap A L (a k) with hb
  set I := Submodule.map (Algebra.linearMap A L) (Ideal.span (Set.range a)) with hI
  have hIspan : I = Submodule.span A (Set.range b) := by
    rw [hI, Ideal.span, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmem : ∀ k, b k ∈ I := fun k =>
    Submodule.mem_map_of_mem (f := Algebra.linearMap A L) (Ideal.subset_span ⟨k, rfl⟩)
  have hex : ∀ j, ∃ m : ℕ, b j ≠ 0 → f * b j ^ m ∈ I ^ m := by
    intro j
    by_cases hj : b j = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨m, hm⟩ := ChartsInColon.exists_mul_pow_mem a j hj (hf j hj)
      exact ⟨m, fun _ => hm⟩
  choose m hm using hex
  set M := ∑ j, m j with hM
  refine Submodule.mem_iSup_of_mem (Fintype.card J * M + 1) ?_
  rw [Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [hIspan, Submodule.span_pow] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := Set.mem_pow.mp hx
    choose k hk using fun i => (g i).2
    have hx' : (List.ofFn fun i => (g i : L)).prod = ∏ i, b (k i) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => (hk i).symm
    rw [hx']
    obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := k) (n := M)
      (by rw [Fintype.card_fin]; omega)
    set s := Finset.univ.filter fun i => k i = j with hs
    set t := Finset.univ.filter fun i => ¬ k i = j with ht
    have hsplit : ∏ i, b (k i) = b j ^ s.card * ∏ i ∈ t, b (k i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => k i = j), ← Finset.prod_const]
      congr 1
      exact Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    have hcard : s.card + t.card = Fintype.card J * M + 1 := by
      rw [hs, ht, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have ht' : ∏ i ∈ t, b (k i) ∈ I ^ t.card :=
      ChartsInColon.prod_mem_pow I t _ fun i _ => hmem (k i)
    rw [hsplit]
    by_cases hbj : b j = 0
    · rw [hbj, zero_pow (by omega), zero_mul, mul_zero]
      exact zero_mem _
    · have hmj : m j ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h1 := Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hm j hbj) (Submodule.pow_mem_pow I (hmem j) (s.card - m j))) ht'
      rw [← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega), hcard] at h1
      convert h1 using 1
      have hc : s.card - m j + m j = s.card := Nat.sub_add_cancel (by omega)
      conv_lhs => rw [← hc, pow_add]
      ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HsymmShiftProof

open NumericalSegreProof

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] [DecidableEq K] in

theorem length_rootList {n : ℕ} (x : Fin n → K → ℤ) (α : Fin n → ℕ) :
    (rootList x α).length = ∑ i, α i := by
  unfold rootList
  simp [List.length_flatMap, Fin.sum_univ_def]

theorem cons_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F W ((c + c') :: l) = intNumL F W (c :: l) + intNumL F W (c' :: l) := by
  have key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get := by
    intro e
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd
    ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

theorem replicate_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W)
    (z s : K → ℤ) : ∀ (n : ℕ) (L : List (K → ℤ)),
    FieldNumbers.relDim W = ((n + L.length : ℕ) : WithBot (WithTop ℤ)) →
    intNumL F W (List.replicate n (z + s) ++ L) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) *
        intNumL F W (List.replicate (n - k) z ++ List.replicate k s ++ L)
  | 0, L, _ => by simp
  | n + 1, L, hd => by
    have hd' : ∀ c : K → ℤ,
        FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by
      intro c
      rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rw [List.replicate_succ, List.cons_append,
      cons_add W hW _ (by rw [hd, List.length_append, List.length_replicate]; congr 1; omega) z s,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s))).symm,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s)) (a := s)).symm,
      replicate_add W hW z s n (z :: L) (hd' z), replicate_add W hW z s n (s :: L) (hd' s),
      ProjectiveBundleNumbers.sum_choose_succ n (fun k => intNumL F W (List.replicate (n + 1 - k) z ++ List.replicate k s ++ L))]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1
      refine intNumL_perm F W ?_
      rw [show n + 1 - k = (n - k) + 1 by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ List.perm_middle
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [show n + 1 - (k + 1) = n - k by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

def H (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ) (L : List (K → ℤ)) : ℤ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple n c, intNumL F W (rootList x α ++ L)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_zero (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (L : List (K → ℤ)) :
    H W x 0 L = intNumL F W L := by
  simp [H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_one (W : Ideal (MRing ι F)) (x : Fin 1 → K → ℤ) (c : ℕ) (L : List (K → ℤ)) :
    H W x c L = intNumL F W (List.replicate c (x 0) ++ L) := by
  unfold H
  rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]
  simp [rootList]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_perm (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ)
    {L L' : List (K → ℤ)} (h : L.Perm L') : H W x c L = H W x c L' :=
  Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)

theorem H_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) {n : ℕ} (x : Fin n → K → ℤ)
    (c : ℕ) (L : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((c + 1 + L.length : ℕ) : WithBot (WithTop ℤ))) (a b : K → ℤ) :
    H W x c ((a + b) :: L) = H W x c (a :: L) + H W x c (b :: L) := by
  unfold H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlen : (rootList x α).length = c := by
    rw [length_rootList]
    exact Finset.Nat.mem_antidiagonalTuple.mp hα
  rw [intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]
  exact cons_add W hW _
    (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem H_succ (W : Ideal (MRing ι F)) {i : ℕ} (x : Fin (i + 1) → K → ℤ) (c : ℕ)
    (L : List (K → ℤ)) :
    H W x (c + 1) L = H W (fun j => x (Fin.castSucc j)) (c + 1) L + H W x c (x (Fin.last i) :: L) := by
  unfold H
  rw [sum_antidiagonalTuple_succ]
  congr 1
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [rootList_snoc_zero]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [rootList_update_last, List.append_assoc, List.singleton_append]

theorem sum_choose_pascal (M r : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((M + 1).choose k : ℤ) * f k =
      ∑ k ∈ Finset.range (r + 1 + 1), (M.choose k : ℤ) * f k +
        ∑ k ∈ Finset.range (r + 1), (M.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

theorem main (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (s : K → ℤ) :
    ∀ (N : ℕ) (x : Fin (N + 1) → K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
    FieldNumbers.relDim W = ((r + Y.length : ℕ) : WithBot (WithTop ℤ)) →
    H W (fun i => x i + s) r Y =
      ∑ k ∈ Finset.range (r + 1), ((N + r).choose k : ℤ) * H W x (r - k) (List.replicate k s ++ Y)
  | 0, x, r, Y, hd => by
    rw [H_one, replicate_add W hW (x 0) s r Y hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r]
  | N + 1, x, r, Y, hd => by
    induction r generalizing Y with
    | zero => simp [H_zero]
    | succ r ih =>
      have e1 := main W hW s N (fun j => x (Fin.castSucc j)) (r + 1) Y hd
      have e2 := ih (x (Fin.last (N + 1)) :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have e3 := ih (s :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have hadd := H_add W hW (fun i => x i + s) r Y hd (x (Fin.last (N + 1))) s
      have hAB : ∑ k ∈ Finset.range (r + 1 + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - k) (List.replicate k s ++ Y) =
          ∑ k ∈ Finset.range (r + 1 + 1), ((N + (r + 1)).choose k : ℤ) *
              H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y) +
            ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
              H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y) := by
        rw [show N + (r + 1) = N + 1 + r by omega, Finset.sum_range_succ,
          Finset.sum_range_succ (fun k => ((N + 1 + r).choose k : ℤ) *
            H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y)),
          Nat.sub_self, H_zero, H_zero,
          add_right_comm _ _ (∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y)),
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, H_succ W x (r - k) (List.replicate k s ++ Y),
          ← mul_add, H_perm W x (r - k) (List.perm_middle (l₁ := List.replicate k s)).symm]
      have hC : ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - (k + 1)) (List.replicate (k + 1) s ++ Y) =
          ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ s :: Y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_add_right, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [H_succ W (fun i => x i + s) r Y]
      beta_reduce at e1 ⊢
      rw [e1, hadd, e2, e3, show N + 1 + (r + 1) = N + 1 + r + 1 by omega,
        sum_choose_pascal (N + 1 + r) r (fun k => H W x (r + 1 - k) (List.replicate k s ++ Y)), hAB, hC]
      ring

end HsymmShiftProof

theorem HsymmShift.proof : HsymmShift.Statement.{u} := by
  intro F _ K _ _ ι _ W hW d hd N hN x s r Y hrY
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])
  simp only [HsymmShiftProof.H] at h
  rw [h, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.append_assoc]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in

theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpLocRingFrac.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
          (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

