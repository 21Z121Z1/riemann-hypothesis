import Formalism.GaloisIrreducibility.Statement

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable
section
namespace Formalism.GaloisIrreducibility

theorem alternating_group_not_solvable : AltNotSolvable := by
  intro α _ _ h hA
  have hcard : 5 ≤ Cardinal.mk α := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast h
  refine Equiv.Perm.not_isSolvable α hcard ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.FewLargeParts
section
namespace Formalism.GaloisIrreducibility

open Finset

lemma prod_lpart_dvd (n : ℕ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    (∏ l ∈ S, l ^ padicValNat l n) ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert l S hl ih =>
    rw [Finset.prod_insert hl]
    have hlp : l.Prime := hS l (Finset.mem_insert_self l S)
    have ih' := ih (fun l' hl' => hS l' (Finset.mem_insert_of_mem hl'))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro l' hl'
      have hl'p : l'.Prime := hS l' (Finset.mem_insert_of_mem hl')
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes hlp hl'p).2 (fun h => hl (h ▸ hl'))
    · exact pow_padicValNat_dvd
    · exact ih'

theorem few_large_cycle_parts : FewLargeParts := by
  intro n B S hn hB hS hne hlarge
  have hdvd := prod_lpart_dvd n S hS
  have hle : (∏ l ∈ S, l ^ padicValNat l n) ≤ n := Nat.le_of_dvd (by omega) hdvd
  calc B ^ S.card = ∏ _l ∈ S, B := by rw [Finset.prod_const]
    _ < ∏ l ∈ S, ((l ^ padicValNat l n : ℕ) : ℝ) :=
        Finset.prod_lt_prod_of_nonempty (fun _ _ => hB) hlarge hne
    _ = ((∏ l ∈ S, l ^ padicValNat l n : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ n := by exact_mod_cast hle

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
section
namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

@[simp] lemma bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : bord M 0 0 = 1 := by
  simp [bord]
@[simp] lemma bord_zero_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
@[simp] lemma bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
@[simp] lemma bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]

lemma bord_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) R) : bord M * bord N = bord (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma bord_one {m : ℕ} : bord (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply]

lemma bord_isUnit {m : ℕ} {M : Matrix (Fin m) (Fin m) R} (h : IsUnit M) : IsUnit (bord M) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨bord (u : Matrix (Fin m) (Fin m) R), bord (↑u⁻¹ : Matrix (Fin m) (Fin m) R), ?_, ?_⟩, rfl⟩
  · first
    | rw [bord_mul, Units.mul_inv, bord_one]
    | simp [bord_mul, bord_one]
  · first
    | rw [bord_mul, Units.inv_mul, bord_one]
    | simp [bord_mul, bord_one]

lemma bord_diag {n : ℕ} (d : R) :
    bord (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) =
      diagonal fun i : Fin (n+2) => if (i : ℕ) = n + 1 then d else 1 := by
  have h0 : (0 : ℕ) ≠ n + 1 := by omega
  have h0' : n + 1 ≠ 0 := by omega
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, h0, h0']

lemma bord_map {S : Type} [CommRing S] (φ : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (bord M).map φ = bord (M.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.map_apply]

lemma rank_add_le' {K : Type} [Field K] {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_bord_le {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) :
    (bord M).rank ≤ M.rank + 1 := by
  classical
  let S : Matrix (Fin (m+1)) (Fin m) K := Matrix.of fun i k => if i = k.succ then 1 else 0
  let T : Matrix (Fin m) (Fin (m+1)) K := Matrix.of fun k j => if j = k.succ then 1 else 0
  let S' : Matrix (Fin (m+1)) (Fin 1) K := Matrix.of fun i _ => if i = 0 then 1 else 0
  let T' : Matrix (Fin 1) (Fin (m+1)) K := Matrix.of fun _ j => if j = 0 then 1 else 0
  have hsplit : bord M = S' * T' + S * M * T := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [S, T, S', T', Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hsplit]
  refine (rank_add_le' _ _).trans ?_
  have h1 : (S' * T').rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width S')
  have h2 : (S * M * T).rank ≤ M.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

def Equi {s : ℕ} (A B : Matrix (Fin s) (Fin s) R) : Prop :=
  ∃ P Q : Matrix (Fin s) (Fin s) R, IsUnit P ∧ IsUnit Q ∧ P * A * Q = B

lemma Equi.trans {s : ℕ} {A B C : Matrix (Fin s) (Fin s) R} (h1 : Equi A B) (h2 : Equi B C) :
    Equi A C := by
  unfold Equi at h1 h2 ⊢
  obtain ⟨P1, Q1, hP1, hQ1, rfl⟩ := h1
  obtain ⟨P2, Q2, hP2, hQ2, rfl⟩ := h2
  exact ⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩

lemma Equi.rank_map {K : Type} [Field K] (φ : R →+* K) {s : ℕ}
    {A B : Matrix (Fin s) (Fin s) R} (h : Equi A B) : (B.map φ).rank = (A.map φ).rank := by
  unfold Equi at h
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  have hP' : IsUnit (P.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hP.map φ.mapMatrix
  have hQ' : IsUnit (Q.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hQ.map φ.mapMatrix
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP']

lemma perm_isUnit {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin s) (Fin s) R) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, rfl⟩
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

lemma equi_submatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (σ τ : Equiv.Perm (Fin s)) :
    Equi A (A.submatrix σ τ) := by
  unfold Equi
  refine ⟨σ.toPEquiv.toMatrix, τ.symm.toPEquiv.toMatrix, perm_isUnit σ, perm_isUnit τ.symm, ?_⟩
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

lemma clear {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hu : IsUnit (A 0 0)) :
    ∃ A' : Matrix (Fin m) (Fin m) R, Equi A (bord A') := by
  obtain ⟨b, hb⟩ : ∃ b : R, A 0 0 * b = 1 := ⟨_, hu.mul_val_inv⟩
  have hb' : b * A 0 0 = 1 := by rw [mul_comm]; exact hb
  set P : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (-(A i.succ 0 * b)) (fun j => if i = j then 1 else 0))) with hP
  set Pinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (A i.succ 0 * b) (fun j => if i = j then 1 else 0))) with hPinv
  set Q : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons b (fun j => -(b * A 0 j.succ)))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQ
  set Qinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons (A 0 0) (fun j => A 0 j.succ))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQinv
  set A' : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * b * A 0 j.succ
    with hA'
  have hPP : P * Pinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hP, hPinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hQQ : Q * Qinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hQ, hQinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb']
  have hPu : IsUnit P := by
    have h : P.det * Pinv.det = 1 := by rw [← Matrix.det_mul, hPP, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have hQu : IsUnit Q := by
    have h : Q.det * Qinv.det = 1 := by rw [← Matrix.det_mul, hQQ, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have key : P * A * Q = bord A' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination hb | linear_combination (-1 : R) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A 0 j.succ)) * hb | linear_combination (A 0 j.succ) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A i.succ 0 * b)) * hb' | linear_combination (A i.succ 0 * b) * hb'
    · simp [hP, hQ, hA', Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first
        | linear_combination (A i.succ 0 * b * A 0 j.succ) * hb'
        | linear_combination (-(A i.succ 0 * b * A 0 j.succ)) * hb'
  refine ⟨A', ?_⟩
  unfold Equi
  exact ⟨P, Q, hPu, hQu, key⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R] [IsLocalRing R]

lemma main (n : ℕ) : ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    n ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ d : R, Equi A (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) := by
  induction n with
  | zero =>
    intro A _
    refine ⟨A 0 0, ?_⟩
    unfold Equi
    refine ⟨1, 1, isUnit_one, isUnit_one, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp
  | succ n ih =>
    intro A hA
    obtain ⟨i, j, hij⟩ : ∃ i j, IsUnit (A i j) := by
      by_contra hne
      push_neg at hne
      have h0 : A.map (IsLocalRing.residue R) = 0 := by
        ext i j
        simp only [Matrix.map_apply, Matrix.zero_apply]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hne i j))
      rw [h0, Matrix.rank_zero] at hA
      omega
    have hu : IsUnit ((A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j)) 0 0) := by
      simpa using hij
    obtain ⟨A', e2⟩ := clear _ hu
    have e12 : Equi A (bord A') := (equi_submatrix A _ _).trans e2
    have hr : n ≤ (A'.map (IsLocalRing.residue R)).rank := by
      have h1 := e12.rank_map (IsLocalRing.residue R)
      have h2 := rank_bord_le (A'.map (IsLocalRing.residue R))
      rw [← bord_map, h1] at h2
      omega
    obtain ⟨d, hd⟩ := ih A' hr
    unfold Equi at hd
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := hd
    refine ⟨d, e12.trans ?_⟩
    unfold Equi
    refine ⟨bord P, bord Q, bord_isUnit hP, bord_isUnit hQ, ?_⟩
    rw [bord_mul, bord_mul, hPQ, bord_diag]

end BorderedIndexCases

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum
section
namespace Formalism.GaloisIrreducibility

open Classical

lemma orbit_iterate_mem {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O)
    {x : α} (hx : x ∈ O) : ∀ n : ℕ, f^[n] x ∈ O := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hO.1 _ ih

lemma orbit_image_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.image f = O := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO.1 x hx
  · intro y hy
    obtain ⟨n, hn⟩ := hO.2 (f y) (hO.1 y hy) y hy
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hn
    exact Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩

lemma orbit_map_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by
  have hinj : Set.InjOn f O := by
    rw [← Finset.card_image_iff, orbit_image_eq hO]
  rw [← Finset.image_val_of_injOn hinj, orbit_image_eq hO]

lemma orbit_le {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) {M' : Multiset α}
    (hM : M'.map f = M') {x : α} (hxO : x ∈ O) (hxM : x ∈ M') : O.val ≤ M' := by
  rw [Multiset.le_iff_subset O.nodup]
  intro y hy
  obtain ⟨n, rfl⟩ := hO.2 x hxO y (Finset.mem_val.mp hy)
  clear hy
  induction n with
  | zero => simpa using hxM
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hM]
    exact Multiset.mem_map_of_mem f ih

theorem invariant_multiset_orbit_sum {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro M' hO hle hM
  by_cases h0 : M' = 0
  · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h0
  have hxs : x ∈ ∑ i ∈ I, (O i).val := Multiset.mem_of_le hle hx
  rw [Multiset.mem_sum] at hxs
  obtain ⟨i0, hi0, hxi⟩ := hxs
  have hle0 : (O i0).val ≤ M' := orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx
  obtain ⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M'' :=
    ⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩
  have hM'' : M''.map f = M'' := by
    rw [Multiset.map_add, orbit_map_eq (hO i0 hi0)] at hM
    exact add_left_cancel hM
  have hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val := by
    rw [← Finset.add_sum_erase I _ hi0] at hle
    exact (add_le_add_iff_left _).mp hle
  obtain ⟨J, hJ, hc⟩ := ih (I.erase i0) (Finset.erase_ssubset hi0) M''
    (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''
  refine ⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩
  have hnot : i0 ∉ J := fun h => by simpa using hJ h
  rw [Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]

theorem orbit_subset_sum : OrbitSubSum := by
  intro α ι f O I M' hO hle hM
  exact invariant_multiset_orbit_sum f O I M' hO hle hM

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
section
namespace Formalism.GaloisIrreducibility

theorem power_of_p_cycle : PowerPCycle := by
  intro α _ _ σ p hp hmem hcard
  have hdvd : p ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hmem
  have hpos : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  refine ⟨orderOf σ / p, ?_⟩
  have hord : orderOf (σ ^ (orderOf σ / p)) = p := orderOf_pow_orderOf_div hpos hdvd
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ ^ (orderOf σ / p)) (by rw [hord]; exact hp)
  rw [hord] at hn
  have hsum : (σ ^ (orderOf σ / p)).support.card = (n + 1) * p := by
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul]
  have hle : (σ ^ (orderOf σ / p)).support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    have h3 : 2 * p ≤ Fintype.card α := h2.trans (hsum ▸ hle)
    omega
  subst hn0
  refine ⟨?_, by rw [hsum]; ring⟩
  rw [← Equiv.Perm.card_cycleType_eq_one, hn]
  simp

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.ResiduesLe
section
namespace Formalism.GaloisIrreducibility

open Finset

theorem card_pow_eq_one_le_two_mul {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [IsCyclic H] (hH : H.index ≤ 2) {D : ℕ} (hD : 0 < D) :
    #{a : G | a ^ D = 1} ≤ 2 * D := by
  classical
  set S : Subgroup G := (powMonoidHom D : G →* G).ker with hSdef
  have hmem : ∀ a : G, a ∈ S ↔ a ^ D = 1 := fun a => by simp [hSdef]
  have hcardS : #{a : G | a ^ D = 1} = Nat.card S := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun a => (hmem a).symm))
  rw [hcardS]
  have hK : IsCyclic (H ⊓ S : Subgroup G) := Subgroup.isCyclic_of_le inf_le_left
  have h1 : Nat.card (H ⊓ S : Subgroup G) ≤ D := by
    rw [← IsCyclic.exponent_eq_card]
    apply Nat.le_of_dvd hD
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    have : (g : G) ^ D = 1 := (hmem g).1 g.2.2
    ext; simpa using this
  have h2 : H.relIndex S ≤ 2 := by
    have hd := Subgroup.relIndex_dvd_index_of_normal H S
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hH
  have h3 : Nat.card (H ⊓ S : Subgroup G) * H.relIndex S = Nat.card S := by
    have := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ S) S bot_le inf_le_right
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at this
    exact this
  rw [← h3]
  calc Nat.card (H ⊓ S : Subgroup G) * H.relIndex S ≤ D * 2 := Nat.mul_le_mul h1 h2
    _ = 2 * D := by ring

theorem card_residues_le_units (n D : ℕ) [NeZero n] (hD : 0 < D) :
    ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{u : (ZMod n)ˣ | u ^ D = 1} := by
  classical
  have step1 : ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{y : ZMod n | y ^ D = 1} := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => (x : ZMod n))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      have := (ZMod.natCast_eq_natCast_iff (x ^ D) 1 n).2 hx.2
      push_cast at this
      exact this
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy
      have h := congrArg ZMod.val hxy
      simp only [ZMod.val_natCast] at h
      rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  refine step1.trans ?_
  have hsub : ({y : ZMod n | y ^ D = 1} : Finset (ZMod n)) ⊆
      Finset.image (fun u : (ZMod n)ˣ => (u : ZMod n))
        (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ D = 1)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : y * y ^ (D - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hD, hy]
    refine ⟨⟨y, y ^ (D - 1), h1, by rw [mul_comm]; exact h1⟩, ?_, rfl⟩
    ext; simpa using hy
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem index_zpowers_five (n : ℕ) (h : Nat.Coprime 5 (2 ^ (n + 2))) :
    (Subgroup.zpowers (ZMod.unitOfCoprime 5 h)).index = 2 := by
  have hc := Subgroup.card_mul_index (Subgroup.zpowers (ZMod.unitOfCoprime 5 h))
  rw [Nat.card_zpowers, ← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat,
    ZMod.orderOf_five, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)] at hc
  have : 2 ^ (n + 2 - 1) * (2 - 1) = 2 ^ n * 2 := by
    rw [show n + 2 - 1 = n + 1 by omega, pow_succ]; norm_num
  rw [this] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc

theorem residues_count_le : ResiduesLe := by
  classical
  intro l j D hl hD
  have hD0 : 0 < D := hD
  have : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine (card_residues_le_units (l ^ j) D hD0).trans ?_
  by_cases hcyc : IsCyclic (ZMod (l ^ j))ˣ
  · exact card_pow_eq_one_le_two_mul (⊤ : Subgroup (ZMod (l ^ j))ˣ)
      (by rw [Subgroup.index_top]; norm_num) hD0
  · have hl2 : l = 2 := by
      by_contra hne
      exact hcyc (ZMod.isCyclic_units_of_prime_pow l hl hne j)
    subst hl2
    have hj : ¬ j ≤ 2 := fun hj => hcyc ((ZMod.isCyclic_units_two_pow_iff j).2 hj)
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    have h5 : Nat.Coprime 5 (2 ^ (n + 2)) :=
      Nat.Coprime.pow_right _ (by norm_num)
    exact card_pow_eq_one_le_two_mul (Subgroup.zpowers (ZMod.unitOfCoprime 5 h5))
      (by rw [index_zpowers_five n h5]) hD0

end Formalism.GaloisIrreducibility
end

