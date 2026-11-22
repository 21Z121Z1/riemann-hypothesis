import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0003

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationCoactionStable
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_coaction_stable : FiltrationCoactionStable := by
  intro n _ M CF pi _ x hx l
  let L0 : (M.ι → ℤ) →+ (M.ι → ℤ) :=
    { toFun := fun x i => l (∑ k, M.A i k * (x k : GLCoord ℤ n))
      map_zero' := by funext i; simp
      map_add' := fun x y => by
        funext i
        simp only [Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib, map_add] }
  let L : (M.ι → ℤ) →ₗ[ℤ] (M.ι → ℤ) := L0.toIntLinearMap
  have hL : CF.Mpi pi ≤ (CF.Mpi pi).comap L := by
    unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro y ⟨j, hj, I, rfl⟩
    have : L (CF.vec j I) = ∑ K, l (TMat (CF.mu j) K I) • CF.vec j K := by
      funext i
      have h1 : L (CF.vec j I) i = l (∑ k, M.A i k * (CF.ph j k I : GLCoord ℤ n)) := rfl
      rw [h1, qb_equiv_apply, map_sum, Finset.sum_apply]
      refine sum_congr rfl fun K _ => ?_
      rw [← zsmul_eq_mul, map_zsmul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      rfl
    rw [SetLike.mem_coe, Submodule.mem_comap, this]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, K, rfl⟩)
  exact hL hx

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.HighestWeightSpaceFinite
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qr_ext {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  if e then insert (Fin.last m) (S.map Fin.castSuccEmb) else S.map Fin.castSuccEmb

section Ext

variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))

lemma qr_last_notMem : Fin.last m ∉ S.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h

lemma qr_mem_castSucc (a : Fin m) : a.castSucc ∈ qr_ext e S ↔ a ∈ S := by
  unfold qr_ext
  split_ifs <;> simp [(Fin.castSucc_lt_last a).ne]

lemma qr_mem_last : Fin.last m ∈ qr_ext e S ↔ e := by
  unfold qr_ext
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; exact qr_last_notMem S

lemma qr_ext_card : (qr_ext e S).card = S.card + if e then 1 else 0 := by
  unfold qr_ext
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (qr_last_notMem S), Finset.card_map]
  · rw [Finset.card_map]; rfl

lemma qr_ext_inj {S S' : Finset (Fin m)} (h : qr_ext e S = qr_ext e S') : S = S' := by
  ext a
  rw [← qr_mem_castSucc e S a, h, qr_mem_castSucc]

lemma qr_ext_surj (K : Finset (Fin (m + 1))) (h : Fin.last m ∈ K ↔ e) :
    K = qr_ext e (univ.filter fun a : Fin m => a.castSucc ∈ K) := by
  ext x
  induction x using Fin.lastCases with
  | last => rw [qr_mem_last, h]
  | cast a => rw [qr_mem_castSucc]; simp

lemma qr_filter_castSucc (t : Fin m) :
    ((qr_ext e S).filter (· ≤ t.castSucc)) = (S.filter (· ≤ t)).map Fin.castSuccEmb := by
  ext x
  induction x using Fin.lastCases with
  | last =>
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨_, h⟩; exact absurd h (not_le.2 (Fin.castSucc_lt_last t))
    · rintro ⟨a, _, h⟩; exact absurd h (Fin.castSucc_lt_last a).ne
  | cast a =>
    simp only [Finset.mem_filter, qr_mem_castSucc, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_inj,
      exists_eq_right, Fin.castSucc_le_castSucc_iff]

lemma qr_filter_last : ((qr_ext e S).filter (· ≤ Fin.last m)) = qr_ext e S := by
  apply Finset.filter_true_of_mem
  intro x _; exact Fin.le_last x

lemma qr_emb_map {k : ℕ} (h : S.card = k) (h' : (S.map Fin.castSuccEmb).card = k) :
    ⇑((S.map Fin.castSuccEmb).orderEmbOfFin h') = fun a => (S.orderEmbOfFin h a).castSucc := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a; simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono hab)

lemma qr_emb_insert {k : ℕ} (h : S.card = k) (h' : (insert (Fin.last m) (S.map Fin.castSuccEmb)).card = k + 1) :
    ⇑((insert (Fin.last m) (S.map Fin.castSuccEmb)).orderEmbOfFin h') =
      Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (S.orderEmbOfFin h a).castSucc) (Fin.last m) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    induction a using Fin.lastCases with
    | last => simp
    | cast a => simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Fin.castSucc_lt_last _
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.2 (Fin.le_last _))
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hab))

end Ext

section Block

variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

lemma qr_det_cast (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (fun a => (r a).castSucc) (fun a => (c a).castSucc)).det = (g1.val.submatrix r c).det := by
  congr 1
  ext a b
  exact hb.1 _ _

lemma qr_det_snoc (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).det =
      (t : R) * (g1.val.submatrix r c).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have h1 : ((h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).submatrix
        (Fin.last k).succAbove (Fin.last k).succAbove) = g1.val.submatrix r c := by
      ext a b
      simp [Fin.succAbove_last, hb.1]
    rw [h1]
    simp [hb.2.1, ← two_mul]
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
    simp [(hb.2.2 _).2]
  · simp

lemma qr_det_block (hb : IsBlock h g1 t) : h.val.det = (t : R) * g1.val.det := by
  have := qr_det_snoc hb (id : Fin m → Fin m) id
  have h1 : (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a : Fin m => (id a).castSucc) (Fin.last m)) = id := by
    funext a
    induction a using Fin.lastCases <;> simp
  rw [h1] at this
  simpa using this

lemma qr_minor_ext (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K' S : Finset (Fin m)) {k k' : ℕ}
    (hK' : K'.card = k') (hS' : S.card = k') (hK : (qr_ext e K').card = k) (hS : (qr_ext e S).card = k) :
    (h.val.submatrix ((qr_ext e K').orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det =
      (if e then (t : R) else 1) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
  by_cases he : e
  · have hk : k = k' + 1 := by rw [← hK, qr_ext_card, hK', if_pos he]
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k' + 1) (hB : B.card = k' + 1),
        A = insert (Fin.last m) (K'.map Fin.castSuccEmb) → B = insert (Fin.last m) (S.map Fin.castSuccEmb) →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (t : R) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_insert K' hK', qr_emb_insert S hS', qr_det_snoc hb]
    rw [if_pos he]
    exact key _ _ hK hS (by rw [qr_ext, if_pos he]) (by rw [qr_ext, if_pos he])
  · have hk : k = k' := by rw [← hK, qr_ext_card, hK', if_neg he]; rfl
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k) (hB : B.card = k),
        A = K'.map Fin.castSuccEmb → B = S.map Fin.castSuccEmb →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_map K' hK', qr_emb_map S hS', qr_det_cast hb]
    rw [if_neg he, one_mul]
    exact key _ _ hK hS (by rw [qr_ext, if_neg he]) (by rw [qr_ext, if_neg he])

lemma qr_minor_zero (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K : Finset (Fin (m + 1))) (S : Finset (Fin m))
    {k : ℕ} (hK : K.card = k) (hS : (qr_ext e S).card = k) (hne : ¬ (Fin.last m ∈ K ↔ e)) :
    (h.val.submatrix (K.orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det = 0 := by
  by_cases he : e
  · have hl : Fin.last m ∉ K := fun hl => hne ⟨fun _ => he, fun _ => hl⟩
    have h1 : Fin.last m ∈ Set.range ((qr_ext e S).orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact (qr_mem_last e S).2 he
    obtain ⟨b0, hb0⟩ := h1
    apply Matrix.det_eq_zero_of_column_eq_zero b0
    intro a
    rw [Matrix.submatrix_apply, hb0]
    have h2 : K.orderEmbOfFin hK a ≠ Fin.last m := fun h3 => hl (h3 ▸ Finset.orderEmbOfFin_mem K hK a)
    obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← ha']
    exact (hb.2.2 a').1
  · have hl : Fin.last m ∈ K := by
      by_contra hl; exact hne ⟨fun h => absurd h hl, fun h => absurd h he⟩
    have h1 : Fin.last m ∈ Set.range (K.orderEmbOfFin hK) := by
      rw [Finset.range_orderEmbOfFin]; exact hl
    obtain ⟨a0, ha0⟩ := h1
    apply Matrix.det_eq_zero_of_row_eq_zero a0
    intro b
    rw [Matrix.submatrix_apply, ha0]
    have h2 : (qr_ext e S).orderEmbOfFin hS b ≠ Fin.last m := fun h3 =>
      he ((qr_mem_last e S).1 (h3 ▸ Finset.orderEmbOfFin_mem _ hS b))
    obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← hb']
    exact (hb.2.2 b').2

end Block

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LWedge
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_U : (N : ℕ) → (Fin N → Finset (Fin n)) → Finset (Fin n)
  | 0, _ => ∅
  | N + 1, D => D 0 ∪ ql_U N (Fin.tail D)

def ql_sW (R : Type*) [CommRing R] : (N : ℕ) → (Fin N → Finset (Fin n)) → R
  | 0, _ => 1
  | N + 1, D => wedgeSign R (D 0) (ql_U N (Fin.tail D)) * ql_sW R N (Fin.tail D)

def wedgeCoeff (R : Type*) [CommRing R] {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) : R :=
  if ql_U N D = L then ql_sW R N D else 0

variable {R : Type*} [CommRing R]

lemma ql_W_succ {N : ℕ} (D : Fin (N + 1) → Finset (Fin n)) (L : Finset (Fin n)) :
    wedgeCoeff R D L = ∑ M, ql_w R (D 0) M L * wedgeCoeff R (Fin.tail D) M := by
  simp only [wedgeCoeff, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, ql_U, ql_sW, ql_w, ite_mul, zero_mul]
  congr

lemma ql_sW_cast : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), ((ql_sW ℤ N D : ℤ) : R) = ql_sW R N D
  | 0, _ => by simp [ql_sW]
  | N + 1, D => by simp only [ql_sW, Int.cast_mul, ql_s_cast, ql_sW_cast N]

lemma ql_W_cast {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) :
    ((wedgeCoeff ℤ D L : ℤ) : R) = wedgeCoeff R D L := by
  unfold wedgeCoeff; split_ifs
  · exact ql_sW_cast N D
  · simp

lemma ql_mem_U : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (a : Fin n), a ∈ ql_U N D ↔ ∃ j, a ∈ D j
  | 0, _, a => by simp [ql_U]
  | N + 1, D, a => by
    rw [ql_U, mem_union, ql_mem_U N, Fin.exists_fin_succ]; rfl

lemma ql_sW_isUnit : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
    IsUnit (ql_sW R N D)
  | 0, _, _ => by simp [ql_sW]
  | N + 1, D, h => by
    rw [ql_sW]
    refine IsUnit.mul (ql_s_isUnit ?_) (ql_sW_isUnit N _ fun i j hij => h _ _ (by simpa using hij))
    rw [Finset.disjoint_left]
    intro a ha hU
    obtain ⟨j, hj⟩ := (ql_mem_U N _ a).1 hU
    exact Finset.disjoint_left.1 (h 0 j.succ (Fin.succ_ne_zero j).symm) ha hj

lemma ql_sum_cons {N : ℕ} (φ : (Fin (N + 1) → Finset (Fin n)) → R) :
    ∑ D, φ D = ∑ a, ∑ D', φ (Fin.cons a D') := by
  rw [← (Fin.consEquiv (fun _ => Finset (Fin n))).sum_comp, Fintype.sum_prod_type]; rfl

lemma ql_prod_sum {N : ℕ} (G : Fin N → Finset (Fin n) → R) :
    ∏ j, ∑ a, G j a = ∑ x : Fin N → Finset (Fin n), ∏ j, G j (x j) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable (g : Matrix (Fin n) (Fin n) R)

theorem ql_W_equiv : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)),
    ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (D j)) * wedgeCoeff R D' L = ∑ L', qs_mn g L L' * wedgeCoeff R D L'
  | 0, D, L => by
    simp [wedgeCoeff, ql_U, ql_sW, ql_mn_empty, eq_comm]
  | N + 1, D, L => by
    rw [ql_sum_cons]
    calc ∑ a, ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g ((Fin.cons a D' : Fin (N + 1) → _) j) (D j)) *
            wedgeCoeff R (Fin.cons a D' : Fin (N + 1) → _) L
        = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L *
            ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (Fin.tail D j)) * wedgeCoeff R D' M := by
          refine sum_congr rfl fun a _ => ?_
          simp only [ql_W_succ (Fin.cons a _), Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
            mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by simp only [Fin.tail]; ring
      _ = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L * ∑ M', qs_mn g M M' * wedgeCoeff R (Fin.tail D) M' := by
          simp only [ql_W_equiv N]
      _ = ∑ M', wedgeCoeff R (Fin.tail D) M' * ∑ a, ∑ M, qs_mn g a (D 0) * qs_mn g M M' * ql_w R a M L := by
          simp only [mul_sum]
          symm
          rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]; exact sum_congr rfl fun M _ => sum_congr rfl fun M' _ => by ring
      _ = ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
          simp only [ql_lapM, ql_W_succ D, mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by ring

def ql_P (R : Type*) [CommRing R] {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n))
    (i : Fin N → Finset (Fin n)) : R :=
  ∑ D : Fin N → Finset (Fin n), (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D L

lemma ql_P_cast {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ((ql_P ℤ k L i : ℤ) : R) = ql_P R k L i := by
  simp only [ql_P, Int.cast_sum, Int.cast_mul, Int.cast_prod, ql_w_cast, ql_W_cast]

theorem ql_P_equiv {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i =
      ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
  calc ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i
      = ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          (∏ j, qs_mn g (k j) (k' j)) * (∏ j, ql_w R (k' j) (D j) (i j)) * ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
        refine sum_congr rfl fun k' _ => ?_
        simp only [ql_P, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          ∏ j, qs_mn g (k j) (k' j) * qs_mn g (D' j) (D j) * ql_w R (k' j) (D j) (i j) := by
        simp only [← ql_W_equiv, mul_sum, prod_mul_distrib]
        symm
        rw [sum_comm]; refine sum_congr rfl fun k' _ => ?_
        rw [sum_comm]; exact sum_congr rfl fun D _ => sum_congr rfl fun D' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∏ j, ∑ a, ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j) := by
        refine sum_congr rfl fun D' _ => ?_
        rw [ql_prod_sum (fun j a => ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j))]
        refine congrArg _ (sum_congr rfl fun k' _ => ?_)
        exact (ql_prod_sum (fun j d => qs_mn g (k j) (k' j) * qs_mn g (D' j) d * ql_w R (k' j) d (i j))).symm
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∑ i' : Fin N → Finset (Fin n), ∏ j, ql_w R (k j) (D' j) (i' j) * qs_mn g (i' j) (i j) := by
        simp only [ql_lapT, ql_prod_sum]
    _ = ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
        simp only [ql_P, mul_sum, sum_mul, prod_mul_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring

lemma ql_P_unit {N : ℕ} (k i : Fin N → Finset (Fin n)) (hk : ∀ j, k j ⊆ i j)
    (hd : ∀ j j', j ≠ j' → Disjoint (i j \ k j) (i j' \ k j')) :
    IsUnit (ql_P R k (ql_U N fun j => i j \ k j) i) := by
  have h0 : ∀ D : Fin N → Finset (Fin n), D ≠ (fun j => i j \ k j) →
      (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D (ql_U N fun j => i j \ k j) = 0 := by
    intro D hD
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hD
    rw [prod_eq_zero (mem_univ j), zero_mul]
    rw [ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hdis
      apply hj
      rw [← h, union_sdiff_cancel_left hdis]
    · rfl
  rw [ql_P, sum_eq_single _ (fun D _ hD => h0 D hD) (fun h => absurd (mem_univ _) h)]
  refine IsUnit.mul ?_ ?_
  · refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_
    rw [ql_w, if_pos (union_sdiff_of_subset (hk j))]
    exact ql_s_isUnit disjoint_sdiff
  · rw [wedgeCoeff, if_pos rfl]
    exact ql_sW_isUnit N _ hd

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

