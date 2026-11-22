import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0008

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LamStrip
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_be (b : ℕ) (L : LamIdx n b) : Fin n → ℤ := ∑ x ∈ L.1, Pi.single x (1 : ℤ)

lemma ql_be_apply (b : ℕ) (L : LamIdx n b) (a : Fin n) : ql_be b L a = if a ∈ L.1 then 1 else 0 := by
  simp [ql_be, Finset.sum_apply, Pi.single_apply]

lemma ql_be_inj (b : ℕ) : Function.Injective (ql_be (n := n) b) := by
  intro L L' h
  apply Subtype.ext
  ext a
  have := congrFun h a
  rw [ql_be_apply, ql_be_apply] at this
  by_cases h1 : a ∈ L.1 <;> by_cases h2 : a ∈ L'.1 <;> simp_all

lemma ql_torus (b : ℕ) (k l : LamIdx n b) :
    evGL (torusPt n) (LamMat n b k l) = if k = l then AddMonoidAlgebra.single (ql_be b k) 1 else 0 := by
  rw [LamMat, qb_evGL_minorC]
  change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
  rw [qb_minor_diagonal, qb_prod_single]
  simp only [Subtype.ext_iff, ql_be]

variable [NeZero n]

def ql_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × LamIdx n b) (TIdx nu) ℤ :=
  fun y I => ql_P ℤ (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext mu y.1)) y.2.1
    (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext nu I))

lemma ql_mem_strVert {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strVert mu b) :
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  simpa only [strVert, mem_filter, Fintype.mem_piFinset, mem_Icc] using h

theorem ql_core (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) {lo : ℤ} {N : ℕ}
    (m1 : lo ≤ mu (lastIdx n)) (m2 : mu 0 ≤ lo + N) (n1 : lo ≤ nu (lastIdx n)) (n2 : nu 0 ≤ lo + N)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 (ql_E lo N (qs_ext nu I)) : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_P ℤ (ql_E lo N (qs_ext mu K)) L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) *
        TMat nu I' I := by
  set d : GLCoord ℤ n := ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) with hd
  set k := ql_E lo N (qs_ext mu K) with hk
  set i := ql_E lo N (qs_ext nu I) with hi
  calc ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 i : ℤ) : GLCoord ℤ n)
      = ∑ K' : TIdx mu, ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (ql_E lo N (qs_ext mu K') j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) (ql_E lo N (qs_ext mu K')) L'.1 i) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun L' _ => ?_
        rw [ql_TMat hmu m1 m2, LamMat, qs_minorC_eq, ql_P_cast]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i) := by
        refine sum_indices_eq_sum_columns hmu m1 m2 (fun k' => ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i)) ?_
        rintro f ⟨j, hj⟩
        refine sum_eq_zero fun L' _ => ?_
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hk, ql_E_card hmu]; exact hj.symm))]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : Finset (Fin n), d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i) := by
        refine sum_congr rfl fun k' _ => ql_sum_L (b := b) (fun L' => d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i)) ?_
        intro L' hL'
        show d * (_ * qs_mn (qs_gC n) L.1 L' * _) = 0
        rw [qs_mn_ne _ (by rw [L.2]; exact hL'.symm)]; ring
    _ = ∑ i' : Fin N → Finset (Fin n), d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j)) := by
        rw [← mul_sum, ← ql_P_equiv]; simp only [mul_sum]
    _ = ∑ I' : TIdx nu, d * (ql_P (GLCoord ℤ n) k L.1 (ql_E lo N (qs_ext nu I')) *
          ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext nu I') j) (i j)) := by
        symm
        refine sum_indices_eq_sum_columns hnu n1 n2 (fun i' => d * (ql_P (GLCoord ℤ n) k L.1 i' *
          ∏ j, qs_mn (qs_gC n) (i' j) (i j))) ?_
        rintro f ⟨j, hj⟩
        show d * (_ * ∏ j, qs_mn (qs_gC n) (f j) (i j)) = 0
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hi, ql_E_card hnu]; exact hj))]; ring
    _ = ∑ I' : TIdx nu, ((ql_P ℤ k L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
        refine sum_congr rfl fun I' _ => ?_
        rw [ql_TMat hnu n1 n2, ql_P_cast]; ring

lemma ql_range {mu nu : Fin n → ℤ} {b : ℕ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    mu (lastIdx n) + ((nu 0 - mu (lastIdx n)).toNat : ℕ) = nu 0 := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have := ((ql_mem_strVert h).1 0).1
  omega

theorem ql_ps_equiv (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) * ((ql_ps b mu nu y I : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_ps b mu nu (K, L) I' : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
  obtain ⟨hb, hnu, -⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  exact ql_core b hmu hnu le_rfl (by rw [hN]; exact (hb 0).1) (hb _).1 hN.ge K L I

theorem ql_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    ∃ k0 : LamIdx n b, ql_be b k0 = nu - mu ∧
      (ql_ps b mu nu (canT mu, k0) (canT nu) = 1 ∨ ql_ps b mu nu (canT mu, k0) (canT nu) = -1) := by
  obtain ⟨hb, hnu, hs⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  set lo := mu (lastIdx n) with hlo
  set N := (nu 0 - lo).toNat with hNdef
  set k := ql_E lo N (qs_ext mu (canT mu)) with hk
  set i := ql_E lo N (qs_ext nu (canT nu)) with hi
  have hmk : ∀ (j : Fin N) a, a ∈ k j ↔ lo + 1 + (j : ℕ) ≤ mu a := fun j a => ql_mem_can hmu _ a
  have hmi : ∀ (j : Fin N) a, a ∈ i j ↔ lo + 1 + (j : ℕ) ≤ nu a := fun j a => ql_mem_can hnu _ a
  have hU : ∀ a, a ∈ ql_U N (fun j => i j \ k j) ↔ mu a < nu a := by
    intro a
    rw [ql_mem_U]
    simp only [mem_sdiff, hmk, hmi]
    constructor
    · rintro ⟨j, h1, h2⟩; omega
    · intro hlt
      have h1 : lo ≤ mu a := hmu (qb_le_lastIdx a)
      have h2 : nu a ≤ nu 0 := hnu (Fin.zero_le a)
      refine ⟨⟨(nu a - lo - 1).toNat, by omega⟩, ?_, ?_⟩
      · show lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ nu a; omega
      · show ¬ lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ mu a; omega
  have hind : ∀ a, (if a ∈ ql_U N (fun j => i j \ k j) then (1 : ℤ) else 0) = nu a - mu a := by
    intro a
    have := hb a
    split_ifs with h1
    · rw [hU] at h1; omega
    · rw [hU] at h1; omega
  have hcard : (ql_U N (fun j => i j \ k j)).card = b := by
    have : ((ql_U N (fun j => i j \ k j)).card : ℤ) = b := by
      rw [← hs, ← sum_congr rfl fun a _ => hind a, Finset.sum_boole, filter_mem_eq_inter, univ_inter]
    exact_mod_cast this
  refine ⟨⟨_, hcard⟩, ?_, ?_⟩
  · funext a
    rw [ql_be_apply, Pi.sub_apply]
    exact hind a
  · refine Int.isUnit_iff.1 (ql_P_unit k i ?_ ?_)
    · intro j a ha
      rw [hmk] at ha; rw [hmi]; exact ha.trans (hb a).1
    · intro j j' hjj
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [mem_sdiff, hmk, hmi] at h1 h2
      have := hb a
      apply hjj; ext; omega

theorem lamStrip_of (hc : CntLam) : LamStrip := by
  intro n _ b
  refine ⟨ql_be b, ql_ps b, ql_be_inj b, ql_torus b, fun mu _ nu h => (ql_mem_strVert h).2.1, ?_,
    fun mu hmu nu h => ql_lead b hmu h, fun mu hmu => hc n mu b hmu⟩
  intro mu hmu nu h
  ext ⟨K, L⟩ I
  exact ql_ps_equiv b hmu h K L I

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SymStrip
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

open Classical in

def qs_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D mu nu) → Fin n,
    if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0)
    else 0

open Classical in

def qs_mid (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D mu nu), ((qs_sg (qs_ext mu J c.1) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0),
            qs_mn (qs_gC n) (qs_add (qs_D mu nu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0

open Classical in
theorem qs_ps_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_mid b mu nu J α K := by
  have hT : ∀ I, TMat mu J I = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ le_rfl (hs.1 0) J I
  have hm : ∀ m : ↥(qs_D mu nu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0), qs_mn (qs_gC n) (qs_ext mu J c) (qs_rem (qs_D mu nu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D mu nu), qs_gC n (a c) (m c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gC n) b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymMat n b α β *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_rem_card hmu hnu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gC n) (qs_card_D hmu hnu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D mu nu) → Fin n, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_ps, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core (qs_gC n) _ _ (qs_D_sub mu nu)]
  · simp only [if_neg h, Finset.sum_const_zero]

open Classical in
theorem qs_ps_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_mid b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ (hs.1 _) le_rfl K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D mu nu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((E c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D mu nu) → Fin n,
        if (∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_add (qs_D mu nu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_ps, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D mu nu) (qs_ext mu J) (qs_ext nu K') a
    by_cases h : (∀ c : ↥(qs_D mu nu), a c ∈ qs_ext nu K' c.1) ∧ qs_ext mu J = qs_rem (qs_D mu nu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.1 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_add_card hmu hnu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    have h3 : ∀ c : ↥(qs_D mu nu), (qs_add (qs_D mu nu) (qs_ext mu J) a c.1).erase (a c) = qs_ext mu J c.1 := by
      intro c; rw [qs_add_mem, Finset.erase_insert (h c)]
    simp only [h3]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp

theorem qs_ps_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b) :
    qs_ps b mu nu (canT mu, qs_mon (qs_card_D hmu hnu hs) (qs_mc mu nu)) (canT nu) = 1 := by
  rw [qs_ps, Finset.sum_eq_single (qs_mc mu nu)]
  · rw [if_pos ((qs_can_iff hmu hnu hs _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu, (qs_mem_D hmu hnu c.1).1 c.2]
    have hlt : colH mu c.1 < n := (qs_mc mu nu c).2
    show qs_sg ((qs_ini (colH mu c.1 + 1)).erase ⟨colH mu c.1, hlt⟩) ⟨colH mu c.1, hlt⟩ = 1
    rw [qs_ini_erase, qs_sg_ini]
  · intro m _ hm
    rw [if_neg (fun h => hm ((qs_can_iff hmu hnu hs _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero n] in
lemma qs_gC_torus : (qs_gC n).map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (1 : ℤ)) (1 : ℤ) := by
  ext a b
  simp only [Matrix.map_apply, qs_gC, Matrix.of_apply, qb_evGL_algebraMap, genMat, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X]
  rfl

omit [NeZero n] in
lemma qs_prod_torus (ε : ℤ) (f : Fin n → ℕ) :
    ∏ x, (AddMonoidAlgebra.single (Pi.single x ε : Fin n → ℤ) (1 : ℤ)) ^ (f x) =
      AddMonoidAlgebra.single (fun x => ε * (f x : ℤ)) 1 := by
  simp_rw [AddMonoidAlgebra.single_pow, one_pow]
  rw [qb_prod_single]
  congr 1
  funext y
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

omit [NeZero n] in
open Classical in
lemma qs_mem_strUp {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := (Finset.mem_filter.1 h).2

theorem symStrip_of : CntSym → SymStrip := by
  intro hc n _ b
  refine ⟨fun α x => ((α.1 x : ℕ) : ℤ), qs_ps b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by have := congrFun h x; simp only at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymMat_eq, qs_SM_map, qs_gC_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_up hmu (qs_mem_strUp hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    ext ⟨J, α⟩ K
    exact (qs_ps_left b hmu hnu' hs J α K).trans (qs_ps_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    refine ⟨qs_mon (qs_card_D hmu hnu' hs) (qs_mc mu nu), ?_, Or.inl (qs_ps_lead b hmu hnu' hs)⟩
    funext x
    exact qs_cnt_mc hmu hnu' hs x
  · intro mu hmu
    exact hc n mu b hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

