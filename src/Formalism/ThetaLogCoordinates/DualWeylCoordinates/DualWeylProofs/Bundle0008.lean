import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0006
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0004

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHStrip
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma qs_dom_up {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hs : HStrip lam kap b) : Dominant kap := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hy : y.1 - 1 < n := by have := y.2; omega
    have h1 : (⟨y.1 - 1, hy⟩ : Fin n).1 + 1 < n := by
      have := y.2; have := Fin.lt_def.1 hlt; simp only; omega
    have h2 := hs.2.1 ⟨y.1 - 1, hy⟩ h1
    have h3 : (⟨(⟨y.1 - 1, hy⟩ : Fin n).1 + 1, h1⟩ : Fin n) = y := by
      apply Fin.ext; have := Fin.lt_def.1 hlt; simp only; omega
    rw [h3] at h2
    have h4 : lam ⟨y.1 - 1, hy⟩ ≤ lam x := hl (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact h2.trans (h4.trans (hs.1 x))

omit [NeZero n] in
lemma qs_dom_down {lam kap : Fin n → ℤ} {b : ℕ} (hk : Dominant kap) (hs : HStrip lam kap b) : Dominant lam := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have h1 : x.1 + 1 < n := by have := y.2; have := Fin.lt_def.1 hlt; omega
    have h2 := hs.2.1 x h1
    have h4 : kap y ≤ kap ⟨x.1 + 1, h1⟩ := hk (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact (hs.1 y).trans (h4.trans h2)

lemma qs_colH_strip {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (c : ℤ) : colH kap c = colH lam c ∨ colH kap c = colH lam c + 1 := by
  have h1 : colH lam c ≤ colH kap c := by
    by_contra hcon
    have hlt : colH kap c < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le lam c)
    have h2 := (qb_lt_colH_iff hl c ⟨colH kap c, hlt⟩).1 (not_le.1 hcon)
    have h3 := (qb_lt_colH_iff hk c ⟨colH kap c, hlt⟩).2 (h2.trans (hs.1 _))
    exact lt_irrefl _ h3
  have h2 : colH kap c ≤ colH lam c + 1 := by
    by_contra hcon
    have hlt : colH lam c + 1 < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le kap c)
    have h2 := (qb_lt_colH_iff hk c ⟨colH lam c + 1, hlt⟩).1 (not_le.1 hcon)
    have h3 := hs.2.1 ⟨colH lam c, by omega⟩ hlt
    have h4 := (qb_lt_colH_iff hl c ⟨colH lam c, by omega⟩).2 (h2.trans h3)
    exact lt_irrefl _ h4
  omega

def qs_D (lam kap : Fin n → ℤ) : Finset ℤ :=
  (Finset.Ioc (lam (lastIdx n)) (kap 0)).filter fun c => colH kap c = colH lam c + 1

lemma qs_D_sub (lam kap : Fin n → ℤ) : qs_D lam kap ⊆ Finset.Ioc (lam (lastIdx n)) (kap 0) := Finset.filter_subset _ _

lemma qs_mem_D {lam kap : Fin n → ℤ} (hl : Dominant lam) (hk : Dominant kap) (c : ℤ) :
    c ∈ qs_D lam kap ↔ colH kap c = colH lam c + 1 := by
  simp only [qs_D, mem_filter, mem_Ioc, and_iff_right_iff_imp]
  intro h
  constructor
  · by_contra hcon
    have := qs_colH_low hl (not_lt.1 hcon)
    have := colH_le kap c
    omega
  · by_contra hcon
    have := qs_colH_high hk (not_le.1 hcon)
    omega

def qs_mc (lam kap : Fin n → ℤ) : ↥(qs_D lam kap) → Fin n := fun c =>
  ⟨colH lam c.1, by have := (Finset.mem_filter.1 c.2).2; have := colH_le kap c.1; omega⟩

lemma qs_cnt_mc {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (x : Fin n) : ((qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = kap x - lam x := by
  have h1 : (univ.filter fun c : ↥(qs_D lam kap) => qs_mc lam kap c = x).map (Function.Embedding.subtype _) =
      Finset.Ioc (lam x) (kap x) := by
    ext c
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
      exists_and_right, exists_eq_right, mem_Ioc]
    have e1 := qb_lt_colH_iff hl c x
    have e2 := qb_lt_colH_iff hk c x
    constructor
    · rintro ⟨hc, hx⟩
      have h3 := (qs_mem_D hl hk c).1 hc
      have h4 : colH lam c = x.1 := congrArg Fin.val hx
      constructor
      · by_contra hcon; have := e1.2 (not_lt.1 hcon); omega
      · exact e2.1 (by omega)
    · rintro ⟨h3, h4⟩
      have h5 := e2.2 h4
      have h6 : ¬ x.1 < colH lam c := fun h => absurd (e1.1 h) (not_le.2 h3)
      have h7 := qs_colH_strip hl hk hs c
      exact ⟨(qs_mem_D hl hk c).2 (by omega), Fin.ext (by simp only [qs_mc]; omega)⟩
  rw [qs_cnt, ← Finset.card_map (Function.Embedding.subtype _), h1, Int.card_Ioc,
    Int.toNat_of_nonneg (by have := hs.1 x; omega)]

lemma qs_card_D {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b) :
    Fintype.card ↥(qs_D lam kap) = b := by
  have h1 := qs_sum_cnt (qs_mc lam kap)
  have h2 : ((∑ x, qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = (b : ℤ) := by
    rw [← hs.2.2]; push_cast
    exact Finset.sum_congr rfl fun x _ => qs_cnt_mc hl hk hs x
  rw [h1] at h2
  exact_mod_cast h2

omit [NeZero n] in
lemma qs_sg_ini (h : ℕ) (hh : h < n) : qs_sg (qs_ini h) (⟨h, hh⟩ : Fin n) = 1 := by
  have : (qs_ini h : Finset (Fin n)).filter ((⟨h, hh⟩ : Fin n) < ·) = ∅ := by
    ext x; simp only [qs_ini, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and, not_lt]
    intro hx; exact Fin.le_def.2 (by simp only; omega)
  rw [qs_sg, this]; simp

omit [NeZero n] in
lemma qs_ini_erase (h : ℕ) (hh : h < n) : (qs_ini (h + 1) : Finset (Fin n)).erase ⟨h, hh⟩ = qs_ini h := by
  ext x
  simp only [qs_ini, mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega

lemma qs_can_iff {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (m : ↥(qs_D lam kap) → Fin n) :
    ((∀ c : ↥(qs_D lam kap), m c ∈ qs_ext kap (canT kap) c.1) ∧
      qs_ext lam (canT lam) = qs_rem (qs_D lam kap) (qs_ext kap (canT kap)) m) ↔ m = qs_mc lam kap := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    have h3 := h1 c
    have h4 := congrFun h2 c.1
    have h5 := (qs_mem_D hl hk c.1).1 c.2
    rw [qs_rem_mem, qs_ext_can hl, qs_ext_can hk] at h4
    rw [qs_ext_can hk] at h3
    have h6 : m c ∉ (qs_ini (colH lam c.1) : Finset (Fin n)) := by rw [h4]; simp
    simp only [qs_ini, mem_filter, mem_univ, true_and] at h3 h6
    exact Fin.ext (by simp only [qs_mc]; omega)
  · rintro rfl
    refine ⟨fun c => ?_, ?_⟩
    · have h5 := (qs_mem_D hl hk c.1).1 c.2
      rw [qs_ext_can hk]
      simp only [qs_ini, qs_mc, mem_filter, mem_univ, true_and]; omega
    · funext c
      by_cases hc : c ∈ qs_D lam kap
      · have h5 := (qs_mem_D hl hk c).1 hc
        have h6 := qs_rem_mem (qs_D lam kap) (qs_ext kap (canT kap)) (qs_mc lam kap) ⟨c, hc⟩
        simp only at h6
        rw [h6, qs_ext_can hl, qs_ext_can hk, h5]
        exact (qs_ini_erase _ _).symm
      · rw [qs_rem_not _ _ _ hc, qs_ext_can hl, qs_ext_can hk]
        have h7 := qs_colH_strip hl hk hs c
        have h8 := (qs_mem_D hl hk c).not.1 hc
        congr 1; omega

lemma qs_rem_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (K : ℤ → Finset (Fin n)) (hK : ∀ c, (K c).card = colH kap c) (m : ↥(qs_D lam kap) → Fin n)
    (hm : ∀ c : ↥(qs_D lam kap), m c ∈ K c.1) (c : ℤ) : (qs_rem (qs_D lam kap) K m c).card = colH lam c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_rem_mem (qs_D lam kap) K m ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_erase_of_mem (hm ⟨c, hc⟩), hK, h5]; rfl
  · rw [qs_rem_not _ _ _ hc, hK]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

lemma qs_add_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (J : ℤ → Finset (Fin n)) (hJ : ∀ c, (J c).card = colH lam c) (a : ↥(qs_D lam kap) → Fin n)
    (ha : ∀ c : ↥(qs_D lam kap), a c ∉ J c.1) (c : ℤ) : (qs_add (qs_D lam kap) J a c).card = colH kap c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_add_mem (qs_D lam kap) J a ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_insert_of_notMem (ha ⟨c, hc⟩), hJ, h5]
  · rw [qs_add_not _ _ _ hc, hJ]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SumIndicesEqSumColumns
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_E (lo : ℤ) (N : ℕ) (F : ℤ → Finset (Fin n)) : Fin N → Finset (Fin n) := fun j => F (lo + 1 + (j : ℕ))

lemma ql_prod_Ioc {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by
  symm
  refine Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_
  · intro j _; have := j.2; simp only [mem_Ioc]; omega
  · intro i _ j _ h; ext; omega
  · intro c hc
    simp only [mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩
  · intro j _; rfl

def ql_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : lo < c ∧ c ≤ lo + N then f ⟨(c - lo - 1).toNat, by omega⟩ else if c ≤ lo then univ else ∅

lemma ql_E_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by
  funext j
  have := j.2
  simp only [ql_E, ql_fill]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  show (lo + 1 + (j : ℕ) - lo - 1).toNat = j
  omega

lemma ql_sum_L {M : Type*} [AddCommMonoid M] {b : ℕ} (φ : Finset (Fin n) → M) (hφ : ∀ L, L.card ≠ b → φ L = 0) :
    ∑ L : LamIdx n b, φ L.1 = ∑ L, φ L := by
  refine Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro L hL
  exact hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩

variable [NeZero n]

lemma ql_fill_card {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by
  unfold ql_fill
  split_ifs with h h'
  · rw [hf]; congr 1
    show lo + 1 + ((c - lo - 1).toNat : ℤ) = c
    omega
  · rw [qs_colH_low hmu (h'.trans h1)]; simp
  · rw [qs_colH_high hmu (by omega)]; simp

lemma ql_E_card {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := qs_ext_card hmu I _

lemma sum_indices_eq_sum_columns {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by
  refine Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)
  · intro I I' h
    funext c
    apply Subtype.ext
    rw [← qs_ext_mem, ← qs_ext_mem]
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have := congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩
    have e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1 := by omega
    simp only [ql_E, e] at this
    exact this
  · intro f hf
    apply hφ
    by_contra hc
    push Not at hc
    exact hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by
      simp only [qs_ext_res hmu, ql_E_fill]⟩

lemma ql_TMat {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by
  rw [qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]; rfl

lemma ql_mem_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by
  rw [qs_ext_can hmu, ← qb_lt_colH_iff hmu]; simp [qs_ini]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

