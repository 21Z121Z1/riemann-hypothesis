import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.NormalisedValue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem val_pi_lt_one (h : LF O ϖ nrm q) : ValuativeRel.valuation F ϖ < 1 := by
  exact (h.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩

theorem val_pi_pos (h : LF O ϖ nrm q) : 0 < ValuativeRel.valuation F ϖ := by
  first
    | exact (Valuation.pos_iff _).2 h.ne
    | exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h.ne)

theorem mem_iff_val_le (h : LF O ϖ nrm q) (x : F) : x ∈ O ↔ ValuativeRel.valuation F x ≤ 1 := by
  rw [h.O_eq]
  exact Valuation.mem_integer_iff _ _

theorem one_lt_q (h : LF O ϖ nrm q) : 1 < q := by
  have hq0 : q ≠ 0 := by
    intro hq
    have hp := h.nrm_pi
    rw [hq, Nat.cast_zero, _root_.inv_zero] at hp
    exact h.ne ((AbsoluteValue.eq_zero nrm).1 hp)
  have hq1 : q ≠ 1 := by
    intro hq
    have hc := h.card
    rw [hq] at hc
    have hs := (Nat.card_eq_one_iff_unique.1 hc.symm).1
    exact not_subsingleton (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) hs
  omega

private theorem isUnit_iff_valuation_eq_one' (y : 𝒪[F]) : IsUnit y ↔ ValuativeRel.valuation F (y : F) = 1 := by
  first
    | exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one
    | simpa using (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one (x := y)

theorem irreducible_pi (h : LF O ϖ nrm q) :
    Irreducible (⟨ϖ, (Valuation.mem_integer_iff _ _).2 (val_pi_lt_one h).le⟩ : 𝒪[F]) := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_valuation_eq_one']
    exact (val_pi_lt_one h).ne
  · intro a b hab
    by_cases ha : ValuativeRel.valuation F (a : F) = 1
    · left
      exact (isUnit_iff_valuation_eq_one' a).2 ha
    · right
      have ha1 : ValuativeRel.valuation F (a : F) < 1 :=
        lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 a.2) ha
      obtain ⟨o, hoO, hao⟩ := (h.lt_one a).1 ha1
      have hab' : (ϖ : F) = (a : F) * (b : F) := congrArg Subtype.val hab
      have hoI : o ∈ 𝒪[F] := by
        rw [← h.O_eq]
        exact hoO
      have hob : (⟨o, hoI⟩ : 𝒪[F]) * b = 1 := by
        apply Subtype.ext
        show o * (b : F) = 1
        have hh : ϖ * 1 = ϖ * (o * (b : F)) := by
          rw [mul_one, ← mul_assoc, ← hao, ← hab']
        exact (mul_left_cancel₀ h.ne hh).symm
      exact ⟨⟨b, ⟨o, hoI⟩, (mul_comm _ _).trans hob, hob⟩, rfl⟩

theorem val_eq_pow_of_int (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0)
    (hxO : ValuativeRel.valuation F x ≤ 1) :
    ∃ n : ℕ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ n := by
  have hxI : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hxO
  have hx' : (⟨x, hxI⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    exact hx (congrArg Subtype.val h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' (irreducible_pi h)
  refine ⟨n, ?_⟩
  have hv := congrArg (fun y : 𝒪[F] => ValuativeRel.valuation F (y : F)) hu
  have hu1 : ValuativeRel.valuation F ((u : 𝒪[F]) : F) = 1 := (isUnit_iff_valuation_eq_one' _).1 u.isUnit
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul] at hv
  exact hv

theorem val_eq_zpow (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0) :
    ∃ e : ℤ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e := by
  by_cases hle : ValuativeRel.valuation F x ≤ 1
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h hx hle
    exact ⟨n, by rw [hn, _root_.zpow_natCast]⟩
  · have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hle
    have hinv : ValuativeRel.valuation F x⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hx).1 hlt).le
    obtain ⟨n, hn⟩ := val_eq_pow_of_int h (inv_ne_zero hx) hinv
    refine ⟨-(n : ℤ), ?_⟩
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← hn, map_inv₀, _root_.inv_inv]

theorem val_mul_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    ValuativeRel.valuation F (x * ϖ ^ (-e)) = 1 := by
  rw [map_mul, map_zpow₀, he, ← zpow_add₀ (val_pi_pos h).ne']
  simp

theorem nrm_eq_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    nrm x = (q : ℝ) ^ (-e) := by
  have h1 : nrm (x * ϖ ^ (-e)) = 1 := h.nrm_unit _ (val_mul_zpow h he)
  have hdecomp : x = x * ϖ ^ (-e) * ϖ ^ e := by
    rw [mul_assoc, ← zpow_add₀ h.ne, neg_add_cancel, _root_.zpow_zero, mul_one]
  have hz : nrm (ϖ ^ e) = nrm ϖ ^ e := by
    first
      | exact map_zpow₀ nrm ϖ e
      | exact map_zpow₀ nrm.toMonoidWithZeroHom ϖ e
  conv_lhs => rw [hdecomp]
  rw [map_mul, h1, one_mul, hz, h.nrm_pi, _root_.inv_zpow']

private theorem nrm_le_one_of_valuation_le_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x ≤ 1) :
    nrm x ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h h0 hx
    rw [nrm_eq_zpow h (e := (n : ℤ)) (by rw [hn, _root_.zpow_natCast]), _root_.zpow_neg, _root_.zpow_natCast]
    have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (one_lt_q h).le
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq)

private theorem nrm_le_inv_q_of_valuation_lt_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x < 1) :
    nrm x ≤ (q : ℝ)⁻¹ := by
  obtain ⟨o, hoO, rfl⟩ := (h.lt_one x).1 hx
  rw [map_mul, h.nrm_pi]
  have ho : nrm o ≤ 1 := nrm_le_one_of_valuation_le_one h o ((mem_iff_val_le h o).1 hoO)
  have hq : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  calc (q : ℝ)⁻¹ * nrm o ≤ (q : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left ho hq
    _ = (q : ℝ)⁻¹ := mul_one _

theorem nrm_le_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1 := by
  constructor
  · intro hn
    by_contra hv
    have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hv
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hlt
    have hi : ValuativeRel.valuation F x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx).1 hlt
    have h2 : nrm x⁻¹ ≤ (q : ℝ)⁻¹ := nrm_le_inv_q_of_valuation_lt_one h _ hi
    have hq : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h)
    rw [map_inv₀] at h2
    have hpos : 0 < nrm x := nrm.pos hx
    have h3 : (nrm x)⁻¹ < 1 := lt_of_le_of_lt h2 hq
    have h4 : 1 < nrm x := (inv_lt_one₀ hpos).1 h3
    linarith
  · exact nrm_le_one_of_valuation_le_one h x

theorem nrm_lt_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x < 1 ↔ ValuativeRel.valuation F x < 1 := by
  constructor
  · intro hn
    by_contra hv
    have h1 : 1 ≤ ValuativeRel.valuation F x := not_lt.1 hv
    rcases h1.lt_or_eq with hlt | heq
    · exact absurd ((nrm_le_one_iff h x).1 hn.le) (not_le.2 hlt)
    · have hu := h.nrm_unit x heq.symm
      linarith
  · intro hv
    exact lt_of_le_of_lt (nrm_le_inv_q_of_valuation_lt_one h x hv) (inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h))

theorem nrm_le_of_val_le (h : LF O ϖ nrm q) {x y : F}
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : nrm x ≤ nrm y := by
  by_cases hy : y = 0
  · have hv0 : ValuativeRel.valuation F x = 0 := by
      rw [hy, map_zero] at hxy
      exact le_antisymm hxy zero_le
    have hx : x = 0 := (Valuation.zero_iff _).1 hv0
    simp [hx]
  · have hyv : ValuativeRel.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have hq : ValuativeRel.valuation F (x * y⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      calc ValuativeRel.valuation F x * (ValuativeRel.valuation F y)⁻¹
          ≤ ValuativeRel.valuation F y * (ValuativeRel.valuation F y)⁻¹ := by gcongr
        _ = 1 := _root_.mul_inv_cancel₀ hyv
    have h1 := (nrm_le_one_iff h _).2 hq
    rw [map_mul, map_inv₀] at h1
    have hpos : 0 < nrm y := nrm.pos hy
    calc nrm x = nrm x * (nrm y)⁻¹ * nrm y := (_root_.inv_mul_cancel_right₀ hpos.ne' _).symm
      _ ≤ 1 * nrm y := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = nrm y := one_mul _

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  intro F _ _ _ _ O ϖ nrm q h
  refine ⟨one_lt_q h, (mem_iff_val_le h ϖ).2 (val_pi_lt_one h).le,
    fun x => (nrm_le_one_iff h x).trans (mem_iff_val_le h x).symm,
    fun x => (nrm_lt_one_iff h x).trans (h.lt_one x), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he⟩ := val_eq_zpow h hx
    exact ⟨e, nrm_eq_zpow h he, h.nrm_unit _ (val_mul_zpow h he)⟩
  · intro x y
    rcases le_total (ValuativeRel.valuation F x) (ValuativeRel.valuation F y) with hxy | hxy
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F y :=
        le_trans (Valuation.map_add _ x y) (max_le hxy le_rfl)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_right _ _)
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F x :=
        le_trans (Valuation.map_add _ x y) (max_le le_rfl hxy)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_left _ _)
  · intro x
    constructor
    · intro hn
      have h1 := (nrm_le_one_iff h x).1 hn.le
      have h2 : ¬ ValuativeRel.valuation F x < 1 := fun hlt => by
        have := (nrm_lt_one_iff h x).2 hlt
        linarith
      exact le_antisymm h1 (not_lt.1 h2)
    · exact h.nrm_unit x

end GlobalTheory.CompanionTheory.QL.NormalisedValue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicElementBlocks
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLB

section Alg

variable {F : Type} [Field F]

theorem pEl_coe {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F)) := rfl

section Blocks

variable {r d c : ℕ} (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin c) F)
  (C : Matrix (Fin d) (Fin r) F) (D : Matrix (Fin d) (Fin c) F)

theorem bAA_reindex : bAA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = A := by
  ext i j; simp [bAA]

theorem bAD_reindex : bAD (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = B := by
  ext i j; simp [bAD]

theorem bDA_reindex : bDA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = C := by
  ext i j; simp [bDA]

theorem bDD_reindex : bDD (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = D := by
  ext i j; simp [bDD]

end Blocks

theorem pEl_det {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (m₁ : Matrix (Fin r) (Fin r) F).det * (m₂ : Matrix (Fin c) (Fin c) F).det := by
  rw [pEl_coe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Alg

end GlobalTheory.CompanionTheory.QLB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParahoricSubgroupCompactOpenMeasure
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Par

section Alg

variable {F : Type} [Field F]

def piIdeal (O : Subring F) (ϖ : F) : Ideal O where
  carrier := {x | ∃ o ∈ O, (x : F) = ϖ * o}
  add_mem' := by
    rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
    exact ⟨x + y, O.add_mem hx hy, by simp [hax, hby, mul_add]⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨x, hx, hax⟩
    refine ⟨c * x, O.mul_mem c.2 hx, ?_⟩
    simp only [smul_eq_mul, Subring.coe_mul, hax]
    ring

def liftO {n : ℕ} (O : Subring F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) O := fun i j => ⟨Z i j, h i j⟩

theorem liftO_mul {n : ℕ} (O : Subring F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    liftO O (x * y) hxy = liftO O x hx * liftO O y hy := by
  ext i j
  simp [liftO, Matrix.mul_apply]

theorem liftO_one {n : ℕ} (O : Subring F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    liftO O 1 h = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [liftO, hij, Matrix.one_apply]

def red {n : ℕ} (O : Subring F) (ϖ : F) (Z : Matrix (Fin n) (Fin n) F) (h : IsInt O Z) :
    Matrix (Fin n) (Fin n) (O ⧸ piIdeal O ϖ) :=
  (liftO O Z h).map (Ideal.Quotient.mk (piIdeal O ϖ))

theorem red_mul {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (hx : IsInt O x)
    (hy : IsInt O y) (hxy : IsInt O (x * y)) :
    red O ϖ (x * y) hxy = red O ϖ x hx * red O ϖ y hy := by
  rw [red, liftO_mul O hx hy hxy, Matrix.map_mul]
  rfl

theorem red_one {n : ℕ} (O : Subring F) (ϖ : F) (h : IsInt O (1 : Matrix (Fin n) (Fin n) F)) :
    red O ϖ 1 h = 1 := by
  rw [red, liftO_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem red_congr {n : ℕ} (O : Subring F) (ϖ : F) {x y : Matrix (Fin n) (Fin n) F} (e : x = y)
    (hx : IsInt O x) (hy : IsInt O y) : red O ϖ x hx = red O ϖ y hy := by
  subst e
  rfl

def blk (r c : ℕ) (i : Fin (r + c)) : ℕ := if (i : ℕ) < r then 0 else 1

theorem bDA_iff {r c : ℕ} (O : Subring F) (ϖ : F) {Z : Matrix (Fin (r + c)) (Fin (r + c)) F}
    (h : IsInt O Z) : bDA Z ∈ IIset O ϖ ↔ (red O ϖ Z h).BlockTriangular (blk r c) := by
  constructor
  · intro hZ i j hij
    have hji : (j : ℕ) < r ∧ r ≤ (i : ℕ) := by
      unfold blk at hij
      split_ifs at hij <;> omega
    obtain ⟨hj, hi'⟩ := hji
    obtain ⟨i', rfl⟩ : ∃ i' : Fin c, i = Fin.natAdd r i' :=
      ⟨⟨(i : ℕ) - r, by omega⟩, by ext; simp; omega⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd c j' := ⟨⟨j, hj⟩, by ext; simp⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hZ i' j')
  · intro hZ i j
    have hlt : blk r c (Fin.castAdd c j) < blk r c (Fin.natAdd r i) := by
      simp [blk]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hZ hlt)

theorem parJ_mul {O : Subring F} {ϖ : F} {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  have hm : k * k' ∈ GLint O (r + c) := mul_mem hk.1 hk'.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  rw [red_congr O ϖ (Units.val_mul k k') hm.1 (isInt_mul' O hk.1.1 hk'.1.1),
    red_mul O ϖ hk.1.1 hk'.1.1]
  exact ((bDA_iff O ϖ hk.1.1).mp hk.2).mul ((bDA_iff O ϖ hk'.1.1).mp hk'.2)

theorem parJ_inv {O : Subring F} {ϖ : F} {r c : ℕ} {k : GL (Fin (r + c)) F}
    (hk : k ∈ parJ O ϖ r c) : k⁻¹ ∈ parJ O ϖ r c := by
  have hm : k⁻¹ ∈ GLint O (r + c) := inv_mem hk.1
  refine ⟨hm, ?_⟩
  rw [bDA_iff O ϖ hm.1]
  have h1 : IsInt O ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) :=
    isInt_mul' O hk.1.1 hm.1
  have e1 : (k : Matrix (Fin (r + c)) (Fin (r + c)) F) *
      ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1 * red O ϖ _ hm.1 = 1 := by
    rw [← red_mul O ϖ hk.1.1 hm.1 h1, red_congr O ϖ e1 h1 (e1 ▸ h1)]
    exact red_one O ϖ _
  have hinv : (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1)⁻¹ = red O ϖ _ hm.1 :=
    Matrix.inv_eq_right_inv hN
  letI : Invertible (red O ϖ (k : Matrix (Fin (r + c)) (Fin (r + c)) F) hk.1.1) :=
    ⟨_, mul_eq_one_comm.mp hN, hN⟩
  rw [← hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular ((bDA_iff O ϖ hk.1.1).mp hk.2)

theorem one_mem_parJ {O : Subring F} {ϖ : F} {r c : ℕ} : (1 : GL (Fin (r + c)) F) ∈ parJ O ϖ r c := by
  refine ⟨one_mem _, fun i j => ⟨0, O.zero_mem, ?_⟩⟩
  have : Fin.natAdd r i ≠ Fin.castAdd c j := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [bDA, Matrix.one_apply, this]

def parSub (O : Subring F) (ϖ : F) (r c : ℕ) : Subgroup (GL (Fin (r + c)) F) where
  carrier := parJ O ϖ r c
  mul_mem' := parJ_mul
  one_mem' := one_mem_parJ
  inv_mem' := parJ_inv

end Alg

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem isOpen_O (h : LF O ϖ nrm q) : IsOpen (O : Set F) := by
  rw [h.O_eq]
  exact Valuation.isOpen_integer

theorem isCompact_O (h : LF O ϖ nrm q) : IsCompact (O : Set F) := by
  rw [h.O_eq]
  exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

theorem isOpen_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsOpen (GLint O n : Set (GL (Fin n) F)) := by
  have hv : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hw : ∀ a b : Fin n, Continuous fun g : GL (Fin n) F =>
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b :=
    fun a b => (hv a b).comp continuous_inv
  have e : (GLint O n : Set (GL (Fin n) F)) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) ∩
      (⋂ a, ⋂ b, (fun g : GL (Fin n) F =>
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b) ⁻¹' (O : Set F)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hv a b)).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_O h).preimage (hw a b))

theorem isCompact_int (h : LF O ϖ nrm q) (n : ℕ) :
    IsCompact {m : Matrix (Fin n) (Fin n) F | IsInt O m} := by
  have e : {m : Matrix (Fin n) (Fin n) F | IsInt O m} =
      Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => (O : Set F))) := by
    ext m
    exact ⟨fun hm a _ b _ => hm a b, fun hm a b => hm a trivial b trivial⟩
  rw [e]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => isCompact_O h))

theorem isCompact_GLint (h : LF O ϖ nrm q) (n : ℕ) : IsCompact (GLint O n : Set (GL (Fin n) F)) := by
  haveI : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hc := isCompact_int h n
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    (hc.prod (hc.image MulOpposite.continuous_op))
  refine h2.of_isClosed_subset ((GLint O n).isClosed_of_isOpen (isOpen_GLint h n)) ?_
  intro x hx
  exact ⟨hx.1, _, hx.2, rfl⟩

theorem isOpen_parJ (h : LF O ϖ nrm q) (r c : ℕ) : IsOpen (parJ O ϖ r c) := by
  have hP : IsOpen {x : F | ∃ o ∈ O, x = ϖ * o} := by
    have e : {x : F | ∃ o ∈ O, x = ϖ * o} = (fun x => ϖ⁻¹ * x) ⁻¹' (O : Set F) := by
      ext x
      constructor
      · rintro ⟨o, ho, rfl⟩
        simpa [h.ne] using ho
      · intro hx
        exact ⟨_, hx, by simp [h.ne]⟩
    rw [e]
    exact (isOpen_O h).preimage (continuous_const.mul continuous_id)
  have e : parJ O ϖ r c = (GLint O (r + c) : Set (GL (Fin (r + c)) F)) ∩
      ⋂ i : Fin c, ⋂ j : Fin r, (fun g : GL (Fin (r + c)) F =>
        (g : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
          {x : F | ∃ o ∈ O, x = ϖ * o} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [e]
  exact (isOpen_GLint h _).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hP.preimage (Units.continuous_val.matrix_elem _ _))

theorem parJ_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ r c : ℕ, ∃ J : Subgroup (GL (Fin (r + c)) F),
      (J : Set (GL (Fin (r + c)) F)) = parJ O ϖ r c ∧ IsOpen (parJ O ϖ r c) ∧
      IsCompact (parJ O ϖ r c) ∧ ∃ μ : Measure (GL (Fin (r + c)) F), μ.IsMulLeftInvariant ∧
        μ (parJ O ϖ r c) = 1 := by
  intro F _ _ _ _ O ϖ nrm q h r c
  have ho : IsOpen (parJ O ϖ r c) := isOpen_parJ h r c
  have hc : IsCompact (parJ O ϖ r c) :=
    (isCompact_GLint h (r + c)).of_isClosed_subset
      ((parSub O ϖ r c).isClosed_of_isOpen ho) fun k hk => hk.1
  refine ⟨parSub O ϖ r c, rfl, ho, hc, ?_⟩
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin (r + c)) F) :=
    ⟨⟨parJ O ϖ r c, hc⟩, ⟨1, by
      rw [ho.interior_eq]
      exact one_mem_parJ⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

end Top

end GlobalTheory.CompanionTheory.QL.Par
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminantStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | exact GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TraceIdempotentNotDivisibleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_idempotent_not_divisible : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B) (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m → x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} → ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  first | exact @GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | exact GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | (intros; apply GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentativeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
end

