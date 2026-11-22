import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvections
section
open scoped Matrix

namespace GlobalTheory.UTrans.TvKill

open GlobalTheory.UTrans GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

def rk (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun a b => x a * ∑ e, G b e * σ (y e)

theorem rk_mulVec (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by
  funext a
  simp only [rk, Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem exists_dual (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0) : ∃ y, hf σ G x y = 1 := by
  have h1 : Matrix.vecMul x G ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hG.det_ne h)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h1
  refine ⟨Pi.single b (σ (Matrix.vecMul x G b)⁻¹), ?_⟩
  have : hf σ G x (Pi.single b (σ (Matrix.vecMul x G b)⁻¹)) =
      Matrix.vecMul x G b * (Matrix.vecMul x G b)⁻¹ := by
    simp only [hf, Pi.single_apply, apply_ite σ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hG.invol, ← Finset.sum_mul]
    rfl
  rw [this, mul_inv_cancel₀ hb]

theorem exists_dual_iso [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ y, hf σ G x y = 1 ∧ hf σ G y y = 0 := by
  obtain ⟨y, hy⟩ := exists_dual hG hx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(hf σ G y y / 2)) = -(hf σ G y y / 2) := by
    rw [map_neg, map_div₀, hf_conj σ G hG.invol hG.herm, map_ofNat]
  refine ⟨y + (-(hf σ G y y / 2)) • x, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hxx, hy]; ring
  · simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx]
    ring

theorem exists_double [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ γ, IsU σ G γ ∧ γ *ᵥ x = (2 : E) • x := by
  obtain ⟨y, hy, hyy⟩ := exists_dual_iso hG hx hxx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(1 / 2)) = -(1 / 2) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  have hm : ∀ v, (1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x) *ᵥ v =
      v + hf σ G v y • x + (-(1 / 2) : E) • hf σ G v x • y := by
    intro v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
      rk_mulVec]
  refine ⟨1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x, ?_, ?_⟩
  · intro v w
    rw [hm, hm]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx, hyy,
      hf_conj σ G hG.invol hG.herm]
    ring
  · rw [hm, hy, hxx, zero_smul, smul_zero, add_zero, one_smul, two_smul]

theorem char_tvGen : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  intro E _ _ n σ G hG A _ X hX
  have hU1 : IsU σ G 1 := fun x y => by simp
  have hX1 : X 1 = 1 := by
    have := hX 1 1 hU1 hU1
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ X m = 1 := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      have hUq : ∀ q : ℚ, IsU σ G (tv σ G x (q * t)) := by
        intro q
        refine isU_tv σ G hG.invol hG.herm x _ ?_
        rw [hx, map_mul, map_ratCast]
        linear_combination (q : E) * ht
      have hUt : IsU σ G (tv σ G x t) := by simpa using hUq 1
      refine ⟨hUt, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        have : tv σ G 0 t = 1 := by
          ext a b
          simp [tv]
        rw [this, hX1]
      · obtain ⟨γ, hγ, hγx⟩ := exists_double hG hx0 hx
        have h3 : IsU σ G (tv σ G x (1 / 3 * t)) := by
          have := hUq (1 / 3)
          push_cast at this
          exact this
        have hc := conj_tv σ G γ x (1 / 3 * t) hγ
        have he : tv σ G (γ *ᵥ x) (1 / 3 * t) = tv σ G x (1 / 3 * t) * tv σ G x t := by
          rw [hγx, tv_smul, tv_mul, hx, map_ofNat]
          congr 1
          ring
        rw [he] at hc
        have h4 := congrArg X hc
        rw [hX _ _ hγ h3, hX _ _ (isU_mul σ G _ _ h3 hUt) hγ, hX _ _ h3 hUt, mul_comm (X γ)] at h4
        exact mul_eq_left.mp (mul_right_cancel h4).symm
    | one => exact ⟨hU1, hX1⟩
    | mul a b _ _ ha hb =>
      exact ⟨isU_mul σ G _ _ ha.1 hb.1, by rw [hX _ _ ha.1 hb.1, ha.2, hb.2, mul_one]⟩
  exact fun m hm => (key m hm).2

end GlobalTheory.UTrans.TvKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGeneratedByQuasiReflectionsAndWitt
section
open scoped Matrix

namespace GlobalTheory.UTrans.ReflChar0

open GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem hf_sub_smul_left (z x w : Fin n → E) (e : E) :
    hf σ G (z - e • x) w = hf σ G z w - e * hf σ G x w := by
  rw [sub_eq_add_neg, ← neg_smul, hf_add_left, hf_smul_left]
  ring

theorem hf_sub_smul_right (z x w : Fin n → E) (e : E) :
    hf σ G w (z - e • x) = hf σ G w z - σ e * hf σ G w x := by
  rw [sub_eq_add_neg, ← neg_smul, hf_add_right, hf_smul_right, map_neg]
  ring

theorem isU_refl (h : IsHerm σ G) {x : Fin n → E} (hx : hf σ G x x ≠ 0) {u : E} (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by
  apply isU_tv σ G h.invol h.herm
  rw [map_div₀, hf_conj σ G h.invol h.herm, map_sub, map_one]
  field_simp
  linear_combination hu

theorem refl_inv {x : Fin n → E} (hx : hf σ G x x ≠ 0) {u : E} (hu : u * σ u = 1) :
    tv σ G x ((σ u - 1) / hf σ G x x) * tv σ G x ((u - 1) / hf σ G x x) = 1 := by
  rw [tv_mul]
  have : (σ u - 1) / hf σ G x x + (u - 1) / hf σ G x x +
      (σ u - 1) / hf σ G x x * ((u - 1) / hf σ G x x) * hf σ G x x = 0 := by
    field_simp
    linear_combination hu
  rw [this]
  ext a b
  simp [tv]

theorem exists_refl (h : IsHerm σ G) (x z : Fin n → E) (hz : hf σ G z z = hf σ G x x) (e : E)
    (he : σ e = e) (he2 : e * e = 1) (hy : hf σ G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * σ u = 1 ∧
      tv σ G (z - e • x) ((u - 1) / hf σ G (z - e • x) (z - e • x)) *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hf σ G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hf σ G (z - e • x) (z - e • x) = a + σ a := by
    rw [ha, hf_conj σ G h.invol h.herm, hf_sub_smul_left z x (z - e • x), hf_sub_smul_left z x z,
      hf_sub_smul_right z x x, he, hz]
    linear_combination (hf σ G x x) * he2
  have ha0 : a ≠ 0 := by
    intro h0
    exact hy (by rw [hyy, h0]; simp)
  have hca : σ a ≠ 0 := by simpa using ha0
  refine ⟨-σ a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.invol]
    field_simp
  · rw [tv_mulVec, ← ha]
    have : (-σ a / a - 1) / hf σ G (z - e • x) (z - e • x) * a = -1 := by
      rw [div_mul_eq_mul_div, div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

theorem exists_prod_mulVec_eq [CharZero E] (h : IsHerm σ G) (x z : Fin n → E) (hx : hf σ G x x ≠ 0)
    (hz : hf σ G z z = hf σ G x x) :
    ∃ l : List ((Fin n → E) × E),
      (∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧
      (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *ᵥ z = x := by
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hf σ G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hf σ G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [hf_sub_smul_left, hf_sub_smul_right, hf_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hf σ G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', tv_mulVec, hf_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) / hf σ G x x * (-1 * hf σ G x x) = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]

theorem exists_basis [CharZero E] (h : IsHerm σ G) :
    ∃ x : Fin n → Fin n → E, (∀ i, hf σ G (x i) (x i) ≠ 0) ∧
      (∀ i j, i ≠ j → hf σ G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  have he : ∀ x y : Fin n → E, hf σ G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ :=
    GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero h.invol h.herm
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd h.det_ne i
  · rw [he]
    exact hv i j hij

theorem isU_prod (hG : IsHerm σ G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isU_mul σ G _ _ (isU_refl hG hp.1 hp.2) (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem exists_inv (hG : IsHerm σ G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      (l'.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *
        (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    refine ⟨l' ++ [(p.1, σ p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show σ p.2 * σ (σ p.2) = 1
        rw [hG.invol, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (tv σ G _ _), refl_inv hp.1 hp.2, one_mul, h2]

theorem prod_fix (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G v p.1 = 0) :
    (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq), tv_mulVec, hp]
    simp

theorem hf_span {v x z y : Fin n → E} (hx : hf σ G v x = 0) (hz : hf σ G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hf σ G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  rw [hf_add_right, hf_smul_right, hf_smul_right, hx, hz]
  simp

theorem exists_fix [CharZero E] (hG : IsHerm σ G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsU σ G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hf σ G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hf σ G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      ∀ i : Fin n, i.val < k →
        ((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isU_mul σ G _ _ (isU_prod hG l hl) hγ
      set δ := (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ :=
        exists_prod_mulVec_eq hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix _ m fun p hp => hf_span (h2 _ _ hne) ?_ (hm p hp).2.2
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

theorem gen_and_witt : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  intro E _ _ n σ G hG
  refine ⟨fun γ hγ => ?_, fun x z hx hz => ?_⟩
  · obtain ⟨x, h1, h2, h3⟩ := exists_basis hG
    obtain ⟨l, hl, hfix⟩ := exists_fix hG hγ x h1 h2 n
    obtain ⟨l', hl', hinv⟩ := exists_inv hG l hl
    refine ⟨l', hl', ?_⟩
    have hone : (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext_on_range h3 fun i => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
    rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
  · obtain ⟨l, hl, e⟩ := exists_prod_mulVec_eq hG x z hx hz
    exact ⟨_, isU_prod hG l fun p hp => ⟨(hl p hp).1, (hl p hp).2.1⟩, e⟩

end GlobalTheory.UTrans.ReflChar0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaEulerProductNeZeroOneAddMulI
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory

theorem conj_apply_conj_of_entire (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
  have hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) := by
    intro s
    have := (hZ (starRingEnd ℂ s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact h s hs
  have := AnalyticOnNhd.eq_of_eventuallyEq
    (hZ'.differentiableOn.analyticOnNhd isOpen_univ)
    (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev
  exact congrFun this s

theorem zetaEulerProduct_ne_zero_one_add_mul_I : ∀ (ι : Type) (N : ι → ℕ), (∀ i, 2 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z : ℂ → ℂ, Differentiable ℂ Z → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → ∀ t : ℝ, t ≠ 0 → Z (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro ι N hN hsum hne Z hZ hZs t ht ha
  obtain ⟨i₀⟩ := hne
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
  have hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
    refine conj_apply_conj_of_entire Z hZ fun s hs => ?_
    have hs' : 1 < (starRingEnd ℂ s).re := by simpa using hs
    rw [hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj,
      Complex.conj_tsum]
    simp only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]
  set u : ℂ := (t : ℂ) * Complex.I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hure : u.re = 0 := by simp [hu]
  have huc : starRingEnd ℂ u = -u := by simp [hu]
  have hb : Z (1 - u) = 0 := by
    rw [← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]
  have hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a) := by
    intro f a hf
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s := by
    intro f a h0 s
    have := sub_smul_dslope f a s
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this
  have hD1 := hds Z (1 + u) hZ
  have hD2 := hds Z (1 - u) hZ
  have hG := hds _ (1 - u) hD1
  have hD1b : dslope Z (1 + u) (1 - u) = 0 := by
    have := hmul Z (1 + u) ha (1 - u)
    rw [hb, mul_eq_zero] at this
    refine this.resolve_left fun h => hu0 ?_
    linear_combination (-1 / 2 : ℂ) * h
  set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i => by
    simp only [hcdef]
    rw [Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]
    simp
  have hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u := fun i => by
    have harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'
    rw [map_neg, huc, neg_neg, map_natCast] at this
    exact this.symm
  have key := GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) *
      dslope Z (1 - u) (s - u))
    (fun p => by
      have hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc _)
      have h1 := Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))
      have h2 := neg_abs_le (c p.1 ^ (p.2 + 1)).re
      apply div_nonneg (by linarith) (by positivity))
    (fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
    (((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul
      (hD2.comp (differentiable_id.sub_const u)))
    (fun s hs => by
      refine ⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)) := by
        intro i
        simp only [hcdef]
        rw [one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      have e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) =
          1 * ((N i : ℕ) : ℂ) ^ (-(s - u)) := by
        intro i
        rw [hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      simp only [e1, e2]
      rw [Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      have h0 := hZs s hs
      have h1 := hZs (s + u) (by simpa [hure] using hs)
      have h2 := hZs (s - u) (by simpa [hure] using hs)
      have g0 := hmul Z (1 + u) ha s
      have g0' := hmul _ (1 - u) hD1b s
      have g1 := hmul Z (1 + u) ha (s + u)
      have g2 := hmul Z (1 - u) hb (s - u)
      have n1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this; linarith
      have n2 : s - (1 + u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      have n3 : s - (1 - u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *
      generalize dslope (dslope Z (1 + u)) (1 - u) s = G at *
      generalize dslope Z (1 + u) (s + u) = A at *
      generalize dslope Z (1 - u) (s - u) = B at *
      have k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E := by
        rw [← h0, ← g0, ← g0']; ring
      have k1 : (s - 1) * A = (s - (1 - u)) * E1 := by
        linear_combination g1 + h1
      have k2 : (s - 1) * B = (s - (1 + u)) * E2 := by
        linear_combination g2 + h2
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)
      rw [h0]
      calc (s - 1) * (s - (1 + u)) * (s - (1 - u)) * ((s - 1) * E * G * A * B)
          = E * ((s - (1 + u)) * (s - (1 - u)) * G) * ((s - 1) * A) * ((s - 1) * B) := by ring
        _ = _ := by rw [k0, k1, k2]; ring)
  exact not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)

end GlobalTheory
end

