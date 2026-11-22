import Formalism.LocalToGlobal.CharacterGerms.Bundle0027
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem
import Formalism.LocalToGlobal.CharacterGerms.Bundle0026

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigA
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj

section Lim

variable {C : Type} [Field C] {V : VF C} {n : ℕ}

def MT (V : VF C) (A : ℕ → Matrix (Fin n) (Fin n) C) (B : Matrix (Fin n) (Fin n) C) : Prop :=
  ∀ i j, Tends V (fun k => A k i j) (B i j)

def IntM (V : VF C) (A : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, V.Ge 0 (A i j)

private theorem tends_const' (x : C) : Tends V (fun _ => x) x := fun w => ⟨0, fun n _ => by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (x - x)
  rw [sub_self, AddValuation.map_zero]
  exact le_top⟩

theorem MT.const (B : Matrix (Fin n) (Fin n) C) : MT V (fun _ => B) B :=
  fun i j => tends_const' _

variable {A A' : ℕ → Matrix (Fin n) (Fin n) C} {B B' : Matrix (Fin n) (Fin n) C}

theorem MT.add (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k + A' k) (B + B') :=
  fun i j => (h i j).add (h' i j)

theorem MT.sub (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k - A' k) (B - B') :=
  fun i j => (h i j).sub (h' i j)

theorem MT.smul (c : C) (h : MT V A B) : MT V (fun k => c • A k) (c • B) :=
  fun i j => (tends_const' c).mul (h i j)

theorem MT.mul (h : MT V A B) (h' : MT V A' B') : MT V (fun k => A k * A' k) (B * B') := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Tends.sum Finset.univ (fun l _ => (h i l).mul (h' l j))

theorem MT.pow (h : MT V A B) (m : ℕ) : MT V (fun k => A k ^ m) (B ^ m) := by
  induction m with
  | zero => simpa using MT.const (V := V) (1 : Matrix (Fin n) (Fin n) C)
  | succ m ih => simpa only [pow_succ] using ih.mul h

theorem MT.unique (h : MT V A B) (h' : MT V A B') : B = B' :=
  Matrix.ext fun i j => (h i j).unique (h' i j)

theorem MT.shift (h : MT V A B) : MT V (fun k => A (k + 1)) B := by
  intro i j w
  obtain ⟨n0, hn0⟩ := h i j w
  exact ⟨n0, fun m hm => hn0 (m + 1) (by omega)⟩

theorem IntM.of_MT (h : MT V A B) (hA : ∀ k, IntM V (A k)) : IntM V B :=
  fun i j => (h i j).ge0 (fun k => hA k i j)

theorem IntM.mul {X Y : Matrix (Fin n) (Fin n) C} (hX : IntM V X) (hY : IntM V Y) : IntM V (X * Y) := by
  intro i j
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v (∑ l, X i l * Y l j)
  apply AddValuation.map_le_sum
  intro l _
  rw [AddValuation.map_mul]
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (X i l) := hX i l
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (Y l j) := hY l j
  simpa using add_le_add h1 h2

theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  show ((k : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) ^ k)
  rw [AddValuation.map_pow, V.v_l, nsmul_one]
  simp

end Lim

section Key

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem hPT : MT V (fun k => K.ρ (K.ε ^ V.l ^ k)) K.P := by
  intro i j w
  obtain ⟨n0, hn0⟩ := K.P_lim ⌈w⌉₊ i j
  refine ⟨n0, fun n hn => ?_⟩
  have h := hn0 n hn
  show (w : WithTop ℝ) ≤ _
  exact le_trans (WithTop.coe_le_coe.mpr (Nat.le_ceil w)) h

theorem ρ_comm (x y : O) : K.ρ x * K.ρ y = K.ρ y * K.ρ x := by
  rw [← map_mul, mul_comm, map_mul]

theorem P_comm (x : O) : K.P * K.ρ x = K.ρ x * K.P := by
  have e : (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) = fun k => K.ρ x * K.ρ (K.ε ^ V.l ^ k) :=
    funext fun k => ρ_comm K _ _
  have h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ x) (K.P * K.ρ x) := (hPT K).mul (MT.const _)
  rw [e] at h1
  exact h1.unique ((MT.const (K.ρ x)).mul (hPT K))

theorem ρ_natmul (m : ℕ) (y : O) : K.ρ ((m : O) * y) = (m : C) • K.ρ y := by
  rw [map_mul, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

theorem P_int : IntM V K.P :=
  IntM.of_MT (hPT K) (fun k i j => K.ρ_int _ i j)

theorem P_idem : K.P * K.P = K.P := by
  obtain ⟨y, hy⟩ := K.ε_idem
  have hd : ((V.l : ℕ) : O) ∣ K.ε ^ 2 - K.ε := ⟨y, by rw [pow_two]; exact hy⟩
  have hk : ∀ k : ℕ, ∃ z : O,
      (K.ε ^ 2) ^ V.l ^ k - K.ε ^ V.l ^ k = ((V.l ^ (k + 1) : ℕ) : O) * z := by
    intro k
    obtain ⟨z, hz⟩ := dvd_sub_pow_of_dvd_sub hd k
    exact ⟨z, by rw [hz, Nat.cast_pow]⟩
  choose z hz using hk
  have e : ∀ k, K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k) =
      ((V.l ^ (k + 1) : ℕ) : C) • K.ρ (z k) := by
    intro k
    rw [← ρ_natmul K, ← hz k, map_sub, pow_right_comm, pow_two, map_mul]
  have h1 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k))
      (K.P * K.P - K.P) := ((hPT K).mul (hPT K)).sub (hPT K)
  have h0 : MT V (fun k => K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) 0 := by
    intro i j w
    refine ⟨⌈w⌉₊, fun k hk => ?_⟩
    show (w : WithTop ℝ) ≤ V.v ((0 : Matrix (Fin n) (Fin n) C) i j -
      (K.ρ (K.ε ^ V.l ^ k) * K.ρ (K.ε ^ V.l ^ k) - K.ρ (K.ε ^ V.l ^ k)) i j)
    rw [e k, Matrix.zero_apply, zero_sub, AddValuation.map_neg, Matrix.smul_apply, smul_eq_mul,
      AddValuation.map_mul]
    have h2 : (((k + 1 : ℕ) : ℝ) : WithTop ℝ) ≤ V.v (((V.l ^ (k + 1) : ℕ) : C)) := by
      have := ge_lpow (V := V) (k + 1)
      rw [Nat.cast_pow]
      exact this
    have h3 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (K.ρ (z k) i j) := K.ρ_int _ i j
    have h4r : w ≤ ((k + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil w).trans (by exact_mod_cast (by omega : ⌈w⌉₊ ≤ k + 1))
    have h4 : (w : WithTop ℝ) ≤ (((k + 1 : ℕ) : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.mpr h4r
    calc (w : WithTop ℝ) ≤ (((k + 1 : ℕ) : ℝ) : WithTop ℝ) := h4
      _ = (((k + 1 : ℕ) : ℝ) : WithTop ℝ) + ((0 : ℝ) : WithTop ℝ) := by
        rw [WithTop.coe_zero, add_zero]
      _ ≤ _ := add_le_add h2 h3
  exact sub_eq_zero.mp (h1.unique h0)

theorem S_mul (x y : O) : K.P * K.ρ x * (K.P * K.ρ y) = K.P * K.ρ (x * y) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K.ρ x), ← P_comm K x, Matrix.mul_assoc K.P (K.ρ x),
    ← Matrix.mul_assoc K.P K.P, P_idem K, ← map_mul]

theorem S_pow (x : O) (m : ℕ) : (K.P * K.ρ x) ^ (m + 1) = K.P * K.ρ (x ^ (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, S_mul, ← pow_succ]

def Acl : Set (Matrix (Fin n) (Fin n) C) := {B | ∃ s : ℕ → O, MT V (fun k => K.P * K.ρ (s k)) B}

theorem S_mem (x : O) : K.P * K.ρ x ∈ Acl K :=
  ⟨fun _ => x, MT.const _⟩

theorem add_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B + B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k + s' k, ?_⟩
  simpa only [map_add, Matrix.mul_add] using hs.add hs'

theorem neg_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : -B ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  refine ⟨fun k => -s k, ?_⟩
  simpa only [map_neg, Matrix.mul_neg, zero_sub] using (MT.const (V := V) (0 : Matrix (Fin n) (Fin n) C)).sub hs

theorem sub_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B - B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k - s' k, ?_⟩
  simpa only [map_sub, Matrix.mul_sub] using hs.sub hs'

theorem mul_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B * B' ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  refine ⟨fun k => s k * s' k, ?_⟩
  simpa only [S_mul K] using hs.mul hs'

theorem P_mem : K.P ∈ Acl K := by
  refine ⟨fun _ => 1, ?_⟩
  simpa only [map_one, Matrix.mul_one] using MT.const (V := V) K.P

theorem pow_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (m : ℕ) : B ^ (m + 1) ∈ Acl K := by
  induction m with
  | zero => simpa using hB
  | succ m ih =>
    rw [pow_succ]
    exact mul_mem K ih hB

theorem comm_mem {B B' : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (hB' : B' ∈ Acl K) : B * B' = B' * B := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨s', hs'⟩ := hB'
  have e : (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) =
      fun k => K.P * K.ρ (s' k) * (K.P * K.ρ (s k)) := by
    funext k
    rw [S_mul, S_mul, mul_comm (s k)]
  have h1 : MT V (fun k => K.P * K.ρ (s k) * (K.P * K.ρ (s' k))) (B * B') := hs.mul hs'
  rw [e] at h1
  exact h1.unique (hs'.mul hs)

theorem int_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : IntM V B := by
  obtain ⟨s, hs⟩ := hB
  exact IntM.of_MT hs (fun k => IntM.mul (P_int K) (fun i j => K.ρ_int _ i j))

theorem closed_mem {A : ℕ → Matrix (Fin n) (Fin n) C} {B : Matrix (Fin n) (Fin n) C} (hA : ∀ k, A k ∈ Acl K)
    (h : MT V A B) : B ∈ Acl K := by
  have hA' : ∀ k : ℕ, ∃ m : O, ∀ i j, V.Ge k (A k i j - (K.P * K.ρ m) i j) := by
    intro k
    obtain ⟨s, hs⟩ := hA k
    have hN : ∀ i j, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge k (A k i j - (K.P * K.ρ (s m)) i j) :=
      fun i j => hs i j k
    choose N hN using hN
    refine ⟨s (Finset.univ.sup fun p : Fin n × Fin n => N p.1 p.2), fun i j => hN i j _ ?_⟩
    exact Finset.le_sup (f := fun p : Fin n × Fin n => N p.1 p.2) (Finset.mem_univ (i, j))
  choose t ht using hA'
  refine ⟨t, fun i j w => ?_⟩
  obtain ⟨n0, hn0⟩ := h i j w
  refine ⟨max n0 ⌈w⌉₊, fun k hk => ?_⟩
  have h1 : V.Ge w (B i j - A k i j) := hn0 k (le_of_max_le_left hk)
  have h2 : V.Ge k (A k i j - (K.P * K.ρ (t k)) i j) := ht k i j
  have h2' : (w : WithTop ℝ) ≤ V.v (A k i j - (K.P * K.ρ (t k)) i j) :=
    le_trans (WithTop.coe_le_coe.mpr
      ((Nat.le_ceil w).trans (by exact_mod_cast le_of_max_le_right hk))) h2
  show (w : WithTop ℝ) ≤ V.v (B i j - (K.P * K.ρ (t k)) i j)
  have e : B i j - (K.P * K.ρ (t k)) i j =
      (B i j - A k i j) + (A k i j - (K.P * K.ρ (t k)) i j) := by ring
  rw [e]
  exact le_trans (le_min h1 h2') (V.v.map_add _ _)

end Key

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

section Glue

variable {C : Type} [Field C] {V : VF C}

theorem tends_pow_zero {a : C} (ha : V.MM a) : Tends V (fun n => a ^ V.l ^ n) 0 := by
  unfold Tends VF.MM at *
  intro w
  by_cases ha0 : a = 0
  · refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [ha0, zero_pow (pow_pos V.l_prime.pos n).ne', sub_zero, AddValuation.map_zero]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff V.v).mpr ha0)
    have hr0 : 0 < r := by
      rw [← hr] at ha
      exact WithTop.coe_pos.mp ha
    refine ⟨⌈w / r⌉₊, fun n hn => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [zero_sub, AddValuation.map_neg, AddValuation.map_pow, ← hr, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ ((V.l ^ n : ℕ) : ℝ) := by
      first
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt n).le
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt).le
    have h2 : w / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (div_mul_cancel₀ w hr0.ne').ge.trans (mul_le_mul_of_nonneg_right (h2.trans h1) hr0.le)

variable [CharZero C] {O : Type} [CommRing O] {n d : ℕ}

theorem chi_kill (K : KeyData C V O n d) (w : Fin n → C) (hw : w ≠ 0) (hP : Matrix.mulVec K.P w = w)
    (χ : O →+* C) (hχ : ∀ x, Matrix.mulVec (K.ρ x) w = χ x • w) :
    (∀ y, V.Ge 0 (χ y)) ∧ ∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z) := by
  have hint : ∀ y, V.Ge 0 (χ y) := fun y => eig_int (K.ρ y) (K.ρ_int y) w hw (χ y) (hχ y)
  refine ⟨hint, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  have hT : Tends V (fun m => χ K.ε ^ V.l ^ m * w i) (w i) := by
    have h1 : Tends V (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) (Matrix.mulVec K.P w i) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Tends.sum _ fun j _ => Tends.mul ?_ (tends_const _)
      exact RowTiePProj.tends_of_nat fun N => K.P_lim N i j
    have e : (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) = fun m => χ K.ε ^ V.l ^ m * w i := by
      funext m
      rw [hχ, map_pow]; rfl
    rw [e, hP] at h1
    exact h1
  have hunit : ¬ V.MM (χ K.ε) := by
    intro hm
    have h0 := (tends_pow_zero hm).mul (tends_const (V := V) (w i))
    rw [zero_mul] at h0
    exact hi (hT.unique h0)
  intro z hz
  obtain ⟨y, hy⟩ := K.ε_ann z hz
  have h1 := congrArg (fun t => V.v (χ t)) hy
  simp only [map_mul, map_natCast, AddValuation.map_mul, V.v_l] at h1
  unfold VF.MM at hunit ⊢
  push_neg at hunit
  have he0 : V.v (χ K.ε) = 0 := le_antisymm hunit (hint K.ε)
  rw [he0, zero_add] at h1
  rw [h1]
  have := hint y
  unfold VF.Ge at this
  calc (0 : WithTop ℝ) < 1 := by exact_mod_cast one_pos
    _ = 1 + 0 := (add_zero _).symm
    _ ≤ 1 + V.v (χ y) := add_le_add le_rfl (by exact_mod_cast this)

end Glue

section Top

theorem keyLA_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) (C : Type) [Field C] [CharZero C] (V : VF C)
    (hac : IsAlgClosed C)
    (hcpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (x : O) :
    Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P = 0 := by
  have hv : ∀ v : Fin n → C,
      Matrix.mulVec (Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P) v = 0 := by
    intro v
    obtain ⟨m, w, χ, hPv, hw⟩ := hE C V hac hcpl O n d K v
    rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h0 : w j = 0
    · rw [h0, Matrix.mulVec_zero]
    obtain ⟨hPw, hχ⟩ := hw j
    obtain ⟨hint, hkill⟩ := chi_kill K (w j) h0 hPw (χ j) hχ
    obtain ⟨c, hc⟩ := hR C V O n d K (χ j) hint hkill
    have heq := hD C V O n d K (χ j) c hint hc
    rw [aeval_mulVec _ _ _ (hχ x), Polynomial.eval_prod]
    have : ∏ c' : ZMod d, Polynomial.eval (χ j x) (Polynomial.X - Polynomial.C (K.em c' x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self])
    rw [this, zero_smul]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem key_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) : KeySt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g ε hε hε1 hεx e he x
  let K : KeyData C V O dd d :=
    { ρ := linHom Y
      ρ_int := fun x i j => Y.intAct x i _
      P := linM e
      em := fun a => p.em g a
      em_int := fun a x => p.em_int g a x
      em_frob := fun a x => p.em_frob g a x
      ε := ε
      ε_idem := hε
      ε_one := hε1
      ε_ann := hεx
      P_lim := fun N i j => he N i _ }
  exact keyLA_of hE hR hD C V Y.algClosed Y.cpl O dd d K x

end Top

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef
section
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def TeichSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (n d : ℕ), d ≠ 0 → ∀ (A : Set (Matrix (Fin n) (Fin n) C)),
      (∀ a ∈ A, ∀ b ∈ A, a + b ∈ A) → (∀ a ∈ A, -a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, ∀ i j, V.Ge 0 (a i j)) →
      (∀ (s : ℕ → Matrix (Fin n) (Fin n) C) (b : Matrix (Fin n) (Fin n) C), (∀ k, s k ∈ A) →
        (∀ i j, RowTiePE0.Tends V (fun k => s k i j) (b i j)) → b ∈ A) →
      (∀ a ∈ A, ((V.l : C)⁻¹) • (a ^ V.l ^ d - a) ∈ A) →
      ∀ b ∈ A, ∃ τ ∈ A, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b - τ) ∈ A

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _
  rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
    Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

end VP

theorem valuation_eq_pair_of_cuts : ValEqPFromCutsSt := by
  intro C _ _ V O _ _ dd d _ Orb _ I _ Y p H Ls n h1 h2 h3 h4 hs P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hUeq⟩ := h2 hs
  obtain ⟨U', hU'i, hU'U⟩ := VP.intInv hUi hU0
  choose G hGi hGe using fun o ρ => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  have hpt : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hpti : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, IntS V (![pt C dd b] s.1 s.2) := by
    intro b s
    simp only [Matrix.cons_val_fin_one, pt]
    exact VP.IntS_X _
  have hb : ∀ b : Fin n, pull1 Y p (U' * ∏ o, G o b) * pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      ∏ o, toAllS o (gr o b * mvExp (Y.raw (p o)).hRow) := by
    intro b
    have e1 : pull1 Y p U' * pull1 Y p U = 1 := by rw [← VP.pullback_one_var_mul, hU'U, VP.pullback_one_var_one]
    rw [hUeq, VP.pullback_one_var_mul, VP.pullback_one_var_prod]
    simp only [hGe, VP.toAllS_mul]
    rw [Finset.prod_mul_distrib]
    calc pull1 Y p U' * (∏ o, toAllS o (gr o b)) * (pull1 Y p U * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow))
        = (pull1 Y p U' * pull1 Y p U) * ((∏ o, toAllS o (gr o b)) * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow)) := by
          ring
      _ = _ := by rw [e1, one_mul]
  have hpull : pullN Y p ((∏ b : Fin n, ev (n := n) ![pt C dd b] (U' * ∏ o, G o b)) *
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      ∏ o, MvPowerSeries.rename (VP.eAll n o)
        (∏ ρ : Fin n, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.raw (p o)).hRow))) := by
    rw [VP.pullN_mul, VP.pullN_prod, VP.pullN_prod, ← Finset.prod_mul_distrib]
    simp only [VP.pullN_ev, ← VP.rowOf_mul, hb, VP.rowOf_prod, VP.rowOf_toAllS, VP.rowCopy_mul_exp, map_prod]
    exact Finset.prod_comm
  refine ⟨∏ b : Fin n, ev (n := n) ![pt C dd b] (U' * ∏ o, G o b), ?_, ?_⟩
  · exact VP.IntS_prod _ fun b _ =>
      IntS.subst (hpt b) (hpti b) (IntS.mul hU'i (VP.IntS_prod _ fun o _ => hGi o b))
  · unfold FBChart.nab nabValN
    rw [h1 n (Ls.ι n) (Ls.cp n) (Ls.uv n) P _ hQ, VP.expS_copies Y n, hpull, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      h4 C V d (I o) (Fin dd) (Y.raw (p o)) (H o) n (Po o) (kind o) (hk o) (gr o)

theorem valuation_eq_pair_of_log_unit_germ {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
    (h1 : LogCoordSt Y p) (h2 : UnitSt Y p) (h3 : GermLiftSt Y p H) : ValEqPSt Y p H Ls n := valuation_eq_pair_of_cuts C V O dd d Orb I Y p H Ls n h1 h2 h3 leaf_holds

end Formalism.L2.FormalSeriesBounds
end
end

