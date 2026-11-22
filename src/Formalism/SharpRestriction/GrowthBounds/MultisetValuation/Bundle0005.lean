import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntCondition : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, PlaceB X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

def RatCondition : Prop := ∀ v j, ∃ q : ℚ, X.g0v v j = q

def HeckeIntegralLevel : Prop :=
  ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ F ∈ X.Int (j + 1), X.Tt v i (j + 1) F ∈ X.Int (j + 1)

theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι) (a : ℝ) (f : ι → ℝ) :
    ∑ v', (if v' = v then a else f v') = a + ∑ v' ∈ univ.erase v, f v' := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun v' hv' => ?_
  rw [if_neg (Finset.ne_of_mem_erase hv')]

variable {X Y}

theorem PlaceB.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hP : PlaceB X Y j v i g) :
    PlaceB X Y j v i g' := by
  unfold PlaceB at *
  rcases hP with ⟨hi, hL | hL⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨hi, Or.inl (Pend.LowAt.mono Y h hL)⟩
  · exact Or.inl ⟨hi, Or.inr (h.trans hL)⟩
  · exact Or.inr ⟨h1, h2, h.trans h3⟩

theorem EntB.mono {j : ℕ} {i0 : X.Pl → ℕ} {g g' : ℝ} (h : g' ≤ g) (hB : EntB X Y j i0 g) : EntB X Y j i0 g' := by
  unfold EntB at *
  intro La La' h1 h2 φ I n
  exact Pend.geC_mono Y h (hB La La' h1 h2 φ I n)

theorem ent_strict (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (gP : X.Pl → ℝ)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (g' : ℝ) (hg : g' < ∑ v, gP v) : EntB X Y j i0 g' := by
  classical
  have hD : 0 < ∑ v, gP v - g' := sub_pos.mpr hg
  have hc : (0 : ℝ) < Fintype.card X.Pl + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (∑ v, gP v - g') / (Fintype.card X.Pl + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hD hc
  have hεc : (Fintype.card X.Pl : ℝ) * ε < ∑ v, gP v - g' := by
    have h1 : ε * (Fintype.card X.Pl + 1) = ∑ v, gP v - g' := by
      rw [hε]; exact div_mul_cancel₀ _ hc.ne'
    nlinarith
  have hq : ∀ v, ∃ q : ℚ, gP v - ε < q ∧ (q : ℝ) < gP v := fun v => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  have hsum : g' ≤ ∑ v, (q v : ℝ) := by
    have h1 : ∑ v, (gP v - ε) ≤ ∑ v, (q v : ℝ) := Finset.sum_le_sum fun v _ => (hq1 v).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    linarith
  exact EntB.mono hsum (hE j hj i0 q fun v => PlaceB.mono (hq2 v).le (hP v))

theorem formB_lim (hF : FormB X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ) (hnd : vs.Nodup)
    (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0) (hB : ∀ g' < g, EntB X Y j i0 g')
    (G : X.Fm j) (hG : G ∈ X.Int j) : X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j) := by
  have he0 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (g - X.dG j) * (X.eO : ℝ) := ⟨_, rfl⟩
  have hc1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hc2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (x - ⌈x⌉ + 1) / ((X.eO : ℝ) + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by linarith)
  have hδe : δ * (X.eO : ℝ) < x - ⌈x⌉ + 1 := by
    have h1 : δ * ((X.eO : ℝ) + 1) = x - ⌈x⌉ + 1 := by
      rw [hδ]; exact div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hlin : (g - δ - X.dG j) * (X.eO : ℝ) = x - δ * (X.eO : ℝ) := by rw [hx]; ring
  have hceil : ⌈(g - δ - X.dG j) * (X.eO : ℝ)⌉ = ⌈(g - X.dG j) * (X.eO : ℝ)⌉ := by
    rw [← hx, Int.ceil_eq_iff, hlin]
    constructor
    · linarith
    · nlinarith
  have h := hF j hj i0 vs (g - δ) hnd hr h0 (hB _ (by linarith)) G hG
  have hv : X.vsc (g - δ - X.dG j) = X.vsc (g - X.dG j) := by rw [vsc_def, vsc_def, hceil]
  unfold Sys.vGe at h ⊢
  rw [hv] at h
  exact h

theorem form_of_place (hF : FormB X Y) (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl)
    (gP : X.Pl → ℝ) (hnd : vs.Nodup) (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (∑ v, gP v - X.dG j) :=
  formB_lim hF j hj i0 vs (∑ v, gP v) hnd hr h0 (fun g' hg' => ent_strict hE j hj i0 gP hP g' hg') G hG

theorem form_valuation_of_bound (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (h3 : adm3 D X Y) : Conclusion0 D X := by
  unfold Conclusion0
  intro j hj G hG
  have h := hF j hj (fun _ => 0) [] 0 List.nodup_nil (fun _ => Nat.zero_le _) (fun _ _ => rfl)
    (fun La La' h1 h2 φ I n => h3 j hj La La' h1 h2 φ I n) G hG
  rw [zero_sub] at h
  exact h

theorem theorem_A_entries_of_corollary (D : Formalism.BasicNotions.D7) (hE : EntCondition X Y) (hQ : RatCondition X) (h2U : VolumeRatio₂ D X Y) : projection_lemma_base_level D X Y := by
  unfold projection_lemma_base_level
  intro j hj La La' h1 h2 φ I n
  choose q hq using hQ
  have hP : ∀ v, PlaceB X Y j v 0 (q v (j + 1)) := fun v =>
    Or.inl ⟨rfl, Or.inl (by rw [← hq v (j + 1)]; exact h2U v j hj)⟩
  have h := hE j hj (fun _ => 0) (fun v => q v (j + 1)) hP La La' h1 h2 φ I n
  have hs : ∑ v, X.g0v v (j + 1) = ∑ v, ((q v (j + 1) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun v _ => hq v (j + 1)
  rw [hs]
  exact h

theorem slopeEstimate_of_lemmaB_slopeLine (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : Conclusion2 D X := by
  unfold Conclusion2
  intro j hj G hG
  exact form_of_place hF hE j hj (fun _ => 0) [] (fun v => X.g0v v (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) (fun v => Or.inl ⟨rfl, Or.inl (h2U v j hj)⟩) G hG

theorem hecke_integral_of_forms (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : MassRatio₂ D X := by
  classical
  unfold MassRatio₂
  intro v j hj G hG
  have hP : ∀ v', PlaceB X Y j v' 0
      (if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl]
      exact Or.inl ⟨rfl, Or.inr le_rfl⟩
    · rw [if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun _ => 0) []
    (fun v' => if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  exact h

theorem hecke_valuation_of_entries (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (v : X.Pl) (j : ℕ)
    (hj : j < X.mm) (i : ℕ) (hi : i ∈ Icc 1 X.G.P.r) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j) := by
  classical
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hP : ∀ v', PlaceB X Y j v' (if v' = v then i else 0)
      (if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl, if_pos rfl]
      exact Or.inr ⟨hi1, hi2, le_rfl⟩
    · rw [if_neg hv, if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun v' => if v' = v then i else 0) [v]
    (fun v' => if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) (List.nodup_singleton v)
    (fun v' => by split_ifs <;> omega)
    (fun v' hv' => if_neg (by simpa using hv')) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  simpa only [TtL, List.foldr_cons, List.foldr_nil, eq_self_iff_true, if_true, ↓reduceIte] using h

theorem latticeChain_succ_of_partial (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (hB1 : HeckeIntegralLevel X) :
    PointsLemma D X := fun v j hj =>
  ⟨fun i hi F hF' => hB1 v j hj i hi F hF', fun i hi G hG => hecke_valuation_of_entries D hF hE h2U v j hj i hi G hG⟩

theorem ramifiedLattice_of_chain_estimates (D : Formalism.BasicNotions.D7) (h2U : VolumeRatio₂ D X Y) (h5D : LowTermBound D X Y) : Conclusion5 D X := by
  unfold Conclusion5
  refine ⟨fun v => relative_presentation_of_d7 D _ _ _ _ _ _ _ _ _ _ _ _ (X.std v), fun VV F hF => ?_⟩
  exact h5D X.gv X.g0v X.Conclusion₂ X.Svv VV (fun _ _ _ _ => le_rfl) h2U (fun _ _ _ _ => le_rfl)
    (fun _ _ => le_rfl) F hF

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RationalLowerBounds
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

structure nm_Hyp {K : Type*} [Field K] (R : Subring K) (p : ℕ) : Prop where
  one_lt : 1 < p
  val : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R
  rk : ∀ x : K, x ≠ 0 → (∃ n : ℕ, (p : K) ^ n / x ∈ R) ∧ (x⁻¹ ∉ R → ∃ n : ℕ, x ^ n / (p : K) ∈ R)
  pinv : (p : K)⁻¹ ∉ R

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

theorem nm_p_ne (h : nm_Hyp R p) : (p : K) ≠ 0 := by
  intro h0
  apply h.pinv
  rw [h0, inv_zero]
  exact R.zero_mem

theorem nm_root (h : nm_Hyp R p) {y : K} {k : ℕ} (hk : 0 < k) (hy : y ^ k ∈ R) : y ∈ R := by
  by_contra hyR
  have hy0 : y ≠ 0 := fun h0 => hyR (h0 ▸ R.zero_mem)
  have hinv : y⁻¹ ∈ R := (h.val y).resolve_left hyR
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : y ^ (m + 1) * y⁻¹ ^ m = y := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hy0, one_pow, mul_one]
  exact hyR (e ▸ R.mul_mem hy (R.pow_mem hinv _))

theorem nm_zpow_mem_iff (h : nm_Hyp R p) (k : ℤ) : (p : K) ^ k ∈ R ↔ 0 ≤ k := by
  constructor
  · intro hk
    by_contra hneg
    push_neg at hneg
    apply h.pinv
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    have e : (p : K) ^ (-((n : ℤ) + 1)) = ((p : K)⁻¹) ^ (n + 1) := by
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, inv_pow]
    exact nm_root h (Nat.succ_pos n) (e ▸ hk)
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact R.pow_mem (natCast_mem R p) k

variable (R p)

def nm_P (x : K) (a : ℤ) (b : ℕ) : Prop := x ^ b * (p : K) ^ (-a) ∈ R

def rationalLowerBounds (x : K) : Set ℝ := {q | ∃ (a : ℤ) (b : ℕ), 0 < b ∧ q = (a : ℝ) / b ∧ nm_P R p x a b}

def nm_v (x : K) : ℝ := sSup (rationalLowerBounds R p x)

variable {R p}

theorem nm_T_nonempty (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : (rationalLowerBounds R p x).Nonempty := by
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).1
  refine ⟨_, -(n : ℤ), 1, one_pos, rfl, ?_⟩
  unfold nm_P
  rw [pow_one, neg_neg, zpow_natCast, mul_comm]
  rwa [div_inv_eq_mul] at hn

theorem nm_T_bdd (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : BddAbove (rationalLowerBounds R p x) := by
  have hp0 := nm_p_ne h
  obtain ⟨n, hn⟩ := (h.rk x hx).1
  refine ⟨n, ?_⟩
  rintro q ⟨a, b, hb, rfl, hP⟩
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx
  have e : (p : K) ^ ((n : ℤ) * b - a) = ((p : K) ^ n / x) ^ b * (x ^ b * (p : K) ^ (-a)) := by
    rw [sub_eq_add_neg, zpow_add₀ hp0, ← Nat.cast_mul, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv,
      mul_assoc, inv_mul_cancel_left₀ hxb]
  have hmem : (p : K) ^ ((n : ℤ) * b - a) ∈ R := e ▸ R.mul_mem (R.pow_mem hn b) hP
  have h0 := (nm_zpow_mem_iff h _).1 hmem
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have : (a : ℤ) ≤ (n : ℤ) * b := by linarith
  exact_mod_cast this

theorem nm_le_v (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) {a : ℤ} {b : ℕ} (hb : 0 < b) (hP : nm_P R p x a b) :
    (a : ℝ) / b ≤ nm_v R p x := by
  unfold nm_v
  exact le_csSup (nm_T_bdd h hx) ⟨a, b, hb, rfl, hP⟩

theorem nm_dich (h : nm_Hyp R p) (x : K) (a : ℤ) (b : ℕ) : nm_P R p x a b ∨ nm_P R p x⁻¹ (-a) b := by
  rcases h.val (x ^ b * (p : K) ^ (-a)) with h1 | h1
  · exact Or.inl h1
  · right
    unfold nm_P
    convert h1 using 1
    rw [mul_inv, inv_pow, neg_neg, zpow_neg, inv_inv]

theorem nm_P_mul (h : nm_Hyp R p) {x y : K} {a a' : ℤ} {b b' : ℕ} (hx : nm_P R p x a b) (hy : nm_P R p y a' b') :
    nm_P R p (x * y) (a * b' + a' * b) (b * b') := by
  unfold nm_P at *
  have e : (x * y) ^ (b * b') * (p : K) ^ (-(a * b' + a' * b)) =
      (x ^ b * (p : K) ^ (-a)) ^ b' * (y ^ b' * (p : K) ^ (-a')) ^ b := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← zpow_natCast ((p : K) ^ (-a)) b',
      ← zpow_natCast ((p : K) ^ (-a')) b, ← zpow_mul, ← zpow_mul, mul_comm b' b]
    have : (p : K) ^ (-(a * b' + a' * b)) = (p : K) ^ (-a * b') * (p : K) ^ (-a' * b) := by
      rw [← zpow_add₀ (nm_p_ne h)]; congr 1; ring
    rw [this]
    ring
  rw [e]
  exact R.mul_mem (R.pow_mem hx _) (R.pow_mem hy _)

theorem nm_v_mul_ge (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p x + nm_v R p y ≤ nm_v R p (x * y) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h1 : ∀ q' ∈ rationalLowerBounds R p y, nm_v R p x ≤ nm_v R p (x * y) - q' := by
    rintro q' ⟨a', b', hb', rfl, hP'⟩
    apply csSup_le (nm_T_nonempty h hx)
    rintro q ⟨a, b, hb, rfl, hP⟩
    have h2 := nm_le_v h hxy (Nat.mul_pos hb hb') (nm_P_mul h hP hP')
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbR' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb'.ne'
    have e : (((a * b' + a' * b : ℤ) : ℝ)) / ((b * b' : ℕ) : ℝ) = (a : ℝ) / b + (a' : ℝ) / b' := by
      push_cast
      field_simp
    rw [e] at h2
    linarith
  have h3 : nm_v R p y ≤ nm_v R p (x * y) - nm_v R p x := by
    apply csSup_le (nm_T_nonempty h hy)
    intro q' hq'
    have := h1 q' hq'
    linarith
  linarith

theorem nm_v_one (h : nm_Hyp R p) : nm_v R p (1 : K) = 0 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h one_ne_zero)
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [one_pow, one_mul] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := by linarith
      exact_mod_cast this
    exact div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
  · have := nm_le_v h (one_ne_zero (α := K)) (a := 0) (b := 1) Nat.one_pos (by
      unfold nm_P
      simp only [pow_one, neg_zero, zpow_zero, mul_one]
      exact R.one_mem)
    simpa using this

theorem nm_v_inv (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : nm_v R p x⁻¹ = -nm_v R p x := by
  have hx' := inv_ne_zero hx
  have h1 : nm_v R p x + nm_v R p x⁻¹ ≤ 0 := by
    have := nm_v_mul_ge h hx hx'
    rwa [mul_inv_cancel₀ hx, nm_v_one h] at this
  have h2 : 0 ≤ nm_v R p x + nm_v R p x⁻¹ := by
    by_contra hneg
    have hlt : nm_v R p x < -nm_v R p x⁻¹ := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rcases nm_dich h x q.num q.den with h3 | h3
    · have := nm_le_v h hx q.den_pos h3
      rw [← hq] at this
      linarith
    · have := nm_le_v h hx' q.den_pos h3
      have e : (((-q.num : ℤ)) : ℝ) / (q.den : ℝ) = -(q : ℝ) := by
        rw [hq]; push_cast; ring
      rw [e] at this
      linarith
  linarith

theorem nm_v_mul (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p (x * y) = nm_v R p x + nm_v R p y := by
  apply le_antisymm _ (nm_v_mul_ge h hx hy)
  have h1 := nm_v_mul_ge h (mul_ne_zero hx hy) (inv_ne_zero hy)
  rw [mul_assoc, mul_inv_cancel₀ hy, mul_one, nm_v_inv h hy] at h1
  linarith

theorem nm_v_nonneg (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) (hxR : x ∈ R) : 0 ≤ nm_v R p x := by
  have := nm_le_v h hx (a := 0) (b := 1) Nat.one_pos (by
    unfold nm_P
    simp only [pow_one, neg_zero, zpow_zero, mul_one]
    exact hxR)
  simpa using this

theorem nm_v_neg (h : nm_Hyp R p) {x : K} (hxR : x ∉ R) : nm_v R p x < 0 := by
  have hx : x ≠ 0 := fun h0 => hxR (h0 ▸ R.zero_mem)
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).2 (by rwa [inv_inv])
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_div] at hn
      exact h.pinv hn
    · exact h0
  have h1 := nm_le_v h (inv_ne_zero hx) (a := 1) (b := n) hn0 (by
    unfold nm_P
    rw [zpow_neg_one, ← div_eq_mul_inv]
    exact hn)
  rw [nm_v_inv h hx] at h1
  have : (0 : ℝ) < ((1 : ℤ) : ℝ) / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  linarith

theorem nm_v_nonneg_iff (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : 0 ≤ nm_v R p x ↔ x ∈ R :=
  ⟨fun h0 => by
    by_contra hxR
    exact absurd (nm_v_neg h hxR) (not_lt.2 h0), nm_v_nonneg h hx⟩

theorem nm_v_p (h : nm_Hyp R p) : nm_v R p (p : K) = 1 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h (nm_p_ne h))
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [← zpow_natCast, ← zpow_add₀ (nm_p_ne h)] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [div_le_one hb']
    have : a ≤ b := by linarith
    exact_mod_cast this
  · have := nm_le_v h (nm_p_ne h) (a := 1) (b := 1) Nat.one_pos (by
      unfold nm_P
      rw [pow_one, zpow_neg_one, mul_inv_cancel₀ (nm_p_ne h)]
      exact R.one_mem)
    simpa using this

theorem nm_v_add (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nm_v R p x) (nm_v R p y) ≤ nm_v R p (x + y) := by
  have key : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x / y ∈ R → nm_v R p y ≤ nm_v R p (x + y) := by
    intro x y _ hy hxy hR
    have e : x + y = y * (1 + x / y) := by field_simp; ring
    have h1 : 1 + x / y ≠ 0 := by
      intro h0
      apply hxy
      rw [e, h0, mul_zero]
    rw [e, nm_v_mul h hy h1]
    have := nm_v_nonneg h h1 (R.add_mem R.one_mem hR)
    linarith
  rcases h.val (x / y) with h1 | h1
  · exact le_trans (min_le_right _ _) (key hx hy hxy h1)
  · rw [inv_div] at h1
    rw [add_comm] at hxy ⊢
    exact le_trans (min_le_left _ _) (key hy hx hxy h1)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

