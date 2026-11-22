import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
import Formalism.GL3MeanSquares.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.Cells

section Comb
variable {F : Type} [Field F]

def Good (k : ℕ) (d : ℕ → F) : Prop := d 0 ≠ 0 ∧ ∀ a, k ≤ a → d a = 1

def st (d : ℕ → F) (b : ℕ) : ℕ := Nat.findGreatest (fun a => d a ≠ 0) b

def en (d : ℕ → F) (b : ℕ) : ℕ := sInf {a | b < a ∧ d a ≠ 0}

def sg (k : ℕ) (d : ℕ → F) (b : ℕ) : ℕ := if b < k then k - en d b + (b - st d b) else b

lemma st_le (d : ℕ → F) (b : ℕ) : st d b ≤ b := Nat.findGreatest_le b

lemma st_ne {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : d (st d b) ≠ 0 :=
  Nat.findGreatest_spec (P := fun a => d a ≠ 0) (Nat.zero_le b) h.1

lemma le_st {d : ℕ → F} {a b : ℕ} (hab : a ≤ b) (ha : d a ≠ 0) : a ≤ st d b :=
  Nat.le_findGreatest (P := fun a => d a ≠ 0) hab ha

lemma en_spec {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : b < en d b ∧ d (en d b) ≠ 0 := by
  have : ({a | b < a ∧ d a ≠ 0} : Set ℕ).Nonempty :=
    ⟨b + k + 1, by omega, by rw [h.2 _ (by omega)]; exact one_ne_zero⟩
  exact Nat.sInf_mem this

lemma en_le {d : ℕ → F} {a b : ℕ} (hab : b < a) (ha : d a ≠ 0) : en d b ≤ a :=
  Nat.sInf_le (show a ∈ {a | b < a ∧ d a ≠ 0} from ⟨hab, ha⟩)

lemma en_le_k {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : en d b ≤ k :=
  en_le hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)

lemma dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) :
    (st d c = st d b ∧ en d c = en d b) ∨ en d c ≤ st d b := by
  by_cases h1 : en d c ≤ b
  · exact Or.inr (le_st h1 (en_spec h c).2)
  · left
    have h2 := en_le (d := d) (b := c) (a := en d b) (by have := (en_spec h b).1; omega) (en_spec h b).2
    have h3 := en_le (d := d) (b := b) (a := en d c) (by omega) (en_spec h c).2
    have h4 := le_st (d := d) (a := st d c) (b := b) (by have := st_le d c; omega) (st_ne h c)
    refine ⟨?_, by omega⟩
    by_cases h5 : st d b ≤ c
    · have := le_st h5 (st_ne h b); omega
    · have := en_le (d := d) (b := c) (a := st d b) (by omega) (st_ne h b)
      have := st_le d b; omega

lemma sg_lt {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : b < k) : sg k d b < k := by
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  simp only [sg, if_pos hb]; omega

lemma sg_ge {k : ℕ} (d : ℕ → F) {b : ℕ} (hb : k ≤ b) : sg k d b = b := by
  simp only [sg, if_neg (not_lt.2 hb)]

lemma sg_dich {k : ℕ} {d : ℕ → F} (h : Good k d) {c b : ℕ} (hcb : c < b) (hb : b < k) :
    (st d c = st d b ∧ sg k d c + b = sg k d b + c) ∨ (c < st d b ∧ sg k d b < sg k d c) := by
  have hc : c < k := by omega
  have := en_spec h b; have := en_le_k h hb; have := st_le d b
  have := en_spec h c; have := en_le_k h hc; have := st_le d c
  simp only [sg, if_pos hb, if_pos hc]
  rcases dich h hcb with h1 | h1 <;> omega

lemma sg_inj {k : ℕ} {d : ℕ → F} (h : Good k d) : Function.Injective (sg k d) := by
  intro c b hcb
  wlog hlt : c < b generalizing c b
  · rcases Nat.lt_or_ge b c with h1 | h1
    · exact (this hcb.symm h1).symm
    · omega
  by_cases hb : b < k
  · have := sg_dich h hlt hb; omega
  · rw [sg_ge d (not_lt.1 hb)] at hcb
    by_cases hc : c < k
    · have := sg_lt h hc; omega
    · rwa [sg_ge d (not_lt.1 hc)] at hcb

lemma st_ge {k : ℕ} {d : ℕ → F} (h : Good k d) {b : ℕ} (hb : k ≤ b) : d (st d b) = 1 := by
  have := le_st (d := d) hb (by rw [h.2 _ le_rfl]; exact one_ne_zero)
  exact h.2 _ this

lemma st_eq_iff {k : ℕ} {d : ℕ → F} (h : Good k d) (b : ℕ) : st d b = b ↔ d b ≠ 0 := by
  constructor
  · intro h1; have := st_ne h b; rwa [h1] at this
  · intro h1; exact le_antisymm (st_le d b) (le_st le_rfl h1)

lemma ext_of {k : ℕ} {d d' : ℕ → F} (h : Good k d) (h' : Good k d')
    (H : ∀ b < k, sg k d b = sg k d' b ∧ d (st d b) = d' (st d' b)) : d = d' := by
  funext b
  by_cases hb : b < k
  swap
  · rw [h.2 b (not_lt.1 hb), h'.2 b (not_lt.1 hb)]
  have key : st d b = b ↔ st d' b = b := by
    have := st_le d b; have := st_le d' b
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · omega
    · have := sg_dich h (c := b - 1) (b := b) (by omega) hb
      have := sg_dich h' (c := b - 1) (b := b) (by omega) hb
      have := (H b hb).1
      have := (H (b - 1) (by omega)).1
      have := st_le d (b - 1); have := st_le d' (b - 1)
      omega
  by_cases h1 : st d b = b
  · have := (H b hb).2
    rwa [h1, key.1 h1] at this
  · have h2 : ¬ st d' b = b := fun h2 => h1 (key.2 h2)
    rw [st_eq_iff h, not_not] at h1
    rw [st_eq_iff h', not_not] at h2
    rw [h1, h2]

def mono {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) : GL (Fin N) F where
  val := Matrix.of fun a b => if a = σ b then t b else 0
  inv := Matrix.of fun a b => if b = σ a then (t a)⁻¹ else 0
  val_inv := by
    ext a b
    obtain ⟨c, rfl⟩ := σ.surjective a
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · by_cases h : σ c = b
      · subst h; simp [ht]
      · simp [h, Ne.symm h]
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · by_cases h : a = b
      · subst h; simp [ht]
      · simp [h]
    · intro x _ hx; simp [hx]
    · simp

lemma mono_val {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (a b : Fin N) :
    (mono σ t ht).val a b = if a = σ b then t b else 0 := rfl

lemma mono_rel {N : ℕ} (σ : Equiv.Perm (Fin N)) (t : Fin N → F) (ht : ∀ b, t b ≠ 0) (u u' : GL (Fin N) F)
    (h : u * mono σ t ht = mono σ t ht * u') (c b : Fin N) : u.val (σ c) (σ b) * t b = t c * u'.val c b := by
  have := congrArg (fun x : GL (Fin N) F => x.val (σ c) b) h
  simpa [Units.val_mul, Matrix.mul_apply, mono_val] using this

def perm {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun b => ⟨sg k d b, by
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb; omega
      · rw [sg_ge d (not_lt.1 hb)]; exact b.2⟩)
    (Finite.injective_iff_bijective.1 fun a b hab => Fin.ext (sg_inj h (congrArg Fin.val hab)))

lemma perm_val {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) (b : Fin N) : (perm hk h b : ℕ) = sg k d b := rfl

def cell {k N : ℕ} (hk : k < N) {d : ℕ → F} (h : Good k d) : GL (Fin N) F :=
  mono (perm hk h) (fun b => d (st d b)) fun b => st_ne h b

def dat (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) (a : ℕ) : F :=
  if k ≤ a then 1 else if a = 0 then (p.1 : F) else if h : a - 1 < k - 1 then p.2 ⟨a - 1, h⟩ else 1

lemma dat_good (k : ℕ) (p : Fˣ × (Fin (k - 1) → F)) : Good k (dat k p) := by
  refine ⟨?_, fun a ha => by simp [dat, ha]⟩
  unfold dat
  split_ifs <;> simp_all

lemma dat_inj {k : ℕ} (hk : 0 < k) : Function.Injective (dat (F := F) k) := by
  intro p q h
  ext i
  · have := congrFun h 0
    simpa [dat, hk.ne'] using this
  · have := congrFun h (i + 1)
    have hi := i.2
    have h1 : ¬ k ≤ i + 1 := by omega
    simpa [dat, h1] using this

lemma cell_inj {k N : ℕ} (hk : k < N) {d d' : ℕ → F} (h : Good k d) (h' : Good k d') (H : cell hk h = cell hk h') :
    d = d' := by
  refine ext_of h h' fun b hb => ?_
  have h1 := congrArg (fun x : GL (Fin N) F => x.val (perm hk h ⟨b, by omega⟩) ⟨b, by omega⟩) H
  simp only [cell, mono_val, if_true] at h1
  split_ifs at h1 with h2
  · exact ⟨congrArg Fin.val h2, h1⟩
  · exact absurd h1 (st_ne h b)

end Comb

theorem relevant_cells : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  intro g _ N L hs hco k hk0 hk
  refine ⟨Finset.univ.image fun p : (ZMod g)ˣ × (Fin (k - 1) → ZMod g) => cell hk (dat_good k p), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ fun p q h => dat_inj hk0 (cell_inj hk _ _ h)]
    simp [Nat.totient_prime (Fact.out : g.Prime)]
  · intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    refine ⟨fun a b hab => ?_, perm hk h, fun a b hab => ?_⟩
    · simp only [cell, mono_val, Fin.ext_iff, perm_val]
      by_cases hb : (b : ℕ) < k
      · have := sg_lt h hb
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [sg_ge _ (not_lt.1 hb), st_ge h (not_lt.1 hb)]
    · by_contra h1
      exact hab (by simp only [cell, mono_val]; exact if_neg h1)
  · intro w hw u u' hu hu' hb hb' H
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    have h := dat_good k p
    set d := dat k p
    have rel := mono_rel _ _ _ u u' H
    unfold Lev.chi
    congr 1
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Equiv.sum_comp (perm hk h)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have r := rel c b
    simp only [Lev.Edge, hs, hco, Units.val_one, one_mul, Bool.false_eq_true, if_false, perm_val]
    have tb := st_ne h b
    have tc := st_ne h c
    have hσ : ∀ x : Fin N, (x : ℕ) < k → sg k d x < k := fun x hx => sg_lt h hx
    have hσ' : ∀ x : Fin N, k ≤ (x : ℕ) → sg k d x = x := fun x hx => sg_ge d hx
    have z : c ≠ b → (k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c) →
        u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := by
      intro hne hh
      have e1 : u'.val c b = 0 → u.val (perm hk h c) (perm hk h b) = 0 ∧ u'.val c b = 0 := fun e =>
        ⟨by rw [e, mul_zero] at r; exact (mul_eq_zero.1 r).resolve_right tb, e⟩
      rcases hh with hh | hh | hh
      · exact e1 (by rw [hb' c b (Or.inr hh), if_neg hne])
      · exact e1 (hu'.2 _ _ hh)
      · have e : u.val (perm hk h c) (perm hk h b) = 0 := hu.2 _ _ hh
        exact ⟨e, by rw [e, zero_mul] at r; exact (mul_eq_zero.1 r.symm).resolve_left tc⟩
    by_cases hne : c = b
    · subst hne; simp
    by_cases hh : k ≤ (b : ℕ) ∨ b < c ∨ sg k d b < sg k d c
    · obtain ⟨z1, z2⟩ := z hne hh
      simp [z1, z2]
    · have hne' : (c : ℕ) ≠ b := fun e => hne (Fin.ext e)
      simp only [not_or, Fin.lt_def] at hh
      rcases sg_dich h (c := c) (b := b) (by omega) (by omega) with ⟨e1, e2⟩ | e
      · have e3 : u.val (perm hk h c) (perm hk h b) = u'.val c b := by
          rw [e1, mul_comm] at r
          exact mul_left_cancel₀ tb r
        rw [e3]
        exact if_congr (by omega) rfl rfl
      · omega

end GlobalTheory.BadShare.Cells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvd
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section
namespace GlobalTheory.KZ.RootDisc

open Metric Filter Topology

theorem exists_root_of_ne_zero (g : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ) (hm : 0 < m)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0) (hR : 0 < R) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball c R) ∧ ∀ z ∈ ball c R, s z ^ m = g z := by
  have hd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := hd.isExactOn_ball.with_val_at c (Complex.log (g c))
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgd : ∀ z ∈ ball c R, HasDerivAt g (deriv g z) z := fun z hz =>
    ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hh : ∀ z ∈ ball c R, HasDerivAt (fun w => g w * Complex.exp (-L w)) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w => g w * Complex.exp (-L w))
        (deriv g z * Complex.exp (-L z) + g z * (Complex.exp (-L z) * -(deriv g z / g z))) z :=
      (hgd z hz).mul ((hL z hz).neg.cexp)
    refine h1.congr_deriv ?_
    have e : g z * (deriv g z / g z) = deriv g z := mul_div_cancel₀ _ (hne z hz)
    linear_combination (-Complex.exp (-L z)) * e
  have hexp : ∀ z ∈ ball c R, g z = Complex.exp (L z) := by
    intro z hz
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz hc
    simp only [hL0, Complex.exp_neg, Complex.exp_log (hne c hc)] at hconst
    rw [mul_inv_cancel₀ (hne c hc)] at hconst
    have := Complex.exp_ne_zero (L z)
    field_simp at hconst
    exact hconst
  refine ⟨fun z => Complex.exp (L z / m), ?_, ?_⟩
  · intro z hz
    exact (((hL z hz).differentiableAt.div_const (m : ℂ)).cexp).differentiableWithinAt
  · intro z hz
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hm', hexp z hz]

end GlobalTheory.KZ.RootDisc

namespace GlobalTheory.KZ.RootDisc
open Metric Filter Topology

theorem exists_root_disc : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R →
    AnalyticOnNhd ℂ h (Metric.closedBall c R) →
    (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  intro h m c R hm hR hh hord
  set U := closedBall c R with hU
  have hmer : MeromorphicOn h U := hh.meromorphicOn
  have htop : ∀ u : U, meromorphicOrderAt h u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := hord u hu
    rw [(hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe]
    exact WithTop.coe_ne_top
  have hfin : (MeromorphicOn.divisor h U).support.Finite := (MeromorphicOn.divisor h U).finiteSupport (isCompact_closedBall c R)
  obtain ⟨g, hg, hgne, hgeq⟩ := hmer.extract_zeros_poles htop hfin
  set d := MeromorphicOn.divisor h U with hd
  set S := hfin.toFinset with hS
  have hdU : ∀ u ∈ U, ∃ k : ℕ, d u = ((m * k : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hord u hu
    refine ⟨k, ?_⟩
    rw [hd, MeromorphicOn.divisor_apply hmer hu, (hh u hu).meromorphicOrderAt_eq, hk, ENat.map_coe, WithTop.untop₀_coe]
  let kk : ℂ → ℕ := fun u => (d u).toNat / m
  have hkk : ∀ u ∈ U, d u = ((m * kk u : ℕ) : ℤ) := by
    intro u hu
    obtain ⟨k, hk⟩ := hdU u hu
    have : kk u = k := by
      simp only [kk, hk, Int.toNat_natCast]
      exact Nat.mul_div_cancel_left k hm
    rw [this, hk]
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    exact d.supportWithinDomain hu
  let q : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ kk u
  have hP : ∀ z, (∏ᶠ u, (· - u) ^ d u : ℂ → ℂ) z = q z ^ m := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S), Finset.prod_apply, ← Finset.prod_pow]
    · refine Finset.prod_congr rfl fun u hu => ?_
      rw [hkk u (hSU u hu), zpow_natCast, mul_comm, pow_mul]
      rfl
    · intro u hu
      rw [Set.Finite.coe_toFinset]
      rw [Function.mem_mulSupport] at hu
      rw [Function.mem_support]
      intro h0
      apply hu
      rw [h0, zpow_zero]
  have hqd : Differentiable ℂ q := by
    intro z
    simp only [q]
    fun_prop
  have hgball : DifferentiableOn ℂ g (ball c R) :=
    (hg.mono ball_subset_closedBall).differentiableOn
  obtain ⟨s, hs, hsm⟩ := exists_root_of_ne_zero g m c R hm hgball
    (fun z hz => hgne ⟨z, ball_subset_closedBall hz⟩) hR
  refine ⟨fun z => q z * s z, hqd.differentiableOn.mul hs, ?_⟩
  intro z hz
  rw [mul_pow, hsm z hz]
  have hzU : z ∈ U := ball_subset_closedBall hz
  have hA := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq) z hzU
  have hUn : U ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds
    (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hev : h =ᶠ[𝓝[≠] z] fun w => q w ^ m * g w := by
    filter_upwards [hA, hUn] with w hw hwU
    rcases hw with hw | hw
    · simp only [Set.mem_setOf_eq, Pi.smul_apply', smul_eq_mul] at hw
      rw [hw, hP]
    · exact absurd hwU hw
  have t1 : Tendsto h (𝓝[≠] z) (𝓝 (h z)) :=
    (hh z hzU).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => q w ^ m * g w) (𝓝[≠] z) (𝓝 (q z ^ m * g z)) :=
    (((hqd z).continuousAt.pow m).mul (hg z hzU).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique_of_eventuallyEq t2 t1 hev.symm)

end GlobalTheory.KZ.RootDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevel
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem intCast_eq_of_dvd_sub {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ x - y) : (x : ZMod k) = (y : ZMod k) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y k).2 (by rw [← neg_sub]; exact dvd_neg.2 h)

theorem exists_scalar_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M →
    ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧
      ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  intro N l a M _ hl _ hlN _ hlM
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ((M * N : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = ((l ^ (a + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hcop : IsCoprime Q L := by
    rw [hQ, hL, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2
      (fun h => (hl.dvd_mul.1 h).elim hlM hlN)))
  obtain ⟨α, β, hab⟩ := hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = β * L - α * Q := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = Q * L := ⟨_, rfl⟩
  have e1 : t * t + m * (4 * α * β) = 1 := by
    rw [ht, hm]; linear_combination (α * Q + β * L + 1) * hab
  have hc : IsCoprime t (m ^ 2) := IsCoprime.pow_right ⟨t, 4 * α * β, by linear_combination e1⟩
  obtain ⟨u, v, e2⟩ := hc
  have hut : u - t = m * (4 * α * β * u - t * v * m) := by linear_combination (-u) * e1 + t * e2
  have ht1 : t - 1 = Q * (-2 * α) := by rw [ht]; linear_combination hab
  have ht2 : t - -1 = L * (2 * β) := by rw [ht]; linear_combination (-1 : ℤ) * hab
  obtain ⟨c, hcm⟩ : ∃ c : SL(2, ℤ), (c : Matrix (Fin 2) (Fin 2) ℤ) = !![t, -(m * v); m, u] :=
    ⟨⟨!![t, -(m * v); m, u], by rw [Matrix.det_fin_two_of]; linear_combination e2⟩, rfl⟩
  have h00 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = t := by rw [hcm]; rfl
  have h01 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(m * v) := by rw [hcm]; rfl
  have h10 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = m := by rw [hcm]; rfl
  have h11 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = u := by rw [hcm]; rfl
  have hNQ : (N : ℤ) ∣ Q := hQ ▸ Int.natCast_dvd_natCast.2 (dvd_mul_left N M)
  have hlaL : ((l ^ a : ℕ) : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (pow_dvd_pow l (Nat.le_succ a))
  have hlL : (l : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (dvd_pow_self l (Nat.succ_ne_zero a))
  have hKm : ((M * N * l ^ a : ℕ) : ℤ) ∣ m := by
    rw [hm, hQ, hL, ← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left _ (pow_dvd_pow l (Nat.le_succ a)))
  have hNm : (N : ℤ) ∣ m := hm ▸ hNQ.mul_right L
  have hlm : (l : ℤ) ∣ m := hm ▸ hlL.mul_left Q
  have hlam : ((l ^ a : ℕ) : ℤ) ∣ m := hm ▸ hlaL.mul_left Q

  have tN : ((t : ℤ) : ZMod N) = 1 := by
    simpa using intCast_eq_of_dvd_sub (k := N) (y := 1) (hNQ.trans ⟨_, ht1⟩)
  have uN : ((u : ℤ) : ZMod N) = 1 := by
    have hd : (N : ℤ) ∣ u - 1 := by
      rw [show u - 1 = (u - t) + (t - 1) by ring]
      exact dvd_add (hNm.trans ⟨_, hut⟩) (hNQ.trans ⟨_, ht1⟩)
    simpa using intCast_eq_of_dvd_sub (k := N) hd
  have mN : ((m : ℤ) : ZMod N) = 0 := by simpa using intCast_eq_of_dvd_sub (k := N) (y := 0) (by simpa using hNm)
  have ml : ((m : ℤ) : ZMod l) = 0 := by simpa using intCast_eq_of_dvd_sub (k := l) (y := 0) (by simpa using hlm)

  have tla : ((t : ℤ) : ZMod (l ^ a)) = -1 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := -1) (hlaL.trans ⟨_, ht2⟩)
  have ula : ((u : ℤ) : ZMod (l ^ a)) = -1 := by
    have hd : ((l ^ a : ℕ) : ℤ) ∣ u - -1 := by
      rw [show u - -1 = (u - t) + (t - -1) by ring]
      exact dvd_add (hlam.trans ⟨_, hut⟩) (hlaL.trans ⟨_, ht2⟩)
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) hd
  have mla : ((m : ℤ) : ZMod (l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := 0) (by simpa using hlam)

  have mK : ((m : ℤ) : ZMod (M * N * l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := M * N * l ^ a) (y := 0) (by simpa using hKm)
  have uK : ((u : ℤ) : ZMod (M * N * l ^ a)) = t := intCast_eq_of_dvd_sub (hKm.trans ⟨_, hut⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Gam, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
    simp only [h00, h11, h10, tN, uN, mN, ml, and_self]
  · intro g
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv]
    set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * N * l ^ a)))
    have hsc : (↑(φ c) : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) =
        ((t : ℤ) : ZMod (M * N * l ^ a)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [φ, Matrix.SpecialLinearGroup.map_apply_coe, h00, h01, h10, h11, mK, uK]
    have hcomm : φ c * φ g = φ g * φ c := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, tla, ula, mla]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankRangeLeSumThreeComplements
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem finrank_range_le_three (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (P a b : Module.End ℂ M) :
    Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - a) * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  have hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔
      (LinearMap.range ((1 - b) * P)).map a := by
    rintro _ ⟨x, rfl⟩
    have hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x) := by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P))
    ((LinearMap.range ((1 - b) * P)).map a)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))
  have h4 := Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))
  omega

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gl2L2IntegralityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl2a2_integral_bound_of_sums : Formalism.HermitianLattices.GL2a2.PartialSumIntegralBound := by
  first | exact @GlobalTheory.PsiTail.psi_tail_bound | exact GlobalTheory.PsiTail.psi_tail_bound | (intros; apply GlobalTheory.PsiTail.psi_tail_bound <;> assumption)
end

