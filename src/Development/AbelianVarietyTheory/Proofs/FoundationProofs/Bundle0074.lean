import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLevelDatumGroupMulPow
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

def levMat {g N : ℕ} (S : Finset (Fin N × Fin N)) (f : S → ZMod g) : Matrix (Fin N) (Fin N) (ZMod g) :=
  fun a b => if h : (a, b) ∈ S then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem levMat_det {g N : ℕ} (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) (f : S → ZMod g) :
    (levMat S f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro a _
    have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
    simp [levMat, this]
  · intro a b hab
    have hab' : b < a := hab
    have : (a, b) ∉ S := fun h => lt_asymm hab' (hS _ h)
    simp [levMat, this, hab'.ne']

theorem card_up_supp (g : ℕ) [Fact g.Prime] (N : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} = g ^ S.card := by
  have e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g) :=
    { toFun := fun u p => u.1.val p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by
        refine ⟨fun a => ?_, fun a b hab h => ?_⟩
        · have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
          show levMat S f a a = 1
          simp [levMat, this]
        · show levMat S f a b = 0
          simp [levMat, h, hab]⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        ext a b
        show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b
        unfold levMat
        split_ifs with h1 h2
        · rfl
        · subst h2; exact (u.2.1 a).symm
        · exact (u.2.2 a b h2 h1).symm
      right_inv := fun f => by
        funext p
        show levMat S f p.1.1 p.1.2 = f p
        simp [levMat, p.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  simp

theorem lev_card : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N,
    Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  intro g _ N L
  set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU
  set R : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR
  have hUc : U.card = N * (N - 1) / 2 := by
    rw [hU, Finset.card_product_filter_lt, Nat.choose_two_right]
    simp
  have hRU : R ⊆ U := by
    intro p hp
    simp only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
    rw [Fin.lt_def]
    omega
  have hRc : R.card = if L.sharp = true then L.k else 0 := by
    split_ifs with h
    · have hk := L.hk
      symm
      rw [← Finset.card_range L.k]
      refine Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_
      · intro i hi
        have := Finset.mem_range.1 hi
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨by omega, by omega, trivial⟩
      · intro i hi j hj hij
        have := congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij
        simp only at this
        omega
      · intro p hp
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp
        refine ⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    · simp [hR, h]
  have hM : ∀ u : GG g N, L.Mem u ↔
      ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0) := by
    intro u
    simp only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun a b hab h => ?_⟩
      rcases lt_or_gt_of_ne hab with h' | h'
      · by_contra hne
        exact h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))
      · exact h2 a b h'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩
      refine h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)
      subst h
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by
    have := (Finset.mem_sdiff.1 hp).1
    exact (Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section AvgAux

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem avg_shift {K : Subgroup G} (M : Subgroup K) [M.Normal] [Fintype (K ⧸ M)]
    (π : Representation ℂ G V) (θ : G → ℂ) (s : K ⧸ M → K)
    (hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q) (hone : θ 1 = 1)
    (hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b)
    (w : V) (hw : ∀ m ∈ M, π (m : G) w = w) (hθM : ∀ m ∈ M, θ (m : G) = 1) (h : K) :
    ∑ q, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ∑ q, (θ (s q))⁻¹ • π (s q) w := by
  have hne : ∀ a : K, θ a ≠ 0 := by
    intro a ha
    have := hmul a a⁻¹
    rw [mul_inv_cancel, ha, zero_mul] at this
    simp [hone] at this
  have key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) =
      θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w) := by
    intro q
    set q' := q * (QuotientGroup.mk h : K ⧸ M)
    set m : K := (s q')⁻¹ * (s q * h) with hm_def
    have hmM : m ∈ M := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']
      group
    have hsplit : s q * h = s q' * m := by simp [hm_def]
    have h1 : π (s q) (π h w) = π (s q') w := by
      have : π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w := by rw [hsplit]
      simpa [map_mul, hw m hmM] using this
    have h2 : θ (s q) * θ h = θ (s q') := by
      rw [← hmul, hsplit, hmul, hθM m hmM, mul_one]
    rw [h1, smul_smul]
    congr 1
    rw [← h2]
    field_simp [hne (s q), hne h]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M))
    (fun q => (θ (s q))⁻¹ • π (s q) w)

end AvgAux

theorem aug_avg_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧
      ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  intro G V _ _ _ _ _ π hsm H θ hD u hu
  let K : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose h hh w hw using fun i => (g i).2
  have hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b := fun a b => hD.val_mul a a.2 b b.2
  let N : Subgroup K :=
    { carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i}
      mul_mem' := by
        intro a b ha hb
        refine ⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩
        simp [map_mul, ha.2 i, hb.2 i]
      one_mem' := ⟨hD.val_one, fun i => by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨?_, fun i => ?_⟩
        · have := hmul a a⁻¹
          rw [mul_inv_cancel, ha.1, one_mul] at this
          simpa [hD.val_one] using this.symm
        · have := congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)
          simpa [← map_mul] using this.symm }
  have hNopen : IsOpen (N : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds
    obtain ⟨U, hU, hUθ⟩ := hD.near
    have hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G) :=
      Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))
    have hS' := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS
    refine Filter.mem_of_superset hS' ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact ⟨hUθ x hx.1 x.2, hx.2⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)
  haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let M : Subgroup K := N.normalCore
  haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M) := Fintype.ofFinite _
  classical
  let s : K ⧸ M → K := fun q => if q = 1 then 1 else q.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp [s, hq]
  have hMN : ∀ m ∈ M, m ∈ N := fun m hm => Subgroup.normalCore_le N hm
  have hinj : Function.Injective (fun q => ((s q : K) : G)) := by
    intro a b hab
    rw [← hs a, ← hs b, Subtype.ext hab]
  refine ⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (s q).2
  · rw [Finset.sum_image fun a _ b _ hab => hinj hab]
    have hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0 := by
      intro i
      rw [hw i]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]
      have := avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i)
        (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩
      rw [this, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm]
    simp only [map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) =
        c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V)) := fun q => smul_comm _ _ _
    simp only [hc, ← Finset.smul_sum, hgen i, smul_zero]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotone
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.StripGrp

variable {k : Type} [Field k] [ValuativeRel k]

theorem triv_mono {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y :=
  fun u hu h1 => hx u hu (h1.trans h)

theorem triv_add {χ : kˣ →* ℂˣ} {x y : k} (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le h le_rfl)) hy
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le le_rfl h)) hx

theorem triv_neg {χ : kˣ →* ℂˣ} {x : k} (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono (by rw [Valuation.map_neg]) hx

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h1
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h1) zero_le'
  have hu : u = 1 := Units.ext (sub_eq_zero.mp ((Valuation.zero_iff _).mp h0))
  simp [hu]

theorem le_inv_of_mul_le {a b : ValueGroupWithZero k} (ha : a ≠ 0) (h : a * b ≤ 1) : b ≤ a⁻¹ :=
  calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left₀ ha b).symm
    _ ≤ a⁻¹ * 1 := by gcongr
    _ = a⁻¹ := mul_one _

variable {n : ℕ}

theorem ne_of_blk {r : ℕ} {i j : Fin n} (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) : i ≠ j := by
  rintro rfl; omega

theorem val_one_apply_le (i j : Fin n) : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mul_eq_zero_of_blk {r : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → A i j = 0)
    (hB : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → B i j = 0) : A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < r
  · rw [hA i l (fun h => absurd h.2 (not_le.mpr hl)), zero_mul]
  · rw [hB l j (fun h => hl h.1), mul_zero]

variable {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ}

theorem mem_strip {g : GL (Fin n) k} : g ∈ strip ψ r ϖ m ↔ ∀ i j : Fin n,
    if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := Iff.rfl

theorem sub_one_of_mem {g : GL (Fin n) k} (hg : g ∈ strip ψ r ϖ m) (i j : Fin n)
    (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : (g.val - 1) i j = 0 := by
  have := mem_strip.mp hg i j
  rw [if_neg h] at this
  simp [Matrix.sub_apply, this]

theorem one_mem : (1 : GL (Fin n) k) ∈ strip ψ r ϖ m := by
  intro i j
  split_ifs with h
  · simp only [Units.val_one, Matrix.one_apply_ne (ne_of_blk h), mul_zero, map_zero, zero_le',
      true_and]
    exact triv_zero _
  · rfl

theorem mul_mem {a b : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) (hb : b ∈ strip ψ r ϖ m) :
    a * b ∈ strip ψ r ϖ m := by
  have key : (a * b).val = 1 + (a.val - 1) + (b.val - 1) := by
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem hb)
    rw [Units.val_mul]
    calc a.val * b.val = (1 + (a.val - 1)) * (1 + (b.val - 1)) := by simp
      _ = 1 + (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  have hB := mem_strip.mp hb i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA hB
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.add_apply, Matrix.sub_apply, h1, sub_zero, zero_add]
    rw [mul_add]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le hA.1 hB.1), triv_add hA.2 hB.2⟩
  · rw [if_neg h] at hA hB
    simp only [Matrix.add_apply, Matrix.sub_apply, hA, hB, sub_self, add_zero]

theorem inv_mem {a : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) : a⁻¹ ∈ strip ψ r ϖ m := by
  have key : (a⁻¹).val = 1 - (a.val - 1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem ha)
    calc a.val * (1 - (a.val - 1)) = 1 - (a.val - 1) * (a.val - 1) := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.sub_apply, h1, sub_zero, zero_sub, mul_neg, Valuation.map_neg]
    exact ⟨hA.1, triv_neg hA.2⟩
  · rw [if_neg h] at hA
    simp only [Matrix.sub_apply, hA, sub_self, sub_zero]

theorem mono {m m' : ℕ} (hϖ : valuation k ϖ < 1) (hmm : m ≤ m') :
    strip ψ r ϖ m ⊆ strip ψ r ϖ m' := by
  intro g hg i j
  have hA := mem_strip.mp hg i j
  split_ifs with h
  · rw [if_pos h] at hA
    have hle : valuation k (ϖ ^ m' * g.val i j) ≤ valuation k (ϖ ^ m * g.val i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      gcongr ?_ * _
      exact pow_le_pow_right_of_le_one' hϖ.le hmm
    exact ⟨hle.trans hA.1, triv_mono hle hA.2⟩
  · rwa [if_neg h] at hA

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_triv (χ : kˣ →* ℂˣ) : IsClosed {x : k | Triv χ x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation k x ≠ 0 := fun h0 => hx (by
    have : x = 0 := (Valuation.zero_iff _).mp h0
    rw [this]; exact triv_zero χ)
  refine Filter.mem_of_superset ((valuation k).locally_const hx0) ?_
  intro y hy hT
  exact hx (triv_mono (le_of_eq hy.symm) hT)

theorem isClosed_strip : IsClosed (strip ψ r ϖ m) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hball : IsClosed {z : k | valuation k z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed
  have hS : IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ i j : Fin n,
      if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * A i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * A i j)
      else A i j = (1 : Matrix (Fin n) (Fin n) k) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) k => A i j :=
      (continuous_apply j).comp (continuous_apply i)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [if_pos h]
      exact (hball.inter (isClosed_triv _)).preimage (continuous_const.mul hc)
    · simp only [if_neg h]
      exact isClosed_eq hc continuous_const
  exact hS.preimage Units.continuous_val

theorem isCompact_strip (hϖ0 : ϖ ≠ 0) (hϖ : valuation k ϖ < 1) : IsCompact (strip ψ r ϖ m) := by
  set a := valuation k (ϖ ^ m) with ha_def
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hϖ0)
  have ha1 : a ≤ 1 := by rw [ha_def, map_pow]; exact pow_le_one' hϖ.le _
  have h1t : (1 : ValueGroupWithZero k) ≤ a⁻¹ := le_inv_of_mul_le ha0 (by rw [mul_one]; exact ha1)
  have hbd : ∀ g ∈ strip ψ r ϖ m, ∀ i j : Fin n, valuation k (g.val i j) ≤ a⁻¹ := by
    intro g hg i j
    have hA := mem_strip.mp hg i j
    split_ifs at hA with h
    · exact le_inv_of_mul_le ha0 (by rw [ha_def, ← map_mul]; exact hA.1)
    · rw [hA]; exact (val_one_apply_le i j).trans h1t
  refine (GlobalTheory.PairingOne.isCompact_bounded (m := Fin n) a⁻¹).of_isClosed_subset isClosed_strip ?_
  intro g hg
  exact ⟨hbd g hg, hbd g⁻¹ (inv_mem hg)⟩

theorem strip_datum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  intro k _ _ _ _ n ψ r ϖ _ hϖ0 hϖ _
  refine ⟨fun m => ⟨one_mem, fun a ha b hb => mul_mem ha hb, fun a ha => inv_mem ha,
    isCompact_strip hϖ0 hϖ, rfl, fun _ _ _ _ => (mul_one 1).symm,
    ⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩⟩, fun m m' hmm => mono hϖ hmm⟩

end GlobalTheory.StripGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
section
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
end

