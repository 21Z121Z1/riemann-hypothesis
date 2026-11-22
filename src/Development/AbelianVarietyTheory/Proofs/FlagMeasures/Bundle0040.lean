import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem exists_invol {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → Eˣ),
      (∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum → σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a) ∧
      (∀ a b, a < (bs.map (fun b => (b.2 : ℕ))).sum → b < (bs.map (fun b => (b.2 : ℕ))).sum →
        ptEntryL bs a b = if b = σ a then (t a : E) else 0) ∧
      (∀ c, c + 1 < (bs.map (fun b => (b.2 : ℕ))).sum →
        (σ c = σ (c + 1) + 1 ∧ t (c + 1) = t c) ∨ σ c < σ (c + 1)) := by
  induction bs with
  | nil => exact ⟨id, 1, by simp, by simp, by simp⟩
  | cons p bs ih =>
    obtain ⟨u, s⟩ := p
    obtain ⟨σ, t, h1, h2, h3⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = m at h1 h2 h3 ⊢
    refine ⟨fun a => if a < s then s - 1 - a else s + σ (a - s),
      fun a => if a < s then u else t (a - s), fun a ha => ?_, fun a b ha hb => ?_, fun c hc => ?_⟩
    · by_cases h : a < s
      · have h' : (s : ℕ) - 1 - a < s := by omega
        simp only [if_pos h, if_pos h']
        omega
      · obtain ⟨h4, h5⟩ := h1 (a - s) (by omega)
        have h' : ¬ (s : ℕ) + σ (a - s) < s := by omega
        simp only [if_neg h, if_neg h', Nat.add_sub_cancel_left, h5]
        omega
    · simp only [ptEntryL]
      by_cases h : a < s
      · simp only [if_pos h]
        by_cases h' : b < s
        · rw [if_pos ⟨h, h'⟩]
          exact if_congr (by omega) rfl rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · simp only [if_neg h]
        rw [if_neg (by omega)]
        by_cases h' : b < s
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), h2 _ _ (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
    · by_cases h : c + 1 < s
      · have h' : c < s := by omega
        simp only [if_pos h, if_pos h']
        exact Or.inl ⟨by omega, trivial⟩
      · by_cases h' : c < s
        · simp only [if_neg h, if_pos h']
          exact Or.inr (by omega)
        · simp only [if_neg h, if_neg h']
          have e : c + 1 - s = c - s + 1 := by omega
          rw [e]
          rcases h3 (c - s) (by omega) with ⟨h4, h5⟩ | h4
          · exact Or.inl ⟨by omega, h5⟩
          · exact Or.inr (by omega)

theorem simple_sum {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by
  obtain ⟨σ₀, t, h1, h2, h3⟩ := exists_invol w.blocks
  rw [w.size] at h1 h2 h3
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ₀ a, (h1 a a.2).1⟩
  have hinv : Function.Involutive σ' := fun a => Fin.ext (h1 a a.2).2
  let σ : Fin (r + 1) ≃ Fin (r + 1) := hinv.toPerm
  have hσ : ∀ a, (σ a : ℕ) = σ₀ a := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := hinv
  let z : Fin (r + 1) → Eˣ := fun a => t a * (-1) ^ (r - (σ a : ℕ))
  have hZ' : ∀ a b, Z a b = if b = σ a then (z a : E) else 0 := by
    intro a b
    rw [hZ, Pt.mat, h2 _ _ a.2 b.2]
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]; simp [z]
    · rw [if_neg hb, if_neg (fun e : (b : ℕ) = σ₀ a => hb (Fin.ext e)), zero_mul]
  have key : ∀ a c, A a c * z c = z a * C (σ a) (σ c) := by
    intro a c
    have := h a (σ c)
    simpa [hZ'] using this
  have term : ∀ a c : Fin (r + 1), (if (a : ℕ) = c + 1 then A a c else 0) =
      -(if (σ c : ℕ) = σ a + 1 then C (σ a) (σ c) else 0) := by
    intro a c
    by_cases hac : (a : ℕ) = c + 1
    · rw [if_pos hac]
      rcases h3 c (hac ▸ a.2) with ⟨h4, h5⟩ | h4
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [← hac] at h5
        rw [if_pos h4]
        have hz : z a = -z c := by
          have := (σ c).2
          have e : r - (σ a : ℕ) = r - (σ c : ℕ) + 1 := by omega
          simp only [z, e, h5, pow_succ]
          simp
        have := key a c
        rw [hz, Units.val_neg, mul_comm, neg_mul, ← mul_neg] at this
        exact (Units.mul_right_inj _).1 this
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [if_neg (by omega), neg_zero]
        have := key a c
        rw [hC _ _ h4, mul_zero] at this
        exact (Units.mul_left_eq_zero _).1 this
    · rw [if_neg hac]
      by_cases h4 : (σ c : ℕ) = σ a + 1
      · rw [if_pos h4]
        have h5 := h3 (σ a) (h4 ▸ (σ c).2)
        rw [← h4, ← hσ, ← hσ, hσσ, hσσ] at h5
        have h6 : a < c := by
          rcases h5 with ⟨h5, -⟩ | h5
          · exact absurd h5 hac
          · exact h5
        have := key a c
        rw [hA _ _ h6, zero_mul] at this
        rw [(Units.mul_right_eq_zero _).1 this.symm, neg_zero]
      · rw [if_neg h4, neg_zero]
  have hs : ∀ M : Fin (r + 1) → Fin (r + 1) → E,
      ∑ a : Fin (r + 1), ∑ c : Fin (r + 1), (if (a : ℕ) = c + 1 then M a c else 0) =
        ∑ j : Fin r, M j.succ j.castSucc := by
    intro M
    rw [Fin.sum_univ_succ]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun (c : Fin (r + 1)) _ =>
      if_neg (show ¬ ((0 : Fin (r + 1)) : ℕ) = c + 1 by simp)), zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.castSucc]
    · simp
    · intro b _ hb
      exact if_neg fun e => hb (Fin.ext (Nat.add_right_cancel e).symm)
    · simp
  rw [← hs A, ← hs (fun a c => C c a)]
  simp only [term, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm, ← σ.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← σ.sum_comp]
  simp only [hσσ]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem hf_sum_l {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm (∑ i, c i • v i) y = ∑ i, c i * hf L S.Hm (v i) y := by
  classical
  refine Finset.induction_on Finset.univ (by simp [hf]) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]

theorem hf_sum_r {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm y (∑ i, c i • v i) = ∑ i, L.cj (c i) * hf L S.Hm y (v i) := by
  rw [← hf_cj L S.herm.1, hf_sum_l, map_sum]
  simp only [map_mul, hf_cj L S.herm.1]

theorem coef_eq (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) (n : S.GLV)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : ∀ j, n (g j) = ∑ i, s i j • g i) (j : Fin r) :
    S.coef g gs n j = s j.castSucc j.succ := by
  simp [Frames.coef, Frames.h, hs, hf_sum_l, dual]

end

theorem psi_eq_psi' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := exists_matrix S S.f S.T S.gram h hh.1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := exists_matrix S S.f' S.T' S.gram' h hh.2
  obtain ⟨C, ⟨hC0, hC1⟩, hC⟩ := exists_matrix S S.f' S.T' S.gram' h⁻¹ (inv_mem hh.2)
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hh.1.1.1
  have hcan : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hneg : ∀ j : Fin r, s' j.castSucc j.succ = -C j.castSucc j.succ := by
    intro j
    have e : hf L S.Hm (h (h⁻¹ (S.f' j.succ))) (S.es' j) = 0 := by
      rw [hcan, S.dual', if_neg (Fin.castSucc_lt_succ (i := j)).ne']
    rw [hC, map_sum] at e
    simp only [map_smul, hf_sum_l] at e
    simp only [hs', hf_sum_l, S.dual', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    rw [Finset.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne, hs1', hC1] at e
    · linear_combination e
    · rintro i - ⟨h1, h2⟩
      by_cases hi : i < j.castSucc
      · rw [hs0' _ _ hi, mul_zero]
      · rw [hC0, zero_mul]
        have h1' : (i : ℕ) ≠ j := fun e => h1 (Fin.ext e)
        have h2' : (i : ℕ) ≠ j + 1 := fun e => h2 (Fin.ext e)
        have h3' : ¬ (i : ℕ) < j := hi
        change (j : ℕ) + 1 < i
        omega
    · simp
    · simp
  have main := simple_sum S.w S.Zh (cT L s) C S.relevant
    (fun i j hij => by rw [cT, hs0 _ _ hij, map_zero]) hC0 (fun a b => by
      have e := hiso (h⁻¹ (S.f' b)) (S.f a)
      rw [hcan, hs, hC, hf_sum_l, hf_sum_r] at e
      simpa [cT, Frames.Zh, Frames.h, mul_comm] using e)
  have e : ∑ j, S.coef S.f' S.es' h j = L.cj (∑ j, S.coef S.f S.es h j) := by
    simp only [coef_eq S _ _ S.dual h s hs, coef_eq S _ _ S.dual' h s' hs', hneg, map_sum,
      Finset.sum_neg_distrib]
    exact main.symm
  simp only [Frames.psi, Frames.psi', Frames.psiOf]
  rw [e, ← L.local_additive_char_conj, map_mul, AlgEquiv.commutes]

end GlobalTheory.HL.CharAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (n : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ n • Λ ↔ ∃ y ∈ Λ, n y = x :=
  Submodule.mem_smul_pointwise_iff_exists x n Λ

theorem smul_eq_map (n : S.GLV) (Λ : Submodule L.O S.V) :
    n • Λ = Λ.map (n.toLinearMap.restrictScalars L.O) := by
  ext x
  rw [mem_smul, Submodule.mem_map]
  rfl

theorem isSD_smul {n : S.GLV} (hn : n ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (n • Λ) := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hn' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hn
  refine ⟨⟨by rw [smul_eq_map]; exact hfg.map _, ?_⟩, fun y => ?_⟩
  · have : ((n • Λ : Submodule L.O S.V) : Set S.V) = n.toLinearMap '' (Λ : Set S.V) := by
      rw [smul_eq_map]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨y, rfl⟩ := n.surjective y
    constructor
    · intro h
      refine (mem_smul S n Λ _).2 ⟨y, (hd y).1 fun x hx => ?_, rfl⟩
      rw [← hn']
      exact h _ ((mem_smul S n Λ _).2 ⟨x, hx, rfl⟩)
    · intro h x hx
      obtain ⟨y', hy', e⟩ := (mem_smul S n Λ _).1 h
      obtain ⟨x', hx', rfl⟩ := (mem_smul S n Λ _).1 hx
      rw [← e, hn']
      exact (hd y').2 hy' x' hx'

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem self_mem (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j := Submodule.subset_span ⟨i, h, rfl⟩

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  rw [Frames.spanTo, hs, Set.image_univ]

section
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg

theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) : n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨-, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine h3.2 _ ?_
    rw [Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
    exact hg _
  · exact (Subgroup.mem_iInf.1 h2 i).2 _ (self_mem S g (by simp))

theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {x : S.V} (hx : x ∈ S.spanTo g j) :
    n x ∈ S.spanTo g j := by
  have : S.spanTo g j ≤ (S.spanTo g j).comap n.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (S.spanTo g j).add_mem (spanTo_mono S g (le_of_lt hi) (sub_mem hg hn i))
      (self_mem S g hi)
    rw [sub_add_cancel] at h1
    exact h1
  exact this hx

theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (x : S.V) :
    n x ∈ S.spanTo g j ↔ x ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem hg hn j⟩
  have := map_mem hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n x) = x := n.symm_apply_apply x
  rwa [e] at this

theorem trace_smul {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V} {j : ℕ}
    (h : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) (x : S.V) :
    (x ∈ n • Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) := by
  have e : Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) =
      n • Submodule.span L.O (g '' {i | (i : ℕ) < j}) := by
    rw [smul_eq_map, Submodule.map_span, Set.image_image]; rfl
  rw [e, mem_smul, mem_smul]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    exact ⟨y, (h y).1 ⟨hy, (map_mem_iff hg hn j y).1 h2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, ((h y).2 hy).1, rfl⟩, map_mem hg hn j ((h y).2 hy).2⟩

end

theorem inner_smul {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (x : S.V) :
    (∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) ↔
      ∃ y ∈ n • Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, (mem_smul S n Λ _).2 ⟨y, hy, rfl⟩, (h1 y).2 hp, ?_⟩
    have := (S.spanTo g r).add_mem (h2 y hp) hx
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨_, hy, hp, hx⟩
    obtain ⟨y, hy0, rfl⟩ := (mem_smul S n Λ _).1 hy
    refine ⟨y, hy0, (h1 y).1 hp, ?_⟩
    have := (S.spanTo g r).sub_mem hx (h2 y ((h1 y).1 hp))
    rwa [sub_sub_sub_cancel_left] at this

theorem term_basic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hW : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dif_pos hT]
    exact hT.choose_spec
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  have det : ∀ d : S.Datum, S.IsTerm d Λ →
      (∀ x, x ∈ d.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f r) ∧ y - x ∈ S.spanTo S.f r) ∧
      (∀ x, x ∈ d.2.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f' r) ∧ y - x ∈ S.spanTo S.f' r) ∧
      d.2.2 = S.graphOf Λ := by
    rintro d ⟨p, hA, hA', hn, hn', e, e', -, hgr⟩
    refine ⟨fun x => ?_, fun x => ?_, hgr⟩
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 x, inner_smul S hn, ← e]
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 x, inner_smul S hn', ← e']
  obtain ⟨hA, hA', hn, hn', e, e', hth', hgr⟩ := id hW
  obtain ⟨s1, s2, -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨-, s2', -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := isSD_smul S hn.1.1 s1
    rwa [← e] at this
  have t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔
      x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg hn (s2 j hj) x
    rwa [← e] at this
  have t' : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔
      x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg' hn' (s2' j hj) x
    rwa [← e'] at this
  have m : ∀ b, S.fr d Λ b ∈ Λ ∧ S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    (t _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  have m' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (t' _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  refine ⟨hSD, hW, ?_, t, t', ?_, ⟨⟨_, hn, _, hn', rfl⟩, ?_⟩, fun d' hd' => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(m b).1, Submodule.mem_sup_left (m b).2⟩
    · refine ⟨?_, S.ME.smul_mem _ (S.ME.sub_mem (Submodule.mem_sup_right (m' b).2)
        (Submodule.mem_sup_left (m b).2))⟩
      obtain ⟨y, hy, e2⟩ := hth' b
      have e3 : S.fr' d Λ b - S.fr d Λ b = algebraMap F E S.th • y := e2
      simp only [e3, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      exact hy
  · obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
    refine LinearIndependent.sum_type (l1.map' (S.wit d Λ).1.toLinearMap (LinearEquiv.ker _))
      (l2.map' (S.wit d Λ).2.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m b).2
      rw [spanTo_top] at this
      exact this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m' b).2
      rw [spanTo_top] at this
      exact this
  · rintro p ⟨A, A', hi, hi', -, -, -, h1, h2⟩ a b
    refine (hSD.2 _).2 ?_ _ ?_
    · rw [h1]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi i a⟩ : L.O) (m i).1
    · rw [h2]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi' i b⟩ : L.O) (m' i).1
  · obtain ⟨a1, a2, a3⟩ := det d hT
    obtain ⟨b1, b2, b3⟩ := det d' hd'
    exact Prod.ext (Submodule.ext fun x => (b1 x).trans (a1 x).symm)
      (Prod.ext (Submodule.ext fun x => (b2 x).trans (a2 x).symm) (b3.trans a3.symm))

end GlobalTheory.HL.TermBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqMeanOverRepresentatives
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma eq_of_mem_finset_of_mk_eq {A B : AddSubgroup W} {R : Finset W}
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B)
    {x y : W} (hx : x ∈ R) (hy : y ∈ R) (h : (x : W ⧸ B) = y) : x = y := by
  have hxy : -x + y ∈ B := QuotientAddGroup.eq.mp h
  obtain ⟨z, _, hz⟩ := hR y (hRA y hy)
  have h1 := hz y ⟨hy, by simp⟩
  have h2 := hz x ⟨hx, by rwa [sub_eq_neg_add]⟩
  exact h2.trans h1.symm

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma exists_mem_finset_mk_eq_of_mem {A B : AddSubgroup W} {R : Finset W}
    (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) {w : W} (hw : w ∈ A) :
    ∃ x ∈ R, (x : W ⧸ B) = w := by
  obtain ⟨x, ⟨hx, hwx⟩, _⟩ := hR w hw
  refine ⟨x, hx, QuotientAddGroup.eq.mpr ?_⟩
  rw [← sub_eq_neg_add]
  exact hwx

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma apply_eq_of_quotient_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) {u v : W} (h : (u : W ⧸ B) = v) : φ u = φ v := by
  have hb : -u + v ∈ B := QuotientAddGroup.eq.mp h
  have := hinv u (-u + v) hb
  rwa [add_neg_cancel_left, eq_comm] at this

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in

theorem _root_.GlobalTheory.IdxInt.cint_eq_mean_reps {W : Type} [AddCommGroup W]
    (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W)
    (hBA : B ≤ A) (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (hsupp : ∀ w, w ∉ A → φ w = 0)
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) :
    _root_.GlobalTheory.IdxInt.Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧
      _root_.GlobalTheory.IdxInt.cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  have hmemA : ∀ w, φ w ≠ 0 → w ∈ A := fun w hw => by
    by_contra h
    exact hw (hsupp w h)
  have hcard : (R.card : ℕ) = B.relIndex A := by
    let f : R → A ⧸ B.addSubgroupOf A := fun x => ((⟨x.1, hRA x.1 x.2⟩ : A) : A ⧸ B.addSubgroupOf A)
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        have h' : -(⟨x, hRA x hx⟩ : A) + ⟨y, hRA y hy⟩ ∈ B.addSubgroupOf A :=
          QuotientAddGroup.eq.mp h
        rw [AddSubgroup.mem_addSubgroupOf] at h'
        have h'' : -x + y ∈ B := by simpa using h'
        exact Subtype.ext (eq_of_mem_finset_of_mk_eq hRA hR hx hy (QuotientAddGroup.eq.mpr h''))
      · intro c
        induction c using QuotientAddGroup.induction_on with
        | H a =>
          obtain ⟨x, ⟨hx, hax⟩, _⟩ := hR a.1 a.2
          refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.mpr ?_⟩
          rw [AddSubgroup.mem_addSubgroupOf]
          have : -x + a.1 ∈ B := by rwa [← sub_eq_neg_add]
          simpa using this
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr (Equiv.ofBijective f hf),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : R.card ≠ 0 := by
    obtain ⟨x, ⟨hx, _⟩, _⟩ := hR 0 A.zero_mem
    exact Finset.card_ne_zero_of_mem hx
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := by
    unfold _root_.GlobalTheory.IdxInt.Fine
    refine ⟨hBA, hcard ▸ hne, fun w b hb => hinv w b hb, ?_⟩
    refine (R.finite_toSet.image (QuotientAddGroup.mk : W → W ⧸ B)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hxw⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA w hw)
    exact ⟨x, hx, hxw⟩
  refine ⟨hfine, hcard, ?_⟩
  have hsum : ∑ᶠ c : W ⧸ B, φ (Quotient.out c) = ∑ w ∈ R, φ w := by
    rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientAddGroup.mk : W → W ⧸ B)) _ ?_]
    · rw [Finset.sum_image (fun x hx y hy h => eq_of_mem_finset_of_mk_eq hRA hR hx hy h)]
      exact Finset.sum_congr rfl fun x _ => apply_eq_of_quotient_mk_eq_of_invariant hinv (QuotientAddGroup.out_eq' _)
    · intro c hc
      obtain ⟨x, hx, hxc⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA _ hc)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, hxc.trans (QuotientAddGroup.out_eq' c)⟩
  rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, ← hcard]

end GlobalTheory.IdxInt
end

