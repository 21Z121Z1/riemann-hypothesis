import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IsoSplit
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem kSpan_self (F : Fin n → Fin n → Module.End ℂ V) (y : V) :
    y ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf]
  exact fun S hS => hS.1

private theorem kSpan_stb (F : Fin n → Fin n → Module.End ℂ V) (y : V) (a b : Fin n) {z : V}
    (hz : z ∈ Formalism.REAL.kSpan (fun _ => true) F y) : F a b z ∈ Formalism.REAL.kSpan (fun _ => true) F y := by
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hz ⊢
  exact fun S hS => hS.2 a b rfl z (hz S hS)

private theorem kSpan_le (F : Fin n → Fin n → Module.End ℂ V) {y : V} {Q : Submodule ℂ V}
    (hy : y ∈ Q) (hQ : Stb F Q) : Formalism.REAL.kSpan (fun _ => true) F y ≤ Q :=
  sInf_le ⟨hy, fun a b _ x hx => hQ a b x hx⟩

private theorem le_isoPart (F : Fin n → Fin n → Module.End ℂ V) {T : Set (Wt n)} {S : Submodule ℂ V}
    {y : V} {μ : Wt n} (hy : y ∈ S) (hμ : μ ∈ T) (h : KHighest (fun _ => true) F μ y) :
    Formalism.REAL.kSpan (fun _ => true) F y ≤ Formalism.REAL.isoPart (fun _ => true) F T S :=
  le_iSup₂_of_le (f := fun (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest (fun _ => true) F μ y) =>
    Formalism.REAL.kSpan (fun _ => true) F y) y ⟨hy, μ, hμ, h⟩ le_rfl

private theorem isoPart_map (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (f : Module.End ℂ V) (Q : Submodule ℂ V)
    (h : ∀ y, y ∈ S → ∀ μ ∈ T, KHighest (fun _ => true) F μ y →
      ∀ z ∈ Formalism.REAL.kSpan (fun _ => true) F y, f z ∈ Q) :
    ∀ z ∈ Formalism.REAL.isoPart (fun _ => true) F T S, f z ∈ Q := by
  have hle : Formalism.REAL.isoPart (fun _ => true) F T S ≤ Q.comap f := by
    unfold Formalism.REAL.isoPart
    refine iSup₂_le fun y hy => ?_
    obtain ⟨hyS, μ, hμ, hk⟩ := hy
    exact fun w hw => h y hyS μ hμ hk w hw
  exact fun z hz => hle hz

private theorem isoPart_stb (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V) :
    Stb F (Formalism.REAL.isoPart (fun _ => true) F T S) := fun a b =>
  isoPart_map F T S (F a b) _ fun y hy μ hμ hk z hz =>
    le_isoPart F hy hμ hk (kSpan_stb F y a b hz)

private theorem isoPart_cm (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Wt n)) (S : Submodule ℂ V)
    (B : Module.End ℂ V) (hB : Cm F S B) :
    ∀ x ∈ Formalism.REAL.isoPart (fun _ => true) F T S, B x ∈ Formalism.REAL.isoPart (fun _ => true) F T S := by
  have hc : ∀ a b x, B (F a b x) = F a b (B x) := fun a b x => LinearMap.congr_fun (hB.1 a b) x
  refine isoPart_map F T S B _ fun y hy μ hμ hk z hz => ?_
  have hkB : KHighest (fun _ => true) F μ (B y) :=
    ⟨fun a => by rw [← hc, hk.1 a, map_smul], fun a b hab he => by rw [← hc, hk.2 a b hab he, map_zero]⟩
  have hle : Formalism.REAL.kSpan (fun _ => true) F y ≤ (Formalism.REAL.kSpan (fun _ => true) F (B y)).comap B :=
    kSpan_le F (kSpan_self F (B y)) fun a b x hx => by
      rw [Submodule.mem_comap, hc]
      exact kSpan_stb F (B y) a b hx
  exact le_isoPart F (hB.2 y hy) hμ hkB (hle hz)

private theorem parts_zero {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂) {u v : V} (hu : u ∈ S₁)
    (hv : v ∈ S₂) (h : u + v = 0) : u = 0 ∧ v = 0 := by
  have hv' : v = -u := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hv1 : v ∈ S₁ := hv' ▸ S₁.neg_mem hu
  have h0 : v = 0 := (Submodule.disjoint_def.mp hd) v hv1 hv
  refine ⟨?_, h0⟩
  rw [h0, add_zero] at h
  exact h

private theorem wt_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : IsWeight F μ (y₁ + y₂)) : IsWeight F μ y₁ ∧ IsWeight F μ y₂ := by
  have key : ∀ a, F a a y₁ = ↑(μ a) • y₁ ∧ F a a y₂ = ↑(μ a) • y₂ := by
    intro a
    have e := h a
    rw [map_add, smul_add] at e
    have hz := parts_zero hd (S₁.sub_mem (s1 a a y₁ h₁) (S₁.smul_mem _ h₁))
      (S₂.sub_mem (s2 a a y₂ h₂) (S₂.smul_mem _ h₂)) (by rw [sub_add_sub_comm, e, sub_self])
    exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩
  exact ⟨fun a => (key a).1, fun a => (key a).2⟩

set_option maxHeartbeats 200000 in
private theorem hw_comp (F : Fin n → Fin n → Module.End ℂ V) {S₁ S₂ : Submodule ℂ V} (hd : Disjoint S₁ S₂)
    (s1 : Stb F S₁) (s2 : Stb F S₂) {μ : Wt n} {y₁ y₂ : V} (h₁ : y₁ ∈ S₁) (h₂ : y₂ ∈ S₂)
    (h : KHighest (fun _ => true) F μ (y₁ + y₂)) :
    KHighest (fun _ => true) F μ y₁ ∧ KHighest (fun _ => true) F μ y₂ := by
  obtain ⟨w1, w2⟩ := wt_comp F hd s1 s2 h₁ h₂ h.1
  refine ⟨⟨w1, fun a b hab e => ?_⟩, ⟨w2, fun a b hab e => ?_⟩⟩
  · have h0 := h.2 a b hab e
    rw [map_add] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).1
  · have h0 := h.2 a b hab e
    rw [map_add] at h0
    exact (parts_zero hd (s1 a b _ h₁) (s2 a b _ h₂) h0).2

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.isoSplit :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → S ≠ ⊥ → ∃ (ν : Wt n) (S₁ S₂ : Submodule ℂ V), S₁ ≠ ⊥ ∧ hw F ν ⊓ S₁ ≠ ⊥ ∧ S₁ ⊔ S₂ = S ∧ Disjoint S₁ S₂ ∧ Stb F S₁ ∧ Stb F S₂ ∧
      (∀ B, Cm F S B → Cm F S₁ B ∧ Cm F S₂ B) ∧ (∀ μ, μ ≠ ν → hw F μ ⊓ S₁ = ⊥) ∧
      ∀ μ, wsp F μ ⊓ S = (wsp F μ ⊓ S₁) ⊔ (wsp F μ ⊓ S₂) ∧ hw F μ ⊓ S = (hw F μ ⊓ S₁) ⊔ (hw F μ ⊓ S₂) := by
  intro n V _ _ F hF S hS hst hne
  have hK := Formalism.REAL.glRel_kRel (fun _ : Fin n => true) F hF.gl
  have hU : Formalism.REAL.KUnit (fun _ : Fin n => true) F := fun a b _ x y => hF.unit a b x y
  have hSt : Formalism.REAL.KStable (fun _ : Fin n => true) F S := fun a b _ x hx => hst a b x hx
  obtain ⟨x, hxS, hx0, ν, hxk⟩ := Formalism.REAL.kHiExist V n _ F S hS hK hU hSt hne
  obtain ⟨horth, hsup⟩ := Formalism.REAL.kIsoSplit V n _ F S {ν} hS hK hU hSt
  set S₁ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν} S with hS₁
  set S₂ := Formalism.REAL.isoPart (fun _ : Fin n => true) F {ν}ᶜ S with hS₂
  have hd : Disjoint S₁ S₂ := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h0 := horth v h1 v h2
    rwa [inner_self_eq_zero] at h0
  have h1S : S₁ ≤ S := hsup ▸ le_sup_left
  have h2S : S₂ ≤ S := hsup ▸ le_sup_right
  have hst1 : Stb F S₁ := isoPart_stb F _ S
  have hst2 : Stb F S₂ := isoPart_stb F _ S
  have hx1 : x ∈ S₁ := le_isoPart (T := {ν}) F hxS (Set.mem_singleton ν) hxk (kSpan_self F x)
  refine ⟨ν, S₁, S₂, ?_, ?_, hsup, hd, hst1, hst2, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx1
    exact hx0 ((Submodule.mem_bot ℂ).mp hx1)
  · intro h
    have hm : x ∈ hw F ν ⊓ S₁ := Submodule.mem_inf.mpr ⟨hxk, hx1⟩
    rw [h] at hm
    exact hx0 ((Submodule.mem_bot ℂ).mp hm)
  · intro B hB
    exact ⟨⟨hB.1, isoPart_cm F _ S B hB⟩, ⟨hB.1, isoPart_cm F _ S B hB⟩⟩
  · intro μ hμ
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyk, hy1⟩ := Submodule.mem_inf.mp hy
    have hy2 : y ∈ S₂ := le_isoPart (T := {ν}ᶜ) F (h1S hy1) (show μ ∈ ({ν}ᶜ : Set (Wt n)) from hμ) hyk (kSpan_self F y)
    exact (Submodule.mem_bot ℂ).mpr (Submodule.disjoint_def.mp hd y hy1 hy2)
  · intro μ
    constructor
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyw, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨w1, w2⟩ := wt_comp F hd hst1 hst2 h₁ h₂ hyw
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨w1, h₁⟩) (Submodule.mem_inf.mpr ⟨w2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
    · apply le_antisymm
      · intro y hy
        obtain ⟨hyk, hyS⟩ := Submodule.mem_inf.mp hy
        rw [← hsup] at hyS
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := Submodule.mem_sup.mp hyS
        obtain ⟨k1, k2⟩ := hw_comp F hd hst1 hst2 h₁ h₂ hyk
        exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨k1, h₁⟩) (Submodule.mem_inf.mpr ⟨k2, h₂⟩)
      · exact sup_le (inf_le_inf_left _ h1S) (inf_le_inf_left _ h2S)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgMulSelf
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.CartanExamples

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def sg (key : ι → ℕ) (i : ι) (A : Finset ι) : ℂ :=
  (-1) ^ (A.filter fun j => key j < key i).card

private def tw (key : ι → ℕ) (i j : ι) : ℂ := if key j < key i then -1 else 1

private theorem tw_self (key : ι → ℕ) (i : ι) : tw key i i = 1 := by simp [tw]

private theorem tw_mul_self (key : ι → ℕ) (i j : ι) : tw key i j * tw key i j = 1 := by
  unfold tw
  split_ifs <;> norm_num

private theorem tw_swap {key : ι → ℕ} (hk : Function.Injective key) {i j : ι} (h : i ≠ j) :
    tw key j i = -tw key i j := by
  have hne : key i ≠ key j := fun e => h (hk e)
  rcases lt_or_gt_of_ne hne with h1 | h1 <;> simp [tw, h1, lt_asymm h1]

private theorem sg_mul_self (key : ι → ℕ) (i : ι) (A : Finset ι) :
    sg key i A * sg key i A = 1 := by
  unfold sg
  rw [← mul_pow]
  norm_num

private theorem star_sg (key : ι → ℕ) (i : ι) (A : Finset ι) :
    star (sg key i A) = sg key i A := by
  unfold sg
  simp

private theorem sg_insert (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∉ A) :
    sg key i (insert j A) = tw key i j * sg key i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

private theorem sg_erase (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∈ A) :
    sg key i (A.erase j) = tw key i j * sg key i A := by
  have h1 := sg_insert key i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

private def al (key : ι → ℕ) (i : ι) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.of fun A A' => if i ∉ A ∧ A' = insert i A then sg key i A else 0

private theorem al_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ) (A B : Finset ι) :
    (al key i * M) A B = if i ∈ A then 0 else sg key i A * M (insert i A) B := by
  rw [Matrix.mul_apply]
  simp only [al, Matrix.of_apply]
  split_ifs with hi
  · simp [hi]
  · simp [hi]

private theorem alH_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ)
    (A B : Finset ι) :
    ((al key i)ᴴ * M) A B = if i ∈ A then sg key i A * M (A.erase i) B else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, al, Matrix.of_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single (A.erase i)]
    · rw [if_pos ⟨Finset.notMem_erase i A, (Finset.insert_erase hi).symm⟩, star_sg,
        sg_erase key i hi, tw_self, one_mul]
    · intro A' _ hA'
      rw [if_neg, star_zero, zero_mul]
      rintro ⟨h1, rfl⟩
      exact hA' (Finset.erase_insert h1).symm
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · apply Finset.sum_eq_zero
    intro A' _
    rw [if_neg, star_zero, zero_mul]
    rintro ⟨_, rfl⟩
    exact hi (Finset.mem_insert_self i A')

private theorem ann_ann {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * (al key j * M) + al key j * (al key i * M) = 0 := by
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, al_mul]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert key j hi, sg_insert key i hj, tw_swap hk hij, Finset.insert_comm j i]
  ring

private theorem ann_cre {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * ((al key j)ᴴ * M) + (al key j)ᴴ * (al key i * M) = if i = j then M else 0 := by
  ext A B
  simp only [Matrix.add_apply, al_mul, alH_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : i ∈ A
    · rw [if_pos hi, if_pos hi, if_neg (Finset.notMem_erase i A), Finset.insert_erase hi,
        sg_erase key i hi, tw_self, zero_add]
      linear_combination M A B * sg_mul_self key i A
    · rw [if_neg hi, if_neg hi, if_pos (Finset.mem_insert_self i A), Finset.erase_insert hi,
        sg_insert key i hi, tw_self, add_zero]
      linear_combination M A B * sg_mul_self key i A
  rw [if_neg hij, Matrix.zero_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, zero_add, if_pos (Finset.mem_erase.2 ⟨hij, hi⟩)]
    simp
  by_cases hj : j ∈ A
  · rw [if_neg hi, if_pos (Finset.mem_insert_of_mem hj), if_pos hj,
      if_neg (fun hm => hi (Finset.mem_of_mem_erase hm)), sg_insert key j hi, sg_erase key i hj,
      tw_swap hk hij, Finset.erase_insert_of_ne hij]
    ring
  · have h1 : j ∉ insert i A := fun hm => (Finset.mem_insert.1 hm).elim (fun e => hij e.symm) hj
    rw [if_neg hi, if_neg h1, if_neg hj]
    simp

private theorem cre_ann (key : ι → ℕ) (i : ι) :
    (al key i)ᴴ * al key i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  ext A B
  rw [alH_mul, Matrix.diagonal_apply]
  simp only [al, Matrix.of_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, if_pos hi, Finset.insert_erase hi, sg_erase key i hi, tw_self, one_mul]
    by_cases hAB : A = B
    · subst hAB
      rw [if_pos ⟨Finset.notMem_erase i A, rfl⟩, if_pos rfl, sg_mul_self]
    · rw [if_neg (fun hc => hAB hc.2.symm), if_neg hAB, mul_zero]
  · rw [if_neg hi, if_neg hi]
    simp

end UpperTheory.RealTr.CartanExamples

open UpperTheory.RealTr.CartanExamples in
theorem UpperTheory.RealTr.carEx :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∃ α : ι → Matrix (Finset ι) (Finset ι) ℂ, (∀ i j, α i * α j + α j * α i = 0) ∧
      (∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) ∧ ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  intro ι _ _
  let key : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have hk : Function.Injective key := fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)
  refine ⟨al key, fun i j => ?_, fun i j => ?_, cre_ann key⟩
  · simpa using ann_ann hk i j 1
  · simpa using ann_cre hk i j 1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Sl2Core
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem sl2Core {V : Type} [AddCommGroup V] [Module ℂ V] (E G A B : Module.End ℂ V)
    (S : Submodule ℂ V) (hfin : FiniteDimensional ℂ S)
    (hEG : ∀ v, E (G v) = G (E v) + A v - B v)
    (hAG : ∀ v, A (G v) = G (A v) - G v)
    (hBG : ∀ v, B (G v) = G (B v) + G v)
    (hS : ∀ v ∈ S, G v ∈ S) (α β : ℂ) (x : V) (hxS : x ∈ S) (hx : x ≠ 0)
    (hA : A x = α • x) (hB : B x = β • x) (hE : E x = 0) :
    ∃ m : ℕ, α - β = (m : ℂ) := by
  classical
  let v : ℕ → V := fun k => (G ^ k) x
  have hv0 : v 0 = x := by simp [v]
  have hv : ∀ k, v (k + 1) = G (v k) := by
    intro k
    simp [v, pow_succ', Module.End.mul_apply]
  have hvS : ∀ k, v k ∈ S := by
    intro k
    induction k with
    | zero => simpa [hv0] using hxS
    | succ k ih => rw [hv]; exact hS _ ih
  have hAk : ∀ k : ℕ, A (v k) = (α - k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hA]
    | succ k ih =>
      rw [hv, hAG, ih, map_smul]
      push_cast
      module
  have hBk : ∀ k : ℕ, B (v k) = (β + k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hB]
    | succ k ih =>
      rw [hv, hBG, ih, map_smul]
      push_cast
      module
  have hEk : ∀ k : ℕ, E (v (k + 1)) = (((k : ℂ) + 1) * (α - β - k)) • v k := by
    intro k
    induction k with
    | zero =>
      rw [hv, hEG, hv0, hE, hA, hB, map_zero]
      push_cast
      module
    | succ k ih =>
      rw [hv (k + 1), hEG, ih, map_smul, ← hv, hAk, hBk]
      push_cast
      module
  have hex : ∃ k, v k = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent ℂ v := by
      apply Module.End.eigenvectors_linearIndependent' A (fun k : ℕ => α - k)
      · intro i j hij
        have : (i : ℂ) = j := by simpa using hij
        exact_mod_cast this
      · intro i
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hAk i, hne i⟩
    let w : ℕ → S := fun k => ⟨v k, hvS k⟩
    have hliw : LinearIndependent ℂ w := by
      apply LinearIndependent.of_comp S.subtype
      exact hli
    have : Finite ℕ := hliw.finite
    exact not_finite ℕ
  have hk : v (Nat.find hex) = 0 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hx
    rw [← hv0, ← h0]
    exact hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hvm : v m ≠ 0 := Nat.find_min hex (by omega)
  have hvm1 : v (m + 1) = 0 := by
    rw [show m + 1 = Nat.find hex by omega]
    exact hk
  have h := hEk m
  rw [hvm1, map_zero] at h
  have hc : ((m : ℂ) + 1) * (α - β - m) = 0 := by
    by_contra hc
    exact hvm ((smul_eq_zero.mp h.symm).resolve_left hc)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have := (mul_eq_zero.mp hc).resolve_left hm1
  linear_combination this

theorem UpperTheory.RealTr.hwDom :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (ν : Wt n), ∀ x ∈ S, x ≠ 0 → x ∈ hw F ν → Dom ν := by
  intro n V _ _ F hUF S hfin hStb ν x hxS hx hxw
  have hk : KHighest (fun _ => true) F ν x := hxw
  have hgl : GlRel F := hUF.gl
  intro a b hab
  have hne : a ≠ b := ne_of_lt hab
  have hEG : ∀ v, F a b (F b a v) = F b a (F a b v) + F a a v - F b b v := by
    intro v
    have h := LinearMap.congr_fun (hgl a b b a) v
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hAG : ∀ v, F a a (F b a v) = F b a (F a a v) - F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl a a b a) v
    simp only [if_neg hne, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hBG : ∀ v, F b b (F b a v) = F b a (F b b v) + F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl b b b a) v
    simp only [if_neg hne, if_neg hne.symm, if_true, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hS : ∀ v ∈ S, F b a v ∈ S := fun v hv => hStb b a v hv
  obtain ⟨m, hm⟩ := sl2Core (F a b) (F b a) (F a a) (F b b) S hfin hEG hAG hBG hS
    (ν a : ℂ) (ν b : ℂ) x hxS hx (hk.1 a) (hk.1 b) (hk.2 a b hab rfl)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
end
end

