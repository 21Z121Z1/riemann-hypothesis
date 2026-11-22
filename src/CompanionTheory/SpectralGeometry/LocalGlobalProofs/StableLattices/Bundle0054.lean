import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0044
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos Cn ann cre lift)
open CompanionTheory.RgExh.U
open GlobalTheory.CompanionTheory.FarReg.BdProd (adL_cre)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_mul_cre (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * cre g : Module.End ℂ (Cn n V)) = cre g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre φ g x

theorem lift_mul_ann (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * ann g : Module.End ℂ (Cn n V)) = ann g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_ann φ g x

theorem lift_mul_adL (φ : Module.End ℂ V) (p q : Fin n) :
    (lift n φ * adL p q : Module.End ℂ (Cn n V)) = adL p q * lift n φ := by
  simp only [adL, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, lift_mul_cre, mul_assoc, lift_mul_ann, mul_assoc]

theorem term_ann (k i g : Pos n) :
    (ann g * (cre k * ann i) - cre k * ann i * ann g : Module.End ℂ (Cn n V)) = if k = g then ann i else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) g k
  have h2 := CompanionTheory.D.LK.Car.ann_ann (V := V) g i
  rw [← mul_assoc, eq_sub_of_add_eq h1, sub_mul, mul_assoc (cre k) (ann g), eq_neg_of_add_eq_zero_left h2]
  by_cases e : k = g
  · subst e
    simp [mul_assoc]
  · have e' : ¬g = k := fun h => e h.symm
    simp [e, e', mul_assoc]

theorem adL_ann (p q : Fin n) (g : Pos n) :
    (∑ i : Pos n, adC p q i g • ann i : Module.End ℂ (Cn n V)) = ann g * adL p q - adL p q * ann g := by
  have h : (ann g * adL p q - adL p q * ann g : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (ann g * (cre k * ann i) - cre k * ann i * ann g) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_ann]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single g]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem adL_comm (p q r v : Fin n) :
    (adL p q * adL r v - adL r v * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ l : Pos n,
        (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • (cre l * ann i) := by
  have gen : ∀ A : Module.End ℂ (Cn n V), A * adL r v - adL r v * A =
      ∑ i : Pos n, ∑ k : Pos n, adC r v i k • (A * (cre k * ann i) - cre k * ann i * A) := by
    intro A
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  have h1 : ∀ k i : Pos n, (adL p q * (cre k * ann i) - cre k * ann i * adL p q : Module.End ℂ (Cn n V)) =
      (∑ l : Pos n, adC p q k l • cre l) * ann i - cre k * ∑ m : Pos n, adC p q m i • ann m := by
    intro k i
    rw [← adL_cre, adL_ann]
    noncomm_ring
  rw [gen]
  simp only [h1, smul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  · refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]

def dl (a b : Fin n) : ℂ := if a = b then 1 else 0

def cc (p q : Fin n) (s t : Fin n × Fin n) : ℂ :=
  dl q s.1 * dl t.1 p * dl t.2 s.2 - dl s.2 p * dl t.1 s.1 * dl t.2 q

theorem ite3 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if A ∧ B ∧ C then 1 else 0 : ℂ) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> simp [a, b, c]

theorem adC_eq (p q : Fin n) (i k : Pos n) : adC p q i k = cc p q i.1 k.1 := by
  have e1 : ∀ a b : Fin n × Fin n, a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := fun a b => Prod.ext_iff
  simp only [adC, cc, dl, e1 k.1, ite3]

theorem ite_dl (a b : Fin n) (x : ℂ) : (if a = b then x else 0) = dl a b * x := by
  by_cases h : a = b <;> simp [dl, h]

theorem sum_at (f : Fin n × Fin n → ℂ) (s : Fin n × Fin n) (hs : (s.1 : ℕ) < s.2) :
    ∑ k : Pos n, (if k.1 = s then f k.1 else 0) = f s := by
  have e : ∀ k : Pos n, k.1 = s ↔ k = ⟨s, hs⟩ := fun k => (Subtype.ext_iff (a1 := k) (a2 := ⟨s, hs⟩)).symm
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]

theorem sum_adC {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) {i : Pos n}
    (hi : inU lev i) (f : Fin n × Fin n → ℂ) :
    ∑ k : Pos n, adC p q i k * f k.1 =
      dl q i.1.1 * f (p, i.1.2) - dl i.1.2 p * f (i.1.1, q) := by
  have a1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1 = (p, i.1.2) then 1 else 0) * f k.1 = dl q i.1.1 * f (p, i.1.2) := by
    by_cases h : q = i.1.1
    · have hs : (p : ℕ) < i.1.2 := by
        have : lev p < lev i.1.2 := by rw [hpq, h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (p, i.1.2) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  have a2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1 = (i.1.1, q) then 1 else 0) * f k.1 = dl i.1.2 p * f (i.1.1, q) := by
    by_cases h : i.1.2 = p
    · have hs : (i.1.1 : ℕ) < q := by
        have : lev i.1.1 < lev q := by rw [← hpq, ← h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (i.1.1, q) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  simp only [adC, sub_mul, Finset.sum_sub_distrib, a1, a2]

theorem mat_id {lev : Fin n → ℕ} (hm : Monotone lev) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v)
    {i : Pos n} (hi : inU lev i) (l : Pos n) :
    ∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l) =
      (if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0) := by
  have h1 := sum_adC hm hrv hi (fun s => cc p q s l.1)
  have h2 := sum_adC hm hpq hi (fun s => cc r v s l.1)
  simp only [← adC_eq] at h1 h2
  rw [Finset.sum_sub_distrib, h1, h2, ite_dl, ite_dl]
  simp only [adC_eq, cc]
  ring

theorem ann_eq_zero {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) {i : Pos n} (hi : ¬inU lev i) :
    ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem adL_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cn n V} (hx : SuppIn (inU lev) x)
    {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    adL p q (adL r v x) - adL r v (adL p q x) =
      (if q = r then adL p v x else 0) - (if v = p then adL r q x else 0) := by
  have h := LinearMap.congr_fun (adL_comm (V := V) p q r v) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  have e : ∀ a b : Fin n, (adL a b x : Cn n V) = ∑ i : Pos n, ∑ l : Pos n, adC a b i l • cre l (ann i x) := by
    intro a b
    simp [adL, LinearMap.sum_apply, Module.End.mul_apply]
  have t : ∀ i l : Pos n,
      (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • cre l (ann i x) =
      ((if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0)) • cre l (ann i x) := by
    intro i l
    by_cases hi : inU lev i
    · rw [mat_id hm hpq hrv hi]
    · rw [ann_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [e]
    · simp
  · split_ifs
    · rw [e]
    · simp

end GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem lF_glRel : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  intro n lev V _ _ E hm hE x hx p q r v hpq hrv
  have hA := LetterGl.adL_comm_apply hm hx hpq hrv
  have h1 : ∀ y : Cn n V, lift n (E p q) (adL r v y) = adL r v (lift n (E p q) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E p q) r v) y
  have h2 : ∀ y : Cn n V, lift n (E r v) (adL p q y) = adL p q (lift n (E r v) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E r v) p q) y
  have hL : lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x) =
      (if q = r then lift n (E p v) x else 0) - (if v = p then lift n (E r q) x else 0) := by
    funext A
    have := LinearMap.congr_fun (hE p q r v) (x A)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [Pi.sub_apply, CompanionTheory.D.LK.lift_apply]
    rw [this]
    split_ifs <;> simp
  simp only [lF, LinearMap.add_apply, map_add, h1, h2]
  calc _ = (lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x)) +
        (adL p q (adL r v x) - adL r v (adL p q x)) := by abel
    _ = _ := by
      rw [hL, hA]
      split_ifs <;> abel

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.PSubFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def Pm (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def Pp (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem mem_Vm {x : Fin n → ℂ} : x ∈ Vm A ↔ ∃ z, Pm A *ᵥ z = x := by
  simp only [Vm, LinearMap.mem_range, Matrix.toLin'_apply, Pm]

theorem mem_Wm {y : Fin n → ℂ} : y ∈ Wm A ↔ Pp A *ᵥ y = 0 := by
  simp only [Wm, LinearMap.mem_ker, Matrix.toLin'_apply, Pp]

theorem anti (hA : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  have h := hA.1
  unfold Formalism.REAL.inG at h
  rw [hA.2.1] at h
  exact eq_neg_of_add_eq_zero_right h

theorem Pm_conj (hA : IsGrad ε A) : (Pm A)ᴴ = Pm A := by
  simp [Pm, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]

theorem Pm_J (hA : IsGrad ε A) : Pm A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pp A := by
  have h := anti hA
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  simp only [Pm, Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h, h2, sub_eq_add_neg, Matrix.neg_mul]

theorem Pp_Pm (hA : IsGrad ε A) : Pp A * Pm A = 0 := by
  have h := hA.2.2.1
  have e : (A * A + A) * (A * A - A) = 0 := by
    have : (A * A + A) * (A * A - A) = (A * A * A) * A - A * A := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, h, sub_self]
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, e, smul_zero]

theorem Vm_le_Wm (hA : IsGrad ε A) : Vm A ≤ Wm A := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_Vm.1 hx
  rw [mem_Wm, Matrix.mulVec_mulVec, Pp_Pm hA, Matrix.zero_mulVec]

theorem mem_Wm_iff (hA : IsGrad ε A) (y : Fin n → ℂ) :
    y ∈ Wm A ↔ ∀ x ∈ Vm A, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  have key : ∀ z, star (Pm A *ᵥ z) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y)) := by
    intro z
    rw [Matrix.star_mulVec, Pm_conj hA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Pm_J hA,
      Matrix.mulVec_mulVec]
  constructor
  · intro hy x hx
    obtain ⟨z, rfl⟩ := mem_Vm.1 hx
    rw [key, mem_Wm.1 hy, Matrix.mulVec_zero, dotProduct_zero]
  · intro h
    have h1 := h _ (mem_Vm.2 ⟨Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y), rfl⟩)
    rw [key, dotProduct_star_self_eq_zero] at h1
    have h2 := congrArg (Formalism.REAL.Jm ε *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, ← Matrix.mul_assoc, Matrix.one_mul, Matrix.mulVec_zero] at h2
    exact mem_Wm.2 h2

theorem isoFlag (hA : IsGrad ε A) : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all [W]
  · intro i
    fin_cases i
    show Module.finrank ℂ (Vm A) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + rk A
    simp [rk]
  · intro x hx y hy
    exact (mem_Wm_iff hA y).1 (Vm_le_Wm hA hy) x hx

theorem keeps_of_stable (g : Formalism.REAL.UJ ε) {S : Submodule ℂ (Fin n → ℂ)} (h : ∀ y ∈ S, uMat g *ᵥ y ∈ S) :
    Keeps (uMat g) S :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul g) S)

theorem stable_of_keeps {g : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)} (h : Keeps g S) :
    ∀ y ∈ S, g *ᵥ y ∈ S := fun y hy => by
  have : Matrix.toLin' g y ∈ S.map (Matrix.toLin' g) := Submodule.mem_map_of_mem hy
  rw [h, Matrix.toLin'_apply] at this
  exact this

theorem flagN_fix {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat u *ᵥ y = y := by
  have h : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hu.1 0 y hy
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h)

theorem flagN_stable_Wm (hA : IsGrad ε A) {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat u *ᵥ y ∈ Wm A := by
  have h : uMat u *ᵥ y - y ∈ Vm A := hu.2 y ((mem_Wm_iff hA y).1 hy)
  have := add_mem (Vm_le_Wm hA h) hy
  simpa using this

theorem flagM_stable_Vm {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat m *ᵥ y ∈ Vm A :=
  (hm 1 y hy).1

theorem flagM_stable_Wm (hA : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat m *ᵥ y ∈ Wm A := by
  refine (mem_Wm_iff hA _).2 fun x hx => ?_
  have hx' : uMat m⁻¹ *ᵥ x ∈ Vm A :=
    GlobalTheory.RealIwasawa.inv_stable _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul m) (Vm A)
      (fun z hz => flagM_stable_Vm hm hz) x hx
  have e : x = uMat m *ᵥ (uMat m⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv, Matrix.one_mulVec]
  have h0 := (mem_Wm_iff hA y).1 hy _ hx'
  rw [e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    GlobalTheory.RealIwasawa.uMat_form]
  exact h0

theorem psubEq : PSubEq := by
  intro n ε A hA g
  constructor
  · intro hg
    have hp : ∀ i, ∀ y ∈ W A i, uMat g *ᵥ y ∈ W A i := by
      intro i y hy
      fin_cases i
      · have : y = 0 := (Submodule.mem_bot ℂ).1 hy
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      · exact stable_of_keeps hg.1 y hy
    obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) g hp
    exact ⟨g * m⁻¹, hu, m, hm, by group⟩
  · rintro ⟨u, hu, m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · exact keeps_mul (keeps_of_stable u fun y hy => by rw [flagN_fix hu hy]; exact hy)
        (keeps_of_stable m fun y hy => flagM_stable_Vm hm hy)
    · exact keeps_mul (keeps_of_stable u fun y hy => flagN_stable_Wm hA hu hy)
        (keeps_of_stable m fun y hy => flagM_stable_Wm hA hm hy)

end GlobalTheory.CompanionTheory.PSubFlag
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GroundTheory.BlockD.FourierDecayAlt.GaugeExists (qdetPoly tmPoly evU evU_apply evU_qdetPoly natDegree_qdetPoly_le
  coeff_qdetPoly_top prod_linear sum_fin_cast)

section Poly

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem poly_eq_zero_of_evU (Q : A[X]) (h : ∀ u : ℂ, evU u Q = 0) : Q = 0 := by
  ext j
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let R : ℂ[X] := ∑ k ∈ range (Q.natDegree + 1), monomial k (φ (Q.coeff k))
  have hR : R = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 := congrArg φ (h u)
    rw [evU_apply, eval₂_eq_sum_range, map_sum, map_zero] at h1
    rw [eval_zero, ← h1]
    simp only [R, eval_finset_sum, eval_monomial, RingHom.id_apply, ← map_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h2 := congrArg (fun p => p.coeff j) hR
  simp only [R, finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', mem_range] at h2
  split_ifs at h2 with hj
  · exact h2
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem commute_coeff_of_evU (P : A[X]) (a : A) (h : ∀ u : ℂ, Commute (evU u P) a) (j : ℕ) :
    Commute (P.coeff j) a := by
  have hC : ∀ u : ℂ, evU u (C a) = a := fun u => by simp [evU_apply]
  have hQ : P * C a - C a * P = 0 := poly_eq_zero_of_evU _ fun u => by
    rw [map_sub, map_mul, map_mul, hC, sub_eq_zero]
    exact h u
  have h2 := congrArg (fun p => p.coeff j) hQ
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero] at h2
  exact sub_eq_zero.1 h2

theorem coeff_qdetPoly_mem {n : ℕ} (E : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (hS : ∀ p q, E p q ∈ S) (j : ℕ) : (qdetPoly E).coeff j ∈ S := by
  let f : S →+* A := S.val.toRingHom
  have hC : ∀ a ∈ S, C a ∈ liftsRing f := fun a ha => by
    rw [← lifts_iff_liftsRing]
    exact C_mem_lifts f ⟨a, ha⟩
  have hX : (X : A[X]) ∈ liftsRing f := by
    rw [← lifts_iff_liftsRing]
    exact X_mem_lifts f
  have hT : ∀ (k : ℕ) (a b : Fin n), tmPoly E k a b ∈ liftsRing f := fun k a b => by
    unfold tmPoly
    refine add_mem ?_ (hC _ (hS a b))
    split_ifs
    · exact sub_mem hX (hC _ (S.algebraMap_mem _))
    · exact zero_mem _
  have hP : qdetPoly E ∈ liftsRing f := by
    unfold qdetPoly
    refine sum_mem fun σ _ => mul_mem (hC _ (intCast_mem S _)) ?_
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hT _ _ _
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hP
  obtain ⟨y, hy⟩ := hP j
  rw [← hy]
  exact y.2

end Poly

theorem capelli_coef_commute : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  intro W _ _ M d X hgl hcomm
  have hL : ∀ i a p q, Commute ((qdetPoly (X i)).coeff a) (X i p q) := fun i a p q =>
    commute_coeff_of_evU _ _ (fun u => by
      rw [evU_qdetPoly]
      exact Formalism.REAL.qDetCentral _ _ (X i) (hgl i) u p q) a
  have hL2 : ∀ i j a r v, Commute ((qdetPoly (X i)).coeff a) (X j r v) := by
    intro i j a r v
    by_cases hij : i = j
    · subst hij
      exact hL i a r v
    · have hm := coeff_qdetPoly_mem (X i) (Subalgebra.centralizer ℂ {X j r v}) (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hcomm i j hij p q r v).symm.eq) a
      rw [Subalgebra.mem_centralizer_iff] at hm
      exact (hm _ rfl).symm
  refine ⟨fun i j => (qdetPoly (X i)).coeff j, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, htop, -⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i) = 1
    rw [coeff_qdetPoly_top _ _ (by omega), htop]
  · intro i u
    rw [← evU_qdetPoly (X i) u, evU_apply,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le (X i)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  · intro i hi
    obtain ⟨-, -, hsub⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i - 1) = _
    rw [coeff_qdetPoly_top _ _ (by omega), hsub (d i - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast, Algebra.algebraMap_eq_smul_one]
  · intro i j a b
    have hm := coeff_qdetPoly_mem (X j) (Subalgebra.centralizer ℂ {(qdetPoly (X i)).coeff a})
      (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hL2 i j a p q).eq) b
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm _ rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.SumSz

theorem sum_sz_eq_card : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  intro n M lev h
  have key := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M)))
    (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  unfold sz
  congr 1
  ext a
  simp [Fin.ext_iff]

end GlobalTheory.CompanionTheory.RgCOBlock.SumSz
end

