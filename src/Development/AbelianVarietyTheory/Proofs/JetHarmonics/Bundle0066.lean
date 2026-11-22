import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.Bundle0005
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
section
namespace GlobalTheory.HatTaylorPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Polynomial

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def ev (f : ℕ → A) (P : A[X]) : A := P.sum fun j a => f j * a

omit [Algebra ℂ A] in
theorem ev_add (f : ℕ → A) (P Q : A[X]) : ev f (P + Q) = ev f P + ev f Q :=
  Polynomial.sum_add_index _ _ _ (by simp) (by simp [mul_add])

omit [Algebra ℂ A] in
theorem ev_monomial (f : ℕ → A) (n : ℕ) (a : A) : ev f (monomial n a) = f n * a :=
  Polynomial.sum_monomial_index _ _ (by simp)

omit [Algebra ℂ A] in
theorem ev_mul (f g : ℕ → A) (P Q : A[X]) (z : A) (h : ∀ j, z * g j = ev (fun i => f (j + i)) P) :
    z * ev g Q = ev f (P * Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [ev_add, mul_add, mul_add, ev_add, hp, hq]
  | monomial n b =>
    rw [ev_monomial, ← mul_assoc, h]
    clear h
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [ev_add, add_mul, add_mul, ev_add, hp, hq]
    | monomial k a => rw [monomial_mul_monomial, ev_monomial, ev_monomial, mul_assoc, add_comm]

omit [Algebra ℂ A] in
theorem ev_eq_sum (f : ℕ → A) (P : A[X]) (n : ℕ) (h : P.natDegree < n) :
    ev f P = ∑ j ∈ Finset.range n, f j * P.coeff j :=
  Polynomial.sum_over_range' _ (by simp) n h

omit [Algebra ℂ A] in
theorem mul_ev (z : A) (f : ℕ → A) (P : A[X]) : z * ev f P = ev (fun i => z * f i) P := by
  simp [ev, Polynomial.sum, Finset.mul_sum, mul_assoc]

def Deg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ P : A[X], P.natDegree ≤ D ∧ (∀ s : ℂ, Z (Y + s) = ev (fun j => algebraMap ℂ A (s ^ j)) P) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ev (fun j => m (q + j)) P

variable {L : LevelData A r} {Y : ℂ}

theorem Deg.mono {D E : ℕ} {Z : ℂ → A} (h : Deg L Y D Z) (hDE : D ≤ E) : Deg L Y E Z := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.trans hDE, h2⟩

theorem Deg.add {D : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y D W) :
    Deg L Y D (fun y => Z y + W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P + Q, (natDegree_add_le _ _).trans (max_le h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_add, ← h2, ← k2]
  · rw [ev_add, ← h3 m hm, ← k3 m hm, add_mul]

theorem Deg.mul {D E : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y E W) :
    Deg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P * Q, natDegree_mul_le.trans (add_le_add h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · show Z (Y + s) * W (Y + s) = _
    rw [k2]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [← Algebra.commutes, h2, mul_ev]
    simp only [pow_add, map_mul]
  · show Z Y * W Y * m q = _
    rw [mul_assoc, k3 m hm]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [h3 m hm]
    simp only [add_assoc]

theorem deg_const (a : A) (ha : ∀ m : ℕ → A, MulRel L m → ∀ q, a * m q = m q * a) :
    Deg L Y 0 (fun _ => a) := by
  refine ⟨monomial 0 a, natDegree_monomial_le _, fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_monomial]; simp
  · rw [ev_monomial, ha m hm]; rfl

theorem deg_fn {a : A} (ha : a ∈ L.fns) : Deg L Y 0 (fun _ => a) :=
  deg_const a fun _ hm q => ((hm q).1 a ha).eq

theorem deg_lin (Z : ℂ → A) (b : A) (h1 : ∀ s, Z (Y + s) = Z Y + algebraMap ℂ A s * b)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * b) : Deg L Y 1 Z := by
  refine ⟨monomial 0 (Z Y) + monomial 1 b, (natDegree_add_le _ _).trans
    (max_le ((natDegree_monomial_le _).trans zero_le_one) (natDegree_monomial_le _)), fun s => ?_,
    fun m hm q => ?_⟩
  · rw [ev_add, ev_monomial, ev_monomial, h1]; simp
  · rw [ev_add, ev_monomial, ev_monomial, h2 m hm]; rfl

theorem deg_list (l : List A) (hl : ∀ a ∈ l, a ∈ L.fns) : Deg L Y 0 (fun _ => l.prod) := by
  induction l with
  | nil => exact deg_const _ (by simp)
  | cons a l ih =>
    simpa using (deg_fn (hl a (by simp))).mul (ih fun b hb => hl b (by simp [hb]))

theorem deg_Tl (l : Fin r) (i j : Fin 2) : Deg L Y 1 (fun y => L.Tl y l i j) := by
  have hc : L.c l ∈ L.fns := by simp [LevelData.fns]
  have hci : L.ci l ∈ L.fns := by simp [LevelData.fns]
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl]
  · refine deg_lin _ 1 (fun s => ?_) fun m hm q => ?_
    · simp [add_right_comm]
    · simp [add_mul, mul_add, (hm q).2.1 l, Algebra.commutes, add_assoc]
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact ((hm q).1 _ hc).neg_left.eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    simpa using ((hm q).1 _ hci).eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact (Commute.zero_left (m q)).eq

theorem deg_prod (l : List (Fin r)) (i j : Fin 2) :
    Deg L Y l.length (fun y => (l.map (L.Tl y)).prod i j) := by
  induction l generalizing i j with
  | nil =>
    refine deg_const ((1 : Matrix (Fin 2) (Fin 2) A) i j) fun m _ q => ?_
    rw [Matrix.one_apply]; split_ifs <;> simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    rw [add_comm l.length 1]
    exact ((deg_Tl a i 0).mul (ih 0 j)).add ((deg_Tl a i 1).mul (ih 1 j))

theorem deg_Tprod (i j : Fin 2) : Deg L Y r (fun y => L.Tprod y i j) := by
  have h := deg_prod (L := L) (Y := Y) (List.finRange r).reverse i j
  simp only [List.length_reverse, List.length_finRange] at h
  simpa only [LevelData.Tprod, List.ofFn_eq_map, List.map_reverse] using h

theorem forwardTaylorDegree_one_leftLetter : Deg L Y 1 L.l0 := by
  refine deg_lin _ (-(L.ζb * L.GGi)) (fun s => ?_) fun m hm q => ?_
  · simp only [LevelData.l0, add_right_comm Y s, map_add (algebraMap ℂ A) (Y + 1 / 2) s]
    noncomm_ring
  · have c1 : ∀ q, Commute (L.ζb * L.GGi) (m q) := fun q =>
      ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))
    have c2 : Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) (m q) :=
      (Algebra.commute_algebraMap_left _ _).mul_left (c1 q)
    rw [LevelData.l0, sub_mul, neg_mul, (hm q).2.2.2.1, c2.eq, (c1 (q + 1)).eq]
    noncomm_ring

theorem deg_Ahat : Deg L Y r L.Ahat := by
  have h := (deg_list (L := L) (Y := Y) (List.ofFn L.c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_Tprod 0 0)
  rw [zero_add] at h
  exact h

theorem forwardTaylorDegree_plusHatR : Deg L Y (r + 1) L.R0 := by
  have h := ((deg_list (L := L) (Y := Y) (List.ofFn L.cb) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_fn (a := L.GG) (by simp [LevelData.fns]))).mul
    ((forwardTaylorDegree_one_leftLetter.mul (deg_Tprod 0 0)).add ((deg_Tprod 1 0).mono (Nat.le_add_left _ _)))
  rw [zero_add, zero_add, add_comm 1 r] at h
  exact h

theorem taylor_plus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨P, h1, h2, h3⟩ := deg_Ahat (L := L) (Y := Y)
  obtain ⟨Q, k1, k2, k3⟩ := forwardTaylorDegree_plusHatR (L := L) (Y := Y)
  have hP : P.natDegree < r + 2 := by omega
  have hQ : Q.natDegree < r + 2 := by omega
  refine ⟨P.coeff, Q.coeff, fun s => ?_, fun s => ?_, fun m hm q => ⟨?_, ?_⟩⟩
  · rw [h2, ev_eq_sum _ _ _ hP]; simp only [Algebra.smul_def]
  · rw [k2, ev_eq_sum _ _ _ hQ]; simp only [Algebra.smul_def]
  · rw [h3 m hm, ev_eq_sum _ _ _ hP]
  · rw [k3 m hm, ev_eq_sum _ _ _ hQ]

end

end GlobalTheory.HatTaylorPlus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHyp
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.HatCommutators

section lists
variable {A : Type} [Ring A]

theorem comm_ofFn {n : ℕ} (f : Fin n → A) (a : A) (h : ∀ l, Commute a (f l)) :
    Commute a (List.ofFn f).prod := by
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  exact h l

theorem ofFn_mul_inv : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, f l * g l = 1) → (∀ l m, Commute (g l) (f m)) →
    (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := ofFn_mul_inv (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)
    have hc' := comm_ofFn (fun i : Fin n => f i.succ) (g 0) (fun l => hc _ _)
    rw [mul_assoc, ← mul_assoc _ (g 0), ← hc'.eq, mul_assoc, ih, mul_one, h]

theorem star_ofFn [StarRing A] : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, star (f l) = g l) →
    (∀ l m, Commute (g l) (g m)) → star (List.ofFn f).prod = (List.ofFn g).prod
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul]
    have ih := star_ofFn (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)
    have hc' := comm_ofFn (fun i : Fin n => g i.succ) (g 0) (fun l => hc _ _)
    rw [ih, h, hc'.eq]

end lists

variable {A : Type} [Ring A] [Algebra ℂ A]

section level
variable {r : ℕ} (L : LevelData A r)

theorem c_mem (l : Fin r) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem ci_mem (l : Fin r) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem cb_mem (l : Fin r) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem cbi_mem (l : Fin r) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem GG_mem : L.GG ∈ L.fns := by simp [LevelData.fns]

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem comm_Dr {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Dr :=
  comm_ofFn _ _ fun l => h _ (c_mem L l)
theorem comm_Drb {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Drb :=
  comm_ofFn _ _ fun l => h _ (cb_mem L l)

theorem Dri_Dr : L.Dri * L.Dr = 1 :=
  ofFn_mul_inv _ _ L.ci_c fun l m => fcomm L (c_mem L l) (ci_mem L m)
theorem Drbi_Drb : L.Drbi * L.Drb = 1 :=
  ofFn_mul_inv _ _ L.cbi_cb fun l m => fcomm L (cb_mem L l) (cbi_mem L m)
theorem Dr_Drb : Commute L.Dr L.Drb :=
  comm_ofFn _ _ fun l => (comm_Dr L fun _ hg => fcomm L (cb_mem L l) hg).symm

end level

variable [StarRing A] {P : M.Par} (d : Q.NFData P A)

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ basics d) : b * h ∈ nfSpan d (basics d) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem kap_mem (f : M.Ty P → ℂ) : d.κ f ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))

theorem ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : ssn d l ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, by simpa using hl, rfl⟩))

theorem star_ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : star (ssn d l) ∈ bmon d :=
  Submonoid.subset_closure (Or.inr ⟨l, by simpa using hl, rfl⟩)

theorem rh_eq (hR : d.Rel) (y : ℂ) :
    rh d y = d.x y * d.L.R0 y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Drb * (d.L.GG * d.x y) = d.x y * (d.L.Drb * d.L.GG) := by
    have := ((comm_Drb d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have h2 : ∀ l, ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y =
      d.L.Drb * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
    intro l
    have hc := ((comm_Dr d.L (hS' l)).mul_left (comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y))).eq
    calc _ = d.L.Drb * d.L.Dri * ((d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Dr) * d.L.Ar y := by
          simp only [ssn, LevelData.Ahat, mul_assoc]
      _ = d.L.Drb * (d.L.Dri * d.L.Dr) * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by rw [Dri_Dr, mul_one]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Drb * ((d.L.GG * d.x y * d.L.l0 y + d.weightedSumBis y) * d.L.Ar y + d.L.GG * d.x y * d.L.Br y) =
    d.x y * (d.L.Drb * d.L.GG * (d.L.l0 y * d.L.Ar y + d.L.Br y)) + d.L.Drb * d.weightedSumBis y * d.L.Ar y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem rhv_eq (hR : d.Rel) (hc : ∀ l, star (d.L.c l) = d.L.cb l) (hci : ∀ l, star (d.L.ci l) = d.L.cbi l)
    (y : ℂ) :
    rhv d y = d.x y * d.L.R0v y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Dr * (d.L.GG * d.x y) = d.x y * (d.L.Dr * d.L.GG) := by
    have := ((comm_Dr d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have s1 : star d.L.Drb = d.L.Dr :=
    star_ofFn _ _ (fun l => by rw [← hc, star_star]) fun l m => fcomm d.L (c_mem _ l) (c_mem _ m)
  have s2 : star d.L.Dri = d.L.Drbi :=
    star_ofFn _ _ hci fun l m => fcomm d.L (cbi_mem _ l) (cbi_mem _ m)
  have h2 : ∀ l, (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y =
      d.L.Dr * ((d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l)) * d.L.Avr y := by
    intro l
    have hs : Commute (star (d.SS l)) d.L.Dr := by
      rw [← s1]; exact (comm_Drb d.L (hS' l)).star_star
    have hc := ((comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y)).mul_left hs).eq
    calc _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * (d.L.Drbi * (d.L.Dr * d.L.Drb)) * d.L.Avr y := by
          simp only [ssn, LevelData.Ahatv, star_mul, s1, s2, mul_assoc]
      _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * d.L.Dr * d.L.Avr y := by
          rw [(Dr_Drb d.L).eq, ← mul_assoc d.L.Drbi, Drbi_Drb, one_mul]
      _ = _ := by rw [hc]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Avr y + d.L.GG * d.x y * d.L.Bvr y) =
    d.x y * (d.L.Dr * d.L.GG * (d.L.m0 y * d.L.Avr y + d.L.Bvr y)) + d.L.Dr * d.S12 y * d.L.Avr y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem xinv_mul (y : ℂ) (hy : ∀ ρ : M.Ty P, M.xC P ρ y ≠ 0) :
    (d.κ fun ρ => (M.xC P ρ y)⁻¹) * d.x y = 1 := by
  rw [Q.NFData.x, ← map_mul, ← map_one d.κ]
  congr 1
  funext ρ
  exact inv_mul_cancel₀ (hy ρ)

end GlobalTheory.HatNF.HatCommutators

namespace GlobalTheory.HatNF

open HatCommutators

theorem r0_mem_nfSpan_basics : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  intro P A _ _ _ _ d hd y hy
  obtain ⟨-, -, hR, -, hc, hci, -⟩ := hd
  have hx := xinv_mul d (y : ℂ) fun ρ => (hy ρ).1
  have hk := kap_mem d fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  set k := d.κ fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  constructor
  · have e : d.L.R0 y = k * rh d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ahat y := by
      rw [rh_eq d hR, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (ssn_mem d hl)) (kap_mem d _)) ⟨y, hy, by simp⟩
  · have e : d.L.R0v y = k * rhv d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l)) * d.L.Ahatv y := by
      rw [rhv_eq d hR hc hci, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (kap_mem d _)) (star_ssn_mem d hl)) ⟨y, hy, by simp⟩

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenspaceIrreducibleDualStandard
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem casimir_eigenspace_irred_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → Stab Et (Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ Module.End.eigenspace Om (β + L l + (n : ℂ)) → Stab Et S' → S' = ⊥ ∨ S' = Module.End.eigenspace Om (β + L l + (n : ℂ))) ∧ Module.End.eigenspace Om (β + L l + (n : ℂ)) ≤ CapSp Et (shf β (Function.update L l (L l - 1))) := by
  intro V _ _ _ n E Et Om β L l hH hA hEt hOm
  classical
  obtain ⟨hgl, hAt, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hH.gl hA hEt hOm
  set S := Module.End.eigenspace Om (β + L l + (n : ℂ)) with hS
  have hstab : Stab Et S := by
    intro a b v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    have := LinearMap.congr_fun (hcomm a b) v
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  have hdec : SDec (shf β L) := by
    intro a b hab
    have h := hH.anti hab
    refine ⟨(L a - L b - 1).toNat, ?_⟩
    have h2 : (((L a - L b - 1).toNat : ℕ) : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((L a - L b - 1).toNat : ℕ) : ℂ) = (L a : ℂ) - L b - 1 := by exact_mod_cast h2
    rw [h3]; simp only [shf]; ring
  have hwt : ∀ (ν : Fin (n + 1) → ℂ) (v : V), v ≠ 0 → IsHW E ν v →
      ∀ j, ν j = β + L j + ((j : ℕ) : ℂ) := by
    intro ν v hv hw j
    have hm : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => hH.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun h => hv (by rw [h] at hm; simpa using hm)
    exact (Formalism.FourierDecayAlt.P.capelli_singular V (n + 1) E _ hH.gl hne).2 hdec ν v hm hv hw j
  have hkey : ∀ (θ : Fin (n + 1) → ℂ) (y : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S → y ≠ 0 →
      IsHW Et θ y → y l ≠ 0 ∧ IsHW E (fun j => β + L j + ((j : ℕ) : ℂ)) (y l) ∧
        θ = fun j => β + L j + ((j : ℕ) : ℂ) - if j = l then 1 else 0 := by
    intro θ y hy hy0 hw
    rw [hS, Module.End.mem_eigenspace_iff] at hy
    obtain ⟨c, hc, hwc, hlam⟩ :=
      hw_component_tensor_dual_standard V n E Et Om θ _ y hEt hOm hy0 hw hy
    have h1 := hwt _ _ hc hwc
    have h2 := h1 c
    simp only [if_true] at h2
    have h3 : (L l : ℂ) = L c := by linear_combination hlam + h2
    have h4 : l = c := hH.anti.injective (by exact_mod_cast h3)
    subst h4
    refine ⟨hc, ?_, ?_⟩
    · have : (fun j => β + L j + ((j : ℕ) : ℂ)) = fun a => θ a + if a = l then 1 else 0 :=
        funext fun j => (h1 j).symm
      rw [this]; exact hwc
    · funext j
      rw [← h1 j]; ring
  have hsub : ∀ (ν : Fin (n + 1) → ℂ) (v : V), IsHW E ν v →
      IsHW (subA E) (fun a => ν a.castSucc) v := by
    intro ν v hw
    exact ⟨fun a => hw.1 _, fun a b hab => hw.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
  have hprop : ∀ (θ θ' : Fin (n + 1) → ℂ) (y y' : PiLp 2 (fun _ : Fin (n + 1) => V)), y ∈ S →
      y ≠ 0 → IsHW Et θ y → y' ∈ S → y' ≠ 0 → IsHW Et θ' y' → ∃ t : ℂ, y' = t • y := by
    intro θ θ' y y' hy hy0 hw hy' hy0' hw'
    obtain ⟨a1, a2, a3⟩ := hkey θ y hy hy0 hw
    obtain ⟨b1, b2, b3⟩ := hkey θ' y' hy' hy0' hw'
    obtain ⟨t, ht⟩ := Formalism.FourierDecayAlt.P.multiplicity_one V n E _ _ _ hH.gl hH.irr (hsub _ _ a2)
      (hsub _ _ b2) a1
    refine ⟨t, ?_⟩
    by_contra hne
    have hθ : θ' = θ := b3.trans a3.symm
    rw [hθ] at hw'
    have hz : IsHW Et θ (y' - t • y) := by
      refine ⟨fun a => ?_, fun a b hab => ?_⟩
      · rw [map_sub, map_smul, hw.1, hw'.1, smul_sub, smul_comm]
      · rw [map_sub, map_smul, hw.2 a b hab, hw'.2 a b hab, smul_zero, sub_zero]
    have := (hkey θ _ (S.sub_mem hy' (S.smul_mem t hy)) (sub_ne_zero.mpr hne) hz).1
    apply this
    rw [PiLp.sub_apply, PiLp.smul_apply, ht, sub_self]
  have hirr : ∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' →
      S' = ⊥ ∨ S' = S := by
    intro S' hle hst
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hT : S'ᗮ ⊓ S ≠ ⊥ := by
      intro h
      have := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
      rw [h, sup_bot_eq] at this
      exact h1 this
    have hTs : Stab Et (S'ᗮ ⊓ S) := by
      intro a b v hv
      refine ⟨?_, hstab a b v hv.2⟩
      have hv1 : v ∈ S'ᗮ := hv.1
      change Et a b v ∈ S'ᗮ
      rw [Submodule.mem_orthogonal] at hv1 ⊢
      intro u hu
      rw [← hAt]
      exact hv1 _ (hst b a u hu)
    obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S' hst h0
    obtain ⟨θ', y', hy', hy0', hw', -⟩ :=
      Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl _ hTs hT
    obtain ⟨t, ht⟩ := hprop θ θ' y y' (hle hy) hy0 hw hy'.2 hy0' hw'
    have hm : y' ∈ S' := ht ▸ S'.smul_mem t hy
    have hm2 : y' ∈ S'ᗮ := hy'.1
    exact hy0' (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hm2 y' hm))
  refine ⟨hstab, hirr, ?_⟩
  by_cases h0 : S = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨θ, y, hy, hy0, hw, -⟩ :=
    Formalism.FourierDecayAlt.P.exists_singular_maximal_vector _ (n + 1) Et hgl S hstab h0
  obtain ⟨-, -, hθ⟩ := hkey θ y hy hy0 hw
  have hcap : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) := by
    rw [mem_CapSp]
    intro w
    rw [qDetHW _ (n + 1) Et θ y hgl hw w]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hθ]
    by_cases hk : k = l
    · subst hk
      simp only [if_true, Function.update_self]
      push_cast; ring
    · simp only [hk, if_false, Function.update_of_ne hk]
      ring
  have hcs := (Formalism.FourierDecayAlt.P.capelli_stabilizer _ (n + 1) Et
    (shf β (Function.update L l (L l - 1))) hgl).1
  rcases hirr (CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S) inf_le_right
    (fun a b v hv => ⟨hcs a b v hv.1, hstab a b v hv.2⟩) with h | h
  · have : y ∈ CapSp Et (shf β (Function.update L l (L l - 1))) ⊓ S := ⟨hcap, hy⟩
    rw [h] at this
    exact absurd (by simpa using this) hy0
  · exact inf_eq_right.mp h

end GlobalTheory
end

