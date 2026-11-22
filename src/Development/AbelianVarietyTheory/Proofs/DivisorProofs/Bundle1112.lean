import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolarisationOperatorApplyVariable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowFock

open MvPolynomial

theorem fock_one {σ : Type} : Formalism.E.fock (1 : MvPolynomial σ ℂ) 1 = 1 := by
  simp [Formalism.E.fock, Formalism.A.mfact]

theorem fock_rename_inj {σ τ : Type} {f : σ → τ} (hf : Function.Injective f) (P P' : MvPolynomial σ ℂ) :
    Formalism.E.fock (rename f P) (rename f P') = Formalism.E.fock P P' := by
  have h := GlobalTheory.JointHarm.fock_rename_mul (g := (fun e : Empty => e.elim : Empty → τ)) hf
    (fun x => x.elim) (fun _ y => y.elim) P P' 1 1
  simpa [fock_one] using h

theorem fock_mul_of_supported {σ : Type} {A B : Set σ} (hAB : Disjoint A B) {P P' Q Q' : MvPolynomial σ ℂ}
    (hP : P ∈ supported ℂ A) (hP' : P' ∈ supported ℂ A) (hQ : Q ∈ supported ℂ B) (hQ' : Q' ∈ supported ℂ B) :
    Formalism.E.fock (P * Q) (P' * Q') = Formalism.E.fock P P' * Formalism.E.fock Q Q' := by
  rw [supported_eq_range_rename] at hP hP' hQ hQ'
  obtain ⟨P₀, rfl⟩ := (AlgHom.mem_range _).mp hP
  obtain ⟨P₁, rfl⟩ := (AlgHom.mem_range _).mp hP'
  obtain ⟨Q₀, rfl⟩ := (AlgHom.mem_range _).mp hQ
  obtain ⟨Q₁, rfl⟩ := (AlgHom.mem_range _).mp hQ'
  rw [GlobalTheory.JointHarm.fock_rename_mul Subtype.val_injective Subtype.val_injective
      (fun x y h => Set.disjoint_left.mp hAB x.2 (h ▸ y.2)),
    fock_rename_inj Subtype.val_injective, fock_rename_inj Subtype.val_injective]

theorem fock_prod_of_supported {σ ι : Type} [DecidableEq ι] (A : ι → Set σ) (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (F G : ι → MvPolynomial σ ℂ) (hF : ∀ i, F i ∈ supported ℂ (A i)) (hG : ∀ i, G i ∈ supported ℂ (A i))
    (s : Finset ι) :
    Formalism.E.fock (∏ i ∈ s, F i) (∏ i ∈ s, G i) = ∏ i ∈ s, Formalism.E.fock (F i) (G i) := by
  induction s using Finset.induction_on with
  | empty => simp [fock_one]
  | insert a s ha ih =>
    have hd : Disjoint (A a) (⋃ i ∈ s, A i) :=
      Set.disjoint_iUnion₂_right.mpr fun i hi => hA (fun e => ha (e ▸ hi))
    have hmem : ∀ H : ι → MvPolynomial σ ℂ, (∀ i, H i ∈ supported ℂ (A i)) →
        ∏ i ∈ s, H i ∈ supported ℂ (⋃ i ∈ s, A i) := fun H hH =>
      Subalgebra.prod_mem _ fun i hi => supported_mono (Set.subset_biUnion_of_mem hi) (hH i)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      fock_mul_of_supported hd (hF a) (hG a) (hmem F hF) (hmem G hG), ih]

theorem rename_mem_supported {σ τ : Type} (f : σ → τ) (s : Set τ) (hs : ∀ x, f x ∈ s) (P : MvPolynomial σ ℂ) :
    rename f P ∈ supported ℂ s := by
  classical
  rw [mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (vars_rename f P hv)
  exact hs w

variable {D : D7} {m n : ℕ}

theorem minorPlus_eq (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) (hpn : p ≤ n) (i : Fin p) :
    minorPlus (D := D) (m := m) (n := n) τ (i + 1) =
      rename (fun v : Fin n × Fin p => ((τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor hpn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor, AlgHom.map_det]
  unfold minorPlus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dif_pos ⟨by omega, by omega⟩]

theorem minorMinus_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hqn : q ≤ n) (i : Fin q) :
    minorMinus (D := D) (m := m) (n := n) τ p (i + 1) =
      rename (fun v : Fin n × Fin q => ((τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor hqn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor, AlgHom.map_det]
  unfold minorMinus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dif_pos ⟨by omega, by omega⟩]

def embTop (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Fin n × Fin p → FVar D m n :=
  fun v => (τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1)

def embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) : Fin n × Fin q → FVar D m n :=
  fun v => (τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1)

theorem embTop_injective (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Function.Injective (embTop (n := n) τ hpm) := by
  intro x y e
  simp only [embTop, Prod.mk.injEq, Fin.mk.injEq] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embBot_injective (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) :
    Function.Injective (embBot (n := n) τ (q := q) hm) := by
  intro x y e
  simp only [embBot, Prod.mk.injEq, Fin.mk.injEq, add_right_inj] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embTop_ne_embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (x : Fin n × Fin p) (y : Fin n × Fin q) :
    embTop τ (by omega) x ≠ embBot τ hm y := by
  intro e
  simp only [embTop, embBot, Prod.mk.injEq, Fin.mk.injEq] at e
  have := x.2.2
  omega

theorem minorProduct_rename_mem_supported_place (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (P : MvPolynomial (Fin n × Fin p) ℂ)
    (Q : MvPolynomial (Fin n × Fin q) ℂ) :
    rename (embTop τ (by omega)) P * rename (embBot τ hm) Q ∈ supported ℂ {v : FVar D m n | v.1 = τ} :=
  Subalgebra.mul_mem _ (rename_mem_supported (embTop τ (by omega)) {v : FVar D m n | v.1 = τ} (fun x => by simp [embTop]) P)
    (rename_mem_supported (embBot τ hm) {v : FVar D m n | v.1 = τ} (fun x => by simp [embBot]) Q)

theorem deltaAt_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ) :
    deltaAt (D := D) (m := m) (n := n) τ p ap q am =
      rename (embTop τ (by omega)) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop hpn (fun i : Fin p => ap i)) *
        rename (embBot τ hm) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom hqn (fun i : Fin q => am i)) := by
  unfold deltaAt GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom
  rw [map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorPlus_eq τ (by omega) hpn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorMinus_eq τ hm hqn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)

theorem hookOf_eq_hookProd (l : ℕ) (a : ℕ → ℕ) (ha : Antitone a) :
    (hookOf l a : ℂ) = ((GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) : ℚ) : ℂ) := by
  have ha' : ∀ x y, x ≤ y → y < l → a y ≤ a x := fun x y h _ => ha h
  have hant : Antitone (fun i : Fin l => a i) := fun i j h => ha (Fin.le_iff_val_le_val.mp h)
  suffices h : (hookOf l a : ℚ) = GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) by
    rw [← h]; push_cast; rfl
  rw [GlobalTheory.HookDiagram.hookOf_eq l a ha', GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd,
    eq_div_iff (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos hant).ne']
  have key := congrArg (Nat.cast : ℕ → ℚ) (GlobalTheory.LiftSizeCompare.hookProd_mul l a ha')
  push_cast [Nat.cast_prod] at key
  have hden : (∏ r ∈ Finset.range l, ∏ j ∈ Finset.Ioo r l, ((a r - a j + (j - r) : ℕ) : ℚ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen (fun i : Fin l => a i) := by
    rw [Finset.prod_range, GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen]
    refine Finset.prod_congr rfl fun i _ => ?_
    symm
    refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Ioo.mpr ⟨Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj), j.2⟩
    · intro j _ j' _ e
      exact Fin.ext e
    · intro b hb
      have := Finset.mem_Ioo.mp hb
      exact ⟨⟨b, this.2⟩, Finset.mem_Ioi.mpr (Fin.lt_iff_val_lt_val.mpr this.1), rfl⟩
    · intro j hj
      have hij : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj)
      have h1 : a j ≤ a i := ha hij.le
      rw [Nat.cast_add, Nat.cast_sub h1, Nat.cast_sub hij.le]
      ring
  have hnum : (∏ r ∈ Finset.range l, (((a r + l - 1 - r).factorial : ℕ) : ℚ)) =
      ∏ i : Fin l, (((a i + (l - ((i : ℕ) + 1))).factorial : ℕ) : ℚ) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := i.2
    congr 3
    omega
  rw [← hden, ← hnum]
  exact_mod_cast key

theorem fock_deltaAt (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    Formalism.E.fock (deltaAt (D := D) (m := m) (n := n) τ p ap q am) (deltaAt τ p ap q am) =
      (hookOf p ap : ℂ) * (hookOf q am : ℂ) := by
  have hp : Antitone (fun i : Fin p => ap i) := fun i j h => hap (Fin.le_iff_val_le_val.mp h)
  have hq : Antitone (fun i : Fin q => am i) := fun i j h => ham (Fin.le_iff_val_le_val.mp h)
  rw [deltaAt_eq τ hm hpn hqn, GlobalTheory.JointHarm.fock_rename_mul (embTop_injective τ _) (embBot_injective τ hm)
      (embTop_ne_embBot τ hm),
    GlobalTheory.MinorNorm.hookNorm _ _ _ _ hp, GlobalTheory.MinorNorm.hookNormBottom _ _ _ _ hq,
    hookOf_eq_hookProd _ _ hap, hookOf_eq_hookProd _ _ ham]

theorem fock_delta (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (h1 : ∀ τ, p τ + q τ ≤ m) (h2 : ∀ τ, p τ ≤ n ∧ q τ ≤ n) (h3 : ∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) :
    Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) =
      ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  classical
  have hmem : ∀ τ, deltaAt (D := D) (m := m) (n := n) τ (p τ) (ap τ) (q τ) (am τ) ∈
      supported ℂ {v : FVar D m n | v.1 = τ} := fun τ => by
    rw [deltaAt_eq τ (h1 τ) (h2 τ).1 (h2 τ).2]
    exact minorProduct_rename_mem_supported_place τ (h1 τ) _ _
  unfold Formalism.IndefR.Datum.delta
  rw [fock_prod_of_supported (fun τ => {v : FVar D m n | v.1 = τ})
    (fun a b hab => Set.disjoint_left.mpr fun v ha hb => hab (ha.symm.trans hb)) _ _ hmem hmem Finset.univ]
  exact Finset.prod_congr rfl fun τ _ =>
    fock_deltaAt τ (h1 τ) (h2 τ).1 (h2 τ).2 _ _ (h3 τ).1 (h3 τ).2

end GlobalTheory.LowRowFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEigenvalueAtBaseFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigenvalue_at_base_frame : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  first | exact @GlobalTheory.HeckeUnitary.star_eigenvalue_mul | exact GlobalTheory.HeckeUnitary.star_eigenvalue_mul | (intros; apply GlobalTheory.HeckeUnitary.star_eigenvalue_mul <;> assumption)
end

