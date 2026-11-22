import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStableAndIncreasing
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

noncomputable section

namespace GlobalTheory.SteepMult.Filt

variable {R S : ℕ}

lemma sameBlock_symm {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

lemma sameBlock_trans {a b c : Ix R S} (h₁ : sameBlock a b) (h₂ : sameBlock b c) : sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

lemma comm_single_apply (Z : Mat R S) (a b c d : Ix R S) :
    ((Z * Matrix.single a b (1 : ℂ) - Matrix.single a b 1 * Z : Mat R S)) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
  by_cases hd : d = b <;> by_cases hc : c = a
  all_goals (try subst hd); (try subst hc); simp [Matrix.sub_apply, *]

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [eNC, Eab, Matrix.smul_apply, smul_eq_mul]
  rw [comm_single_apply]
  obtain ⟨⟨a, b⟩, hab⟩ := x
  by_cases h : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · simp only
      by_cases hd : d = b
      · subst hd
        have hca : ¬ sameBlock c a := fun h' => hab (sameBlock_trans (sameBlock_symm h') h)
        by_cases hc : c = a
        · subst hc; exact absurd h hab
        · simp [hZ _ _ hca, hc]
      · by_cases hc : c = a
        · subst hc
          have hbd : ¬ sameBlock b d := fun h' => hab (sameBlock_trans h (sameBlock_symm h'))
          simp [hZ _ _ hbd, hd]
        · simp [hd, hc]
    · intro y _
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => y.2 (h1 ▸ h2 ▸ h)
      simp [Matrix.single_apply, this]
  · rw [Finset.sum_eq_single ⟨(c, d), h⟩]
    · simp [adP]
    · intro y _ hy
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => hy (Subtype.ext (Prod.ext h1 h2))
      simp [Matrix.single_apply, this]
    · simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

lemma act_comm_eNC {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) {Z : Mat R S} (hZ : IsKC Z)
    (x : NC R S) (w : V) :
    act Z (act (eNC x) w) = act (eNC x) (act Z w) + ∑ y, adP Z y x • act (eNC y) w := by
  have h := hlie Z (eNC x)
  rw [bracket_eNC hZ x] at h
  have h2 := congrArg (fun T : Module.End ℂ V => T w) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [h2]; abel

lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

lemma word_cons (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (x : NC R S) (g : Fin k → NC R S) :
    word act (Fin.cons x g : Fin (k + 1) → NC R S) = act (eNC x) * word act g := by
  simp [word, List.ofFn_succ]

lemma word_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ LinearMap.range (phiN act N k) := by
  classical
  refine ⟨Pi.single g ⟨n, hn⟩, ?_⟩
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hh; simp [Pi.single_apply, hh]
  · simp

lemma act_eNC_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (x : NC R S) {w : V}
    (hw : w ∈ LinearMap.range (phiN act N k)) : act (eNC x) w ∈ LinearMap.range (phiN act N (k + 1)) := by
  obtain ⟨Ψ, rfl⟩ := hw
  rw [phiN_apply, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  have := word_mem_range act N (Fin.cons x g : Fin (k + 1) → NC R S) (Ψ g).2
  rwa [word_cons, Module.End.mul_apply] at this

lemma kstable_range {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) (N : Submodule ℂ V)
    (hN : KStable act N) (k : ℕ) : KStable act (LinearMap.range (phiN act N k)) := by
  induction k with
  | zero =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have := word_mem_range act N g (hN Z hZ _ (Ψ g).2)
    simpa [word_zero] using this
  | succ k ih =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [← Fin.cons_self_tail g, word_cons, Module.End.mul_apply, act_comm_eNC hlie hZ]
    have hw' := word_mem_range act N (Fin.tail g) (Ψ (Fin.cons (g 0) (Fin.tail g))).2
    refine add_mem (act_eNC_mem_range act N _ (ih Z hZ _ hw')) (Submodule.sum_mem _ fun y _ => ?_)
    exact Submodule.smul_mem _ _ (act_eNC_mem_range act N _ hw')

theorem filt_basic : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ k : ℕ,
    KStable M.act (filt M.act N k) ∧
    filt M.act N (k + 1) = filt M.act N k ⊔ LinearMap.range (phiN M.act N (k + 1)) ∧ filt M.act N 0 ≤ N := by
  intro R S M N hN k
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ w hw
    refine Submodule.iSup_induction (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j))
      (motive := fun w => M.act Z w ∈ filt M.act N k) hw ?_ ?_ ?_
    · intro j w hw
      exact (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) j)
        (kstable_range M.lie N hN j Z hZ w hw)
    · simp
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · apply le_antisymm
    · refine iSup_le fun j => ?_
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact le_sup_right
      · exact le_sup_of_le_left (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) i)
    · refine sup_le (iSup_le fun i => ?_) ?_
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) i.castSucc
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) (Fin.last (k + 1))
  · refine iSup_le fun j => ?_
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rintro _ ⟨Ψ, rfl⟩
    rw [phiN_apply]
    refine Submodule.sum_mem _ fun g _ => ?_
    have : word M.act g = 1 := by simp [word]
    rw [this]; exact (Ψ g).2

end GlobalTheory.SteepMult.Filt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernel
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.PositionRel

variable {R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma sameBlock_of_not {a b c : Ix R S} (hab : ¬ sameBlock a b) (hbc : ¬ sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> simp_all [sameBlock]

lemma sameBlock_symm' {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

lemma sameBlock_trans' {a b c : Ix R S} (hab : sameBlock a b) (hbc : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> simp_all [sameBlock]

lemma isPC_eNC (x : NC R S) : IsPC (eNC x) := by
  intro a b hab
  simp only [eNC, Eab, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    exact absurd (h1 ▸ h2 ▸ hab) x.2
  · rfl

lemma isKC_comm_PC {X Y : Mat R S} (hX : IsPC X) (hY : IsPC Y) : IsKC (X * Y - Y * X) := by
  intro u v huv
  have h1 : ∀ (A B : Mat R S), IsPC A → IsPC B → (A * B) u v = 0 := by
    intro A B hA hB
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases huw : sameBlock u w
    · rw [hA u w huw, zero_mul]
    · rw [hB w v (sameBlock_of_not (fun h => huw (sameBlock_symm' h)) huv), mul_zero]
  rw [Matrix.sub_apply, h1 X Y hX hY, h1 Y X hY hX, sub_zero]

lemma isPC_comm_KC {Z X : Mat R S} (hZ : IsKC Z) (hX : IsPC X) : IsPC (Z * X - X * Z) := by
  intro u v huv
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have e1 : ∑ w, Z u w * X w v = 0 := Finset.sum_eq_zero fun w _ => by
    by_cases huw : sameBlock u w
    · rw [hX w v (sameBlock_trans' (sameBlock_symm' huw) huv), mul_zero]
    · rw [hZ u w huw, zero_mul]
  have e2 : ∑ w, X u w * Z w v = 0 := Finset.sum_eq_zero fun w _ => by
    by_cases huw : sameBlock u w
    · rw [hX u w huw, zero_mul]
    · rw [hZ w v (fun h => huw (sameBlock_trans' huv (sameBlock_symm' h))), mul_zero]
  rw [e1, e2, sub_zero]

variable (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)

lemma word_zero (h : Fin 0 → NC R S) : word act h = 1 := by simp [word]

lemma word_succ {j : ℕ} (h : Fin (j + 1) → NC R S) :
    word act h = act (eNC (h 0)) * word act (Fin.tail h) := by
  simp [word, List.ofFn_succ, Fin.tail]

lemma word_cons {j : ℕ} (x : NC R S) (h : Fin j → NC R S) :
    word act (Fin.cons x h : Fin (j + 1) → NC R S) = act (eNC x) * word act h := by
  rw [word_succ, Fin.cons_zero, Fin.tail_cons]

lemma filt_mono {m m' : ℕ} (hm : m ≤ m') : filt act N m ≤ filt act N m' := by
  refine iSup_le fun j => ?_
  exact le_iSup (fun j' : Fin (m' + 1) => LinearMap.range (phiN act N j')) ⟨j, by omega⟩

lemma word_mem {j m : ℕ} (hj : j ≤ m) (h : Fin j → NC R S) (n : N) : word act h n ∈ filt act N m := by
  have h1 : word act h n ∈ LinearMap.range (phiN act N j) := by
    refine ⟨fun g => if g = h then n else 0, ?_⟩
    rw [phiN_apply, Finset.sum_eq_single h (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h2 : LinearMap.range (phiN act N j) ≤ filt act N j :=
    le_iSup (fun j' : Fin (j + 1) => LinearMap.range (phiN act N j')) ⟨j, by omega⟩
  exact filt_mono act N hj (h2 h1)

lemma mem_filt_zero (n : N) : (n : V) ∈ filt act N 0 := by
  have := word_mem act N le_rfl (Fin.elim0 : Fin 0 → NC R S) n
  rwa [word_zero, Module.End.one_apply] at this

lemma filt_map {m m' : ℕ} (T : V →ₗ[ℂ] V)
    (hT : ∀ j ≤ m, ∀ (h : Fin j → NC R S) (n : N), T (word act h n) ∈ filt act N m') :
    ∀ v ∈ filt act N m, T v ∈ filt act N m' := by
  intro v hv
  have hv' : v ∈ ⨆ j : Fin (m + 1), LinearMap.range (phiN act N j) := hv
  refine Submodule.iSup_induction (fun j : Fin (m + 1) => LinearMap.range (phiN act N j))
    (motive := fun v => T v ∈ filt act N m') hv' ?_ (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
  rintro j _ ⟨Ψ, rfl⟩
  rw [phiN_apply, map_sum]
  exact Submodule.sum_mem _ fun g _ => hT j (Nat.lt_succ_iff.mp j.isLt) g (Ψ g)

lemma filt_X {m : ℕ} (x : NC R S) : ∀ v ∈ filt act N m, act (eNC x) v ∈ filt act N (m + 1) :=
  filt_map act N (act (eNC x)) fun j hj h n => by
    rw [← Module.End.mul_apply, ← word_cons]
    exact word_mem act N (by omega) _ n

lemma filt_word {m : ℕ} : ∀ {j : ℕ} (h : Fin j → NC R S), ∀ v ∈ filt act N m, word act h v ∈ filt act N (m + j) := by
  intro j
  induction j with
  | zero => intro h v hv; simpa [word_zero] using hv
  | succ j ih =>
    intro h v hv
    rw [word_succ, Module.End.mul_apply]
    exact filt_X act N (h 0) _ (ih (Fin.tail h) v hv)

lemma act_pc_mem {m : ℕ} {P : Mat R S} (hP : IsPC P) (v : V) (hv : v ∈ filt act N m) :
    act P v ∈ filt act N (m + 1) := by
  rw [Matrix.matrix_eq_sum_single P]
  simp only [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : sameBlock a b
  · simp [hP a b hab]
  · have : Matrix.single a b (P a b) = P a b • eNC (⟨(a, b), hab⟩ : NC R S) := by
      simp [eNC, Eab, Matrix.smul_single]
    rw [this, map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (filt_X act N _ v hv)

lemma filt_KC (hlie : IsLieAct act) (hN : KStable act N) {Z : Mat R S} (hZ : IsKC Z) {m : ℕ} :
    ∀ v ∈ filt act N m, act Z v ∈ filt act N m := by
  have key : ∀ (j : ℕ) (h : Fin j → NC R S) (n : N), act Z (word act h n) ∈ filt act N j := by
    intro j
    induction j with
    | zero =>
      intro h n
      have := word_mem act N le_rfl h ⟨act Z n, hN Z hZ n n.2⟩
      rwa [word_zero, Module.End.one_apply] at this ⊢
    | succ j ih =>
      intro h n
      rw [word_succ, Module.End.mul_apply]
      have hw : word act (Fin.tail h) n ∈ filt act N j := word_mem act N le_rfl _ n
      have e : act Z (act (eNC (h 0)) (word act (Fin.tail h) n)) =
          act (eNC (h 0)) (act Z (word act (Fin.tail h) n)) +
            act (Z * eNC (h 0) - eNC (h 0) * Z) (word act (Fin.tail h) n) := by
        rw [hlie, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [e]
      exact add_mem (filt_X act N _ _ (ih _ n)) (act_pc_mem act N (isPC_comm_KC hZ (isPC_eNC _)) _ hw)
  intro v hv
  exact filt_map act N (act Z) (fun j hj h n => filt_mono act N hj (key j h n)) v hv

lemma comm_word (hlie : IsLieAct act) (hN : KStable act N) (x : NC R S) {m : ℕ} :
    ∀ {j : ℕ} (h : Fin j → NC R S), ∀ v ∈ filt act N m,
      act (eNC x) (word act h v) - word act h (act (eNC x) v) ∈ filt act N (m + j) := by
  intro j
  induction j with
  | zero => intro h v hv; simp [word_zero]
  | succ j ih =>
    intro h v hv
    rw [word_succ, Module.End.mul_apply, Module.End.mul_apply]
    have e : act (eNC x) (act (eNC (h 0)) (word act (Fin.tail h) v)) -
        act (eNC (h 0)) (word act (Fin.tail h) (act (eNC x) v)) =
        act (eNC x * eNC (h 0) - eNC (h 0) * eNC x) (word act (Fin.tail h) v) +
          act (eNC (h 0)) (act (eNC x) (word act (Fin.tail h) v) - word act (Fin.tail h) (act (eNC x) v)) := by
      rw [hlie, map_sub, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
    rw [e]
    refine add_mem ?_ (filt_X act N _ _ (ih (Fin.tail h) v hv))
    exact filt_mono act N (by omega)
      (filt_KC act N hlie hN (isKC_comm_PC (isPC_eNC x) (isPC_eNC _)) _ (filt_word act N _ v hv))

lemma sum_cons {k : ℕ} {β : Type} [AddCommMonoid β] (f : (Fin (k + 1) → NC R S) → β) :
    ∑ g, f g = ∑ x, ∑ g' : Fin k → NC R S, f (Fin.cons x g') := by
  rw [← Fintype.sum_prod_type' (fun x (g' : Fin k → NC R S) => f (Fin.cons x g'))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => NC R S) _ _ (fun p => rfl)).symm

lemma phiN_succ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N) :
    phiN act N (k + 1) Ψ = ∑ x, act (eNC x) (phiN act N k (fun g' => Ψ (Fin.cons x g'))) := by
  rw [phiN_apply, sum_cons]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [phiN_apply, map_sum]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [word_cons, Module.End.mul_apply]

lemma position_zero (hlie : IsLieAct act) (hN : KStable act N) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N)
    (hΨ : ∀ g, phiN act N 1 (section1 Ψ 0 g) = 0) : phiN act N (k + 1) Ψ ∈ filt act N k := by
  have hsum : ∀ g' : Fin k → NC R S, ∑ x, act (eNC x) (Ψ (Fin.cons x g') : V) = 0 := by
    intro g'
    rcases isEmpty_or_nonempty (NC R S) with hE | ⟨⟨x0⟩⟩
    · simp [Finset.univ_eq_empty]
    · have e2 : phiN act N 1 (section1 Ψ 0 (Fin.cons x0 g')) = ∑ x, act (eNC x) (Ψ (Fin.cons x g') : V) := by
        rw [phiN_apply]
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ fun h => ?_
        simp [section1, word, Fin.update_cons_zero]
      rw [← e2, hΨ]
  rw [phiN_apply, sum_cons]
  have e3 : ∀ x (g' : Fin k → NC R S), word act (Fin.cons x g' : Fin (k + 1) → NC R S) (Ψ (Fin.cons x g') : V) =
      word act g' (act (eNC x) (Ψ (Fin.cons x g'))) +
        (act (eNC x) (word act g' (Ψ (Fin.cons x g'))) - word act g' (act (eNC x) (Ψ (Fin.cons x g')))) := by
    intro x g'; rw [word_cons, Module.End.mul_apply]; abel
  simp_rw [e3, Finset.sum_add_distrib]
  have hmain : ∑ x, ∑ g' : Fin k → NC R S, word act g' (act (eNC x) (Ψ (Fin.cons x g') : V)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun g' _ => ?_
    rw [← map_sum, hsum g', map_zero]
  rw [hmain, zero_add]
  refine Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun g' _ => ?_
  simpa using comm_word act N hlie hN x g' _ (mem_filt_zero act N (Ψ (Fin.cons x g')))

theorem position_rel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ (k : ℕ) (i : Fin (k + 1))
    (Ψ : (Fin (k + 1) → NC R S) → N), (∀ g, phiN M.act N 1 (section1 Ψ i g) = 0) →
    phiN M.act N (k + 1) Ψ ∈ filt M.act N k := by
  intro R S M N hN k
  induction k with
  | zero =>
    intro i Ψ hΨ
    obtain rfl : i = 0 := Fin.ext (by omega)
    exact position_zero M.act N M.lie hN 0 Ψ hΨ
  | succ k ih =>
    intro i Ψ hΨ
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact position_zero M.act N M.lie hN _ Ψ hΨ
    · rw [phiN_succ]
      refine Submodule.sum_mem _ fun y _ => filt_X M.act N y _ (ih i' _ fun g' => ?_)
      have : section1 (fun g' => Ψ (Fin.cons y g')) i' g' = section1 Ψ i'.succ (Fin.cons y g') := by
        funext h; simp only [section1, Fin.cons_update]
      rw [this]; exact hΨ _

end GlobalTheory.PositionRel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOpenHopfOrder
section
open Matrix Polynomial
open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

namespace GlobalTheory.SemilocalConj

theorem exists_cyclic_of_finite_maximal {R : Type} [CommRing R]
    (hfin : Set.Finite {I : Ideal R | I.IsMaximal}) {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hs : g.charpoly.Separable) : ∃ v, IsUnit (krylov g v).det := by
  classical
  haveI : Finite (MaximalSpectrum R) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum R =>
      (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal}))
      (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))
  have hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} →
    ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable →
      ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  intro R _ hfin n γ δ hχ hs
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_maximal hfin γ hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := GlobalTheory.Orb.mul_krylov_eq γ v
  have h2 := GlobalTheory.Orb.mul_krylov_eq δ w
  rw [← ha] at h1
  rw [← hb, ← hχ] at h2
  refine ⟨a * b⁻¹, ?_⟩
  set C := GlobalTheory.Orb.companionMat n γ.charpoly
  rw [Units.val_mul]
  calc (a : Matrix (Fin n) (Fin n) R) * ↑b⁻¹ * δ = ↑a * ↑b⁻¹ * (δ * ↑b) * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]
    _ = ↑a * C * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = γ * ↑a * ↑b⁻¹ := by rw [h1]
    _ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]

example : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u :=
  conj_of_charpoly_eq_of_separable

end GlobalTheory.SemilocalConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentPolynomialOfIsAlgCloseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial K)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial K)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.gm_algClosed_cohomology) | (exact GlobalTheory.EtC.gm_algClosed_cohomology) | (intros; apply GlobalTheory.EtC.gm_algClosed_cohomology  <;> assumption)
end

