import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem conj_perm_entry {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (p q : Fin N) :
    ((GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) (w p) (w q) = (g : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv]
  change ((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd p) < blk (stdBlocks d hd) (wOpen d hd q)) : q < p := by
  by_contra hqp
  have hm := Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)
  change wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm
  unfold wKey at hm
  rw [Prod.Lex.le_iff] at hm
  simp only [ofLex_toLex] at hm
  rcases hm with hlt | ⟨heq, _⟩
  · exact lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)
  · rw [OrderDual.toDual_inj] at heq
    rw [heq] at hb
    exact lt_irrefl _ hb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem mem_unipU {u : GL (Fin N) k} : u ∈ unipU k d hd ↔
    u ∈ unipB k (Fin N) ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  exact Iff.rfl

theorem mem_unipL {u : GL (Fin N) k} : u ∈ unipL k d hd ↔
    u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ (leviEmb k (stdBlocks d hd)).range := by
  exact Iff.rfl

theorem conj_mem_parabLower {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹ ∈ parabLower k (stdBlocks d hd) := by
  rw [GlobalTheory.SmGL.mem_parabLower_iff k]
  intro a b i j hab
  obtain ⟨p, hp⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)
  obtain ⟨q, hq⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)
  rw [← hp, ← hq]
  unfold pm
  rw [conj_perm_entry]
  apply ((GlobalTheory.SmGL.mem_unipB k).mp hn).1
  apply lt_of_blk_lt d hd
  rw [hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  exact hab

theorem exists_mul {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u := by
  have hc0 := conj_mem_parabLower k d hd hn
  set P := pm k (wOpen d hd) with hP
  set e := stdBlocks d hd with he
  have hc : P * n * P⁻¹ ∈ parab k (opp e) := hc0
  obtain ⟨v, hv, hcv⟩ := exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩
  set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL
  have hcv' : P * n * P⁻¹ = L * v := hcv
  have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q =
      if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by
    intro p q
    have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q
    simp only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group] at h1
    rw [← h1]
    obtain ⟨⟨x, i⟩, hxi⟩ := e.surjective (wOpen d hd p)
    obtain ⟨⟨y, j⟩, hyj⟩ := e.surjective (wOpen d hd q)
    rw [← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
    split_ifs with hxy
    · subst hxy
      refine (GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_
      refine (GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_
      change ((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _
      rw [hxi, hyj]
      exact conj_perm_entry (wOpen d hd) n p q
    · exact GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j
  have haB : P⁻¹ * L * P ∈ unipB k (Fin N) := by
    rw [GlobalTheory.SmGL.mem_unipB k]
    refine ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hLentry]
      split_ifs
      · exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp
      · rfl
    · rw [hLentry, if_pos rfl]
      exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p
  refine ⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩
  · rw [mem_unipL k d hd]
    refine ⟨haB, ?_⟩
    show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group]
    exact ⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩
  · rw [mem_unipU k d hd]
    refine ⟨?_, ?_⟩
    · have hv' : v = L⁻¹ * (P * n * P⁻¹) := by
        rw [hcv']
        group
      rw [show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn
    · show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e
      rw [show P * (P⁻¹ * v * P) * P⁻¹ = v by group]
      exact hv
  · rw [show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv']
    group

theorem conj_mem_unipU {n u : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) (hu : u ∈ unipU k d hd) :
    n * u * n⁻¹ ∈ unipU k d hd := by
  rw [mem_unipU k d hd] at hu ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩
  have hN := GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)
  have key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ =
      (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) *
        (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹ := by group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hu.2

end GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn,
    fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
section
namespace GlobalTheory.CompanionTheory.DiscreteSeries

private lemma two_mul_rhoN_add_rhoC_eq_card_sub_card {n : ℕ} (ε : Fin n → Bool) (x : Fin n) :
    2 * (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) =
      (({y | x < y} : Finset (Fin n)).card : ℝ) - (({y | y < x} : Finset (Fin n)).card : ℝ) := by
  have hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | x < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hA
  have hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | y < x} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hB
  simp only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  linarith

private lemma rhoN_add_rhoC_le_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    Formalism.REAL.rhoN ε b + Formalism.REAL.rhoC ε b ≤ Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a := by
  have h1 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε a
  have h2 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε b
  have c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hab hy
  have c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hy hab
  have c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c1
  have c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c2
  linarith

private lemma nsq_le_nsq_add_of_dot_nonneg {n : ℕ} (v w : Fin n → ℝ) (h : 0 ≤ Formalism.REAL.dot v w) :
    Formalism.REAL.nsq v ≤ Formalism.REAL.nsq (v + w) := by
  unfold Formalism.REAL.nsq Formalism.REAL.dot at *
  have h2 : 0 ≤ ∑ a, w a * w a := Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))
  have e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)
  rw [e]
  linarith

private lemma dot_nonneg_sum_root_of_antitone {n : ℕ} (v : Fin n → ℝ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b : Fin n, c a b ≠ 0 → a < b) (hmono : ∀ a b : Fin n, a < b → v b ≤ v a) :
    0 ≤ Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) := by
  have hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)
      = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b) := by
    unfold Formalism.REAL.dot
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hdot]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))

open GlobalTheory.LowestKTypeDetermines in

theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam := by rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm]
  apply nsq_le_nsq_add_of_dot_nonneg
  apply dot_nonneg_sum_root_of_antitone _ c hc
  intro a b hab
  simp only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]
  have h1 := rhoN_add_rhoC_le_of_lt ε hab
  have h2 := hlam.1 hab
  linarith

end GlobalTheory.CompanionTheory.DiscreteSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCharacterNontrivialOnCell
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RootElt

def elemGL {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) : GL (Fin N) k where
  val := Matrix.transvection i j t
  inv := Matrix.transvection i j (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

theorem elemGL_apply {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) (a b : Fin N) :
    (elemGL i j hij t).val a b = (1 : Matrix (Fin N) (Fin N) k) a b + if a = i ∧ b = j then t else 0 := by
  show Matrix.transvection i j t a b = _
  rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩]

theorem conj_pm_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (a b : Fin N) :
    (GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹).val a b = g.val (w⁻¹ a) (w⁻¹ b) := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]

theorem exists_root_conj_mem_unipRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)) (i j : Fin N), (j : ℕ) = i + 1 → blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j) → ∀ t : k, ∃ (u : GL (Fin N) k) (hu : u ∈ unipB k (Fin N)), whitChar ψ N ⟨u, hu⟩ = Circle.toUnits (ψ t) ∧ pm k w * u * (pm k w)⁻¹ ∈ unipRad k (stdBlocks d hd) := by
  intro k _ _ _ _ ψ h N d hd w i j hij hb t
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hu : elemGL i j hne t ∈ unipB k (Fin N) := by
    refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [elemGL_apply, Matrix.one_apply_ne hba.ne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hba
      exact absurd hba hlt.not_gt
    · rw [elemGL_apply, Matrix.one_apply_eq, if_neg fun e => hne (e.1.symm.trans e.2), add_zero]
  refine ⟨elemGL i j hne t, hu, ?_, ?_⟩
  · show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (elemGL i j hne t).val p.1 p.2)) = _
    congr 2
    rw [Finset.sum_eq_single_of_mem (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)]
    · rw [elemGL_apply, Matrix.one_apply_ne hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · rintro ⟨a, b⟩ hp hpne
      have hab : (b : ℕ) = a + 1 := (Finset.mem_filter.1 hp).2
      have hne' : a ≠ b := fun e => by rw [e] at hab; omega
      rw [elemGL_apply, Matrix.one_apply_ne hne', if_neg fun e => hpne (Prod.ext e.1 e.2), add_zero]
  · have hent : ∀ a b : Fin N, (pm k w * elemGL i j hne t * (pm k w)⁻¹).val a b =
        (1 : Matrix (Fin N) (Fin N) k) a b + if a = w i ∧ b = w j then t else 0 := by
      intro a b
      rw [conj_pm_apply, elemGL_apply]
      congr 1
      · by_cases e : a = b
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (w⁻¹.injective e')]
      · simp only [Equiv.Perm.inv_eq_iff_eq]
    refine mem_unipRad.2 ⟨mem_parab.2 fun a b hab => ?_, fun c x y => ?_⟩
    · have hne' : a ≠ b := fun e => by rw [e] at hab; exact lt_irrefl _ hab
      rw [hent, Matrix.one_apply_ne hne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hab
      exact lt_asymm hab hb
    · rw [hent, if_neg fun e => ?_, add_zero]
      · by_cases e : x = y
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (by simpa using (stdBlocks d hd).injective e')]
      · have h1 := blk_apply (stdBlocks d hd) c x
        have h2 := blk_apply (stdBlocks d hd) c y
        rw [e.1] at h1
        rw [e.2] at h2
        rw [h1, h2] at hb
        exact lt_irrefl _ hb

end GlobalTheory.CompanionTheory.Rodier.RootElt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevel
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.ChartRed

theorem etale_of_quot {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] (f : R →+* S)
    (hf : f.Etale) (g : R →+* R') (hg : Function.Surjective g) (h : S →+* S') (hh : Function.Surjective h)
    (f' : R' →+* S') (comm : f'.comp g = h.comp f) (hk : RingHom.ker h = (RingHom.ker g).map f) : f'.Etale := by
  letI := f.toAlgebra
  haveI : Algebra.Etale R S := hf
  set P := RingHom.ker g with hP
  have het : Algebra.Etale (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S P).symm
  have h0 : (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S))).Etale := RingHom.etale_algebraMap.2 het
  let e1 : (R ⧸ P) ≃+* R' := RingHom.quotientKerEquivOfSurjective hg
  let e2 : (S ⧸ P.map (algebraMap R S)) ≃+* S' :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hh)
  have key : f' = (e2.toRingHom.comp (algebraMap (R ⧸ P) (S ⧸ P.map (algebraMap R S)))).comp e1.symm.toRingHom := by
    refine RingHom.ext fun r' => ?_
    obtain ⟨r, rfl⟩ := hg r'
    have h1 : e1.symm (g r) = Ideal.Quotient.mk P r := by
      rw [RingEquiv.symm_apply_eq]; rfl
    have h2 : f' (g r) = h (f r) := RingHom.congr_fun comm r
    change _ = e2 (algebraMap _ _ (e1.symm (g r)))
    rw [h1, h2]
    rfl
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e1.symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ h0 (RingHom.Etale.of_bijective e2.bijective))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l]

theorem ker_red (n : ℕ) : RingHom.ker (Wc.red l k n) =
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) ((l : WittVector l k) ^ n))} := by
  unfold Wc.red
  rw [Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]

theorem red_surj (n : ℕ) : Function.Surjective (Wc.red l k n) :=
  Ideal.Quotient.factor_surjective _

theorem map_Im (n : ℕ) : (Wc.Im l k (n + 1)).map (Wc.red l k n) = Wc.Im l k n := by
  unfold Wc.Im
  rw [Ideal.map_map]
  rfl

variable {O : Type} [CommRing O] {F : B.Fn O} {ρ : O →+* k} {n : ℕ}

theorem etale_q (T : Thick (Wc.L l F ρ (n + 1))) {d : ℕ} (t : Fin d → T.B)
    (h : (MvPolynomial.eval₂Hom T.i t : MvPolynomial (Fin d) (Wc.Wm l k (n + 1)) →+* T.B).Etale) :
    (MvPolynomial.eval₂Hom (qi T) (fun i => Ideal.Quotient.mk (lI n T) (t i)) :
      MvPolynomial (Fin d) (Wc.Wm l k n) →+* T.B ⧸ lI n T).Etale := by
  refine etale_of_quot _ h (MvPolynomial.map (Wc.red l k n)) (MvPolynomial.map_surjective _ (red_surj n))
    (Ideal.Quotient.mk (lI n T)) Ideal.Quotient.mk_surjective _ ?_ ?_
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [qi_red]
    · simp
  · rw [Ideal.mk_ker, MvPolynomial.ker_map, ker_red, Ideal.map_map, Ideal.map_span, Set.image_singleton]
    simp [lI]

theorem J_q (T : Thick (Wc.L l F ρ (n + 1))) (h : T.J = (Wc.Im l k (n + 1)).map T.i) :
    T.J.map (Ideal.Quotient.mk (lI n T)) = (Wc.Im l k n).map (qi T) := by
  have e : (Ideal.Quotient.mk (lI n T)).comp T.i = (qi T).comp (Wc.red l k n) :=
    RingHom.ext fun r => (qi_red T r).symm
  calc T.J.map (Ideal.Quotient.mk (lI n T))
      = ((Wc.Im l k (n + 1)).map T.i).map (Ideal.Quotient.mk (lI n T)) := by rw [← h]
    _ = (Wc.Im l k (n + 1)).map ((Ideal.Quotient.mk (lI n T)).comp T.i) := Ideal.map_map _ _
    _ = (Wc.Im l k (n + 1)).map ((qi T).comp (Wc.red l k n)) := by rw [e]
    _ = ((Wc.Im l k (n + 1)).map (Wc.red l k n)).map (qi T) := (Ideal.map_map _ _).symm
    _ = (Wc.Im l k n).map (qi T) := by rw [map_Im n]

abbrev rr (n : ℕ) : Wc.Wm l k (n + 1) ⧸ Wc.Im l k (n + 1) →+* Wc.Wm l k n ⧸ Wc.Im l k n :=
  Ideal.quotientMap _ (Wc.red l k n) (Ideal.map_le_iff_le_comap.1 (Wc.dp_red l k n).1)

theorem rr_surj (n : ℕ) : Function.Surjective (rr (l := l) (k := k) n) :=
  Ideal.quotientMap_surjective (red_surj n)

theorem qy_rr (T : Thick (Wc.L l F ρ (n + 1))) : (qy T).comp (rr n) = (qe T).comp T.y.1.1 := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have h := T.w r
  change qy T (rr n (Ideal.Quotient.mk _ r)) = qe T ((Wc.L l F ρ (n + 1)).str T.y (Ideal.Quotient.mk _ r))
  rw [h]
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

theorem qe_bij (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) : Function.Bijective (qe T) := by
  refine ⟨?_, Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : Ideal.Quotient.mk (lI n T) x ∈ T.J.map (Ideal.Quotient.mk (lI n T)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 ha
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (lI_le hn T)] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.2 h1

section Abs

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem map_eq_iff {κ' : Type} [CommRing κ'] {κ : O →+* κ'} {A : CommRingCat.{0}} {C : Type} [CommRing C]
    (φ : C →+* A) (z : PtOver X q κ C) (y : PtOver X q κ A) :
    (ptFun X q κ).map (CommRingCat.ofHom φ) z = y ↔
      φ.comp z.1.1 = y.1.1 ∧ Spec.map (CommRingCat.ofHom φ) ≫ z.1.2 = y.1.2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)

theorem rep_abs {K₁ K₂ C₁ C₂ : Type} [CommRing K₁] [CommRing K₂] [CommRing C₁] [CommRing C₂] {κ₁ : O →+* K₁}
    {κ₂ : O →+* K₂} (r : K₁ →+* K₂) (hr : Function.Surjective r) (hκ : r.comp κ₁ = κ₂) (e : C₁ →+* C₂)
    (he : Function.Bijective e) (z₁ : PtOver X q κ₁ C₁) (z₂ : PtOver X q κ₂ C₂) (h1 : z₂.1.1.comp r = e.comp z₁.1.1)
    (h2 : z₂.1.2 = Spec.map (CommRingCat.ofHom e) ≫ z₁.1.2) {V : X.Opens}
    (hrep : ∀ (A : CommRingCat.{0}) (y : PtOver X q κ₁ A), ⊤ ≤ y.1.2 ⁻¹ᵁ V →
      ∃! φ : C₁ →+* A, (ptFun X q κ₁).map (CommRingCat.ofHom φ) z₁ = y)
    (A : CommRingCat.{0}) (y : PtOver X q κ₂ A) (hy : ⊤ ≤ y.1.2 ⁻¹ᵁ V) :
    ∃! φ : C₂ →+* A, (ptFun X q κ₂).map (CommRingCat.ofHom φ) z₂ = y := by
  let y' : PtOver X q κ₁ A := ⟨(y.1.1.comp r, y.1.2), by
    have h := y.2
    rw [RingHom.comp_assoc, hκ]
    exact h⟩
  obtain ⟨φ', h', hu⟩ := hrep A y' hy
  rw [map_eq_iff] at h'
  let E := RingEquiv.ofBijective e he
  have hE : ∀ x, E.symm (e x) = x := fun x => E.symm_apply_apply x
  have hE' : ∀ x, e (E.symm x) = x := fun x => E.apply_symm_apply x
  have hcomp : (φ'.comp E.symm.toRingHom).comp e = φ' := RingHom.ext fun x => by simp [hE]
  have hsp : ∀ ψ : C₂ →+* A, Spec.map (CommRingCat.ofHom ψ) ≫ z₂.1.2 =
      Spec.map (CommRingCat.ofHom (ψ.comp e)) ≫ z₁.1.2 := fun ψ => by
    rw [h2, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨φ'.comp E.symm.toRingHom, ?_, fun ψ hψ => ?_⟩
  · refine (map_eq_iff _ _ _).2 ⟨?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      obtain ⟨a, rfl⟩ := hr x
      have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
      have e2 : φ' (z₁.1.1 a) = y.1.1 (r a) := RingHom.congr_fun h'.1 a
      change φ' (E.symm (z₂.1.1 (r a))) = _
      rw [e1, hE, e2]
    · rw [hsp, hcomp]
      exact h'.2
  · obtain ⟨g1, g2⟩ := (map_eq_iff _ _ _).1 hψ
    have : ψ.comp e = φ' := by
      refine hu _ ((map_eq_iff _ _ _).2 ⟨?_, ?_⟩)
      · refine RingHom.ext fun a => ?_
        have e1 : z₂.1.1 (r a) = e (z₁.1.1 a) := RingHom.congr_fun h1 a
        have e2 : ψ (z₂.1.1 (r a)) = y.1.1 (r a) := RingHom.congr_fun g1 (r a)
        change ψ (e (z₁.1.1 a)) = y.1.1 (r a)
        rw [← e1, e2]
      · rw [← hsp]
        exact g2
    rw [← this]
    refine RingHom.ext fun x => ?_
    change ψ x = ψ (e (E.symm x))
    rw [hE']

end Abs

abbrev tD {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k} {m : ℕ} {W : X.Opens}
    {d : ℕ} (c' : Chart (Wc.pd l k m) l q ((Wc.res l k m).comp ρ) W d) : Thick (Wc.L l (B.schFn q) ρ m) := c'.D

def cq {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d where
  D := qT (F := B.schFn q) (ρ := ρ) hn (tD c')
  t := fun i => Ideal.Quotient.mk (lI n (tD c')) (c'.t i)
  etale := etale_q (tD c') c'.t c'.etale
  J_eq := J_q (tD c') c'.J_eq
  inV := inU_qT q ρ hn (tD c') c'.inV
  rep := rep_abs (rr n) (rr_surj n) (Wc.red_res l ρ n) (qe (tD c')) (qe_bij hn (tD c')) (tD c').y
    (qT (F := B.schFn q) (ρ := ρ) hn (tD c')).y (qy_rr (tD c')) rfl c'.rep

theorem chart_q {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ}
    (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d) :
    ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d)
      (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D),
      (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧
        (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) :=
  ⟨cq q ρ hn c', Iso.refl _, fun i => rfl, id⟩

end GlobalTheory.CompanionTheory.ChartRed

end
end

