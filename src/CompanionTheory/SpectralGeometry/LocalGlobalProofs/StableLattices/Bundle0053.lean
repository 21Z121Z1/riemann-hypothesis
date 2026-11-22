import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeight
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.TopU

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    ann i x B = if i ∈ B then 0 else CompanionTheory.D.LK.sg i B • x (insert i B) := rfl

theorem cre_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i x B = if i ∈ B then CompanionTheory.D.LK.sg i B • x (B.erase i) else 0 := rfl

theorem sg_erase (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i (B.erase i) = CompanionTheory.D.LK.sg i B := by
  unfold CompanionTheory.D.LK.sg
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sg_sq (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i B * CompanionTheory.D.LK.sg i B = 1 := by
  unfold CompanionTheory.D.LK.sg; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem cre_ann (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i (ann i x) B = if i ∈ B then x B else 0 := by
  rw [cre_app]
  split_ifs with h
  · rw [ann_app, if_neg (notMem_erase i B), insert_erase h, sg_erase, smul_smul, sg_sq, one_smul]
  · rfl

theorem adC_self (a : Fin n) (i k : Pos n) :
    adC a a i k = if k = i then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0 := by
  unfold adC
  have e1 : (a = i.1.1 ∧ k.1 = (a, i.1.2)) ↔ (k = i ∧ i.1.1 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext h1 rfl)), h1.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨h.symm, Prod.ext h rfl⟩
  have e2 : (i.1.2 = a ∧ k.1 = (i.1.1, a)) ↔ (k = i ∧ i.1.2 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext rfl h1.symm)), h1⟩
    · rintro ⟨rfl, h⟩; exact ⟨h, Prod.ext rfl h⟩
  simp only [e1, e2]
  by_cases hk : k = i <;> simp [hk]

theorem adL_self_apply (a : Fin n) (x : Cn n V) (B : Finset (Pos n)) :
    adL a a x B = ∑ i : Pos n, (((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ)) •
      cre i (ann i x) B := by
  simp only [adL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply,
    adC_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem top_cycle_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  intro n ε lev V _ _ E γ u _ hu
  have memA : ∀ i : Pos n, i ∈ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := fun i => by simp [omU]
  refine ⟨?_, fun a => ?_⟩
  · funext B
    rw [CompanionTheory.D.LK.bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := CompanionTheory.D.LK.tri_ne h
        have e : insert i (insert j (B.erase k)) = omU ε lev := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci := (memA i).1 (e ▸ mem_insert_self _ _)
        have cj := (memA j).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have ck : k ∈ omU ε lev := (memA k).2
          ⟨by rw [t2, t3, ci.1, t1]; exact cj.1,
           by rw [t2, t3]; exact (ci.2.trans_eq (congrArg lev t1)).trans cj.2⟩
        rw [← e] at ck
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_app]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i B = omU ε lev
        · have hiA := (memA i).1 (e ▸ mem_insert_self i B)
          rw [e, Pi.single_eq_same, map_smul, hu.2 _ _ i.2 hiA.1, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext B
    show E a a ((Pi.single (omU ε lev) u : Cn n V) B) + adL a a (Pi.single (omU ε lev) u) B = _
    rw [adL_self_apply]
    simp only [cre_ann]
    by_cases e : B = omU ε lev
    · subst e
      rw [Pi.single_eq_same, hu.1 a, Pi.smul_apply, Pi.single_eq_same]
      have hs : ∀ i : Pos n, ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) •
          (if i ∈ omU ε lev then u else 0) =
          (if i ∈ omU ε lev then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0) • u := by
        intro i; split_ifs <;> simp
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_smul, ← add_smul]
      congr 1
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter, Finset.sum_sub_distrib, Finset.sum_boole,
        Finset.sum_boole]
      simp only [wt]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne e]

end GlobalTheory.CompanionTheory.RgCOBlock.TopU
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgStart

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S GlobalTheory.Count

variable {n : ℕ} {ε : Fin n → Bool}

theorem measurable_modA (A : Matrix (Fin n) (Fin n) ℂ) : Measurable (modA (ε := ε) A) := by
  unfold modA
  have h1 : Measurable fun τ : Fin 1 → ℝ => layerProd n 1 (fun _ : Fin 1 => rk A) τ id := by
    unfold layerProd
    simp only [id]
    fun_prop
  exact (h1.comp (measurable_pi_lambda _ fun i =>
    measurable_locSize_uMat n ε 1 (fun _ : Fin 1 => rk A) (W A) i)).ennreal_ofReal

theorem detOn_pos_of_left_inv {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  classical
  have h : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  unfold detOn
  rw [dif_pos h]
  refine norm_pos_iff.mpr fun h0 => ?_
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero h0)
  have h1 : f *ᵥ (x : Fin n → ℂ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    simpa [Matrix.toLin'_apply] using this
  have h2 : (x : Fin n → ℂ) = 0 := by
    have := congrArg (g *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, hgf] using this
  exact hx0 (by simpa using Subtype.ext h2)

theorem modA_ne_zero (A : Matrix (Fin n) (Fin n) ℂ) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) :
    modA A m ≠ 0 := by
  have hinv : (((m : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      uMat m = 1 := Units.inv_mul _
  have hd : ∀ i, 0 < detOn (uMat m) (W A i) := fun i =>
    detOn_pos_of_left_inv hinv _ fun y hy => (hm i y hy).1
  have hτ : ∀ i : Fin 1, 0 < locSize (fun _ : Fin 1 => rk A) (W A) (uMat m) i := fun i =>
    Real.rpow_pos_of_pos (div_pos (hd _) (hd _)) _
  have hp : 0 < layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id := by
    unfold layerProd
    simp only [id]
    exact mul_pos (prod_pos fun i _ => prod_pos fun k _ =>
        mul_pos (pow_pos (div_pos (hτ i) (hτ k)) _) (pow_pos (mul_pos (hτ i) (hτ k)) _))
      (prod_pos fun i _ => mul_pos (pow_pos (hτ i) _) (pow_pos (pow_pos (hτ i) _) _))
  unfold modA
  exact (ENNReal.ofReal_pos.mpr hp).ne'

theorem startOf : StartOf := by
  intro _ _ hLine hSlab hFub hKMaj n ε H _ _ _ σ D E hK hU hL2 A μ hA hμ u ξ
  obtain ⟨F, hFm, hFK, hFint, hFle⟩ := hKMaj n ε H σ D E hK hU hL2 u ξ
  obtain ⟨μN, μM, hN, hM, hMS, hMinv, ⟨κ, hκ0, hκt, hκ⟩, hnull⟩ := hFub n ε A hA
  obtain ⟨a, τ, ha, hτ, haM, hadd, haS, hcent, hmod, htime⟩ := hLine n ε A hA
  haveI := hN
  haveI := hM
  obtain ⟨⟨Msub, eM⟩, hS, -⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
  have hfin : (∫⁻ v, ∫⁻ m, modA A m * F (v * m) ∂μM ∂μN) < ⊤ := by
    have h := hFint
    rw [hκ F hFm hFK] at h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne hκ0
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ flagN ε (W A) := by
    refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
      · rw [GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _
  have hsl := hSlab (Formalism.REAL.UJ ε) μN μM (flagM ε (W A)) a (modA A) τ (rhoA A) hS.measurableSet hMS ha.measurable
    (measurable_modA A) hτ hadd
    (fun m hm t => by
      have : m * a t ∈ Msub := Msub.mul_mem (by rw [← SetLike.mem_coe, eM]; exact hm)
        (by rw [← SetLike.mem_coe, eM]; exact haS t)
      rw [← eM]; exact this)
    (fun t => hMinv (a t) (haS t) (hcent t)) hmod
    (fun m hm t => by simpa using htime 1 h1N m hm t)
    (fun m hm => modA_ne_zero A hm) F hFm hfin
  let I : Formalism.REAL.UJ ε → ℝ≥0∞ := fun x =>
    ∫⁻ t in Set.Ioi (0 : ℝ), F (x * a t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))
  have hI : Measurable I := Measurable.lintegral_prod_right'
    (f := fun p : Formalism.REAL.UJ ε × ℝ => F (p.1 * a p.2) * ENNReal.ofReal (Real.exp (2 * rhoA A * p.2)))
    ((hFm.comp (measurable_fst.mul (ha.measurable.comp measurable_snd))).mul (by fun_prop))
  have hE : MeasurableSet (I ⁻¹' {⊤}) := hI (measurableSet_singleton ⊤)
  have h0 : (μN.prod μM) {p | p.1 * p.2 ∈ I ⁻¹' {⊤}} = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.mp hsl)
    have hp' : I (p.1 * p.2) = ⊤ := hp
    show ¬ I (p.1 * p.2) < ⊤
    rw [hp']
    exact lt_irrefl _
  have hμE : μ (I ⁻¹' {⊤}) = 0 := hnull μ hμ _ hE h0
  have hae : ∀ᵐ x ∂μ, I x ≠ ⊤ := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hμE)
    exact not_not.mp hx
  have hle : ∀ y : Formalism.REAL.UJ ε, lineInt ε (baseCoef σ D ξ u) A (-rhoA A) y ≤ I y := by
    intro y
    unfold lineInt
    refine lintegral_mono fun t => ?_
    have e1 : S7.toM y * NormedSpace.exp ((t : ℂ) • A) = uMat (y * a t) := by
      rw [← haM t]
      rfl
    have e2 : Real.exp (-2 * (-rhoA A) * t) = Real.exp (2 * rhoA A * t) := by
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul' (hFle _) le_rfl
  filter_upwards [hae] with x hx
  exact lt_of_le_of_lt (hle x) (lt_top_iff_ne_top.mpr hx)

end GlobalTheory.CompanionTheory.RgStart
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBound
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

theorem card_first_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.1 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.1 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.2) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) hxy))
  simpa using h

theorem card_second_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.2 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.2 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.1) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext hxy (h1.trans h2.symm)))
  simpa using h

theorem abs_wt_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) : |wt A c| ≤ n := by
  have h1 : (((A.filter fun i => i.1.1 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_first_le A c
  have h2 : (((A.filter fun i => i.1.2 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_second_le A c
  have h3 : (0 : ℝ) ≤ ((A.filter fun i => i.1.1 = c).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((A.filter fun i => i.1.2 = c).card : ℕ) := Nat.cast_nonneg _
  unfold wt
  rw [abs_le]
  constructor <;> linarith

theorem abs_two_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    |(2 : ℝ) * PI.UpqRep.rhoC ε a| ≤ n := by
  have h1 : (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h2 : (((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  unfold PI.UpqRep.rhoC
  rw [abs_le]
  constructor <;> linarith

theorem abs_modExp_le {M N : ℕ} (d : Fin M → ℕ) (h : ∑ j, d j = N) (i : Fin M) :
    |modExp (fun j => Fin (d j)) i| ≤ (N : ℤ) := by
  have hN : ∑ j, (d j : ℤ) = N := by exact_mod_cast h
  have key : ∀ p : Fin M → Prop, ∀ [DecidablePred p],
      (0 : ℤ) ≤ ∑ b with p b, (d b : ℤ) ∧ ∑ b with p b, (d b : ℤ) ≤ N := fun p _ =>
    ⟨sum_nonneg fun _ _ => Int.natCast_nonneg _, hN ▸ sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _⟩
  obtain ⟨a1, a2⟩ := key (fun b => i < b)
  obtain ⟨b1, b2⟩ := key (fun b => b < i)
  simp only [modExp, Fintype.card_fin]
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem norm_cluster_sum_le (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n) :
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsz : ((sz lev M i : ℕ) : ℝ) ≤ n := by
    have : sz lev M i ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast this
  have hsz0 : (0 : ℝ) ≤ ((sz lev M i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) ≤ n := by
    exact_mod_cast ClusterBound.abs_modExp_le (sz lev M) h i
  have hm0 : (0 : ℝ) ≤ ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) := by
    exact_mod_cast abs_nonneg _
  have hterm : ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ‖((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) := by
    intro a _
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := ClusterBound.abs_wt_le (omU ε lev) a
    have h2 := ClusterBound.abs_two_rhoC_le ε a
    have h3 := abs_sub (wt (omU ε lev) a) ((2 : ℝ) * PI.UpqRep.rhoC ε a)
    linarith
  have hsum : ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤
      ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) := by
    refine (norm_sum_le_of_le _ hterm).trans_eq ?_
    rw [sum_const, nsmul_eq_mul]
    rfl
  have hmod : ‖(sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2)‖ =
      ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_intCast]
    simp
  refine (norm_sub_le _ _).trans ?_
  rw [hmod]
  have e1 : ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) ≤ (n : ℝ) * (2 * n) :=
    mul_le_mul_of_nonneg_right hsz (by positivity)
  have e2 : ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) ≤
      (n : ℝ) * ((n : ℝ) / 2) :=
    mul_le_mul hsz (by linarith) (by linarith) hn
  nlinarith [sq_nonneg (n : ℝ)]

end GlobalTheory.CompanionTheory.RgCOBlock
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
section
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgKMaj

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_riesz (l : E →ₗ[ℂ] ℂ) : ∃ η : E, ∀ x, l x = ⟪η, x⟫_ℂ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  refine ⟨(InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap l), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem sum_sq_eq_of_basis {ι κ : Type*} [Fintype ι] [Fintype κ] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) :
    ∑ i, ‖l (b i)‖ ^ 2 = ∑ j, ‖l (c j)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, c.sum_sq_norm_inner_left]

theorem sq_le_of_basis {ι : Type*} [Fintype ι] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (x : E) :
    ‖l x‖ ^ 2 ≤ ‖x‖ ^ 2 * ∑ i, ‖l (b i)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, ← mul_pow, mul_comm ‖x‖]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm η x) 2

end Abstract

theorem sum_enorm_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∑ i, ‖z i‖ₑ ^ 2 = ENNReal.ofReal (∑ i, ‖z i‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem lintegral_enorm_sq_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (h : MemLp f 2 μ) : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have h1 := h.eLpNorm_lt_top
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h2
  rw [← h2]
  exact ENNReal.pow_lt_top h1

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_coef {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => ⟪ξ, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ) := by
  have h : Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) :=
    (hU.2.2 v).comp_continuous continuous_uMat (fun g => g.2)
  exact continuous_const.inner h

theorem sum_sq_translate {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : Formalism.MainNotions.S.IsKStableOn ε σ S)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ S) (ξ : H) (g k : Formalism.REAL.UJ ε)
    (hk : k ∈ Formalism.REAL.KG ε) :
    ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat (g * k)) (b i : H)⟫_ℂ‖ ^ 2 =
      ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ‖ ^ 2 := by
  have hkK : Formalism.MainNotions.S.umat k ∈ Formalism.REAL.Kset ε := hk
  let T : S →ₗᵢ[ℂ] S :=
    { toLinearMap := ((σ (Formalism.MainNotions.S.umat k) : H →ₗ[ℂ] H).comp S.subtype).codRestrict S
        (fun x => hst _ hkK _ x.2)
      norm_map' := fun x => hU.2.1 _ k.2 _ }
  let Te : S ≃ₗᵢ[ℂ] S := T.toLinearIsometryEquiv rfl
  let l : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [inner_smul_right] }
  have hmul : ∀ x : H, σ (Formalism.MainNotions.S.umat (g * k)) x = σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat k) x) := by
    intro x
    have : Formalism.MainNotions.S.umat (g * k) = Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat k := rfl
    rw [this, hU.1.2 _ g.2 _ k.2]
    rfl
  have h := sum_sq_eq_of_basis l (b.map Te) b
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [hmul, OrthonormalBasis.map_apply]
  rfl

theorem kMaj : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  intro n ε H _ _ _ σ D E hK hU hS u ξ
  obtain ⟨S, hfd, huS, hst⟩ := (hK.mem u).1 u.2
  haveI := hfd
  let b := stdOrthonormalBasis ℂ S
  let c : Formalism.REAL.UJ ε → Fin (Module.finrank ℂ S) → ℂ := fun g i => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ
  have hcm : ∀ i, Measurable fun g => ‖c g i‖ₑ ^ 2 := fun i =>
    (continuous_coef hU ξ (b i : H)).measurable.enorm.pow_const 2
  refine ⟨fun g => ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖c g i‖ₑ ^ 2, ?_, ?_, ?_, ?_⟩
  · exact (Finset.measurable_sum _ fun i _ => hcm i).const_mul _
  · intro g k hk
    simp only [sum_enorm_sq]
    congr 2
    exact sum_sq_translate hU hst b ξ g k hk
  · rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hcm i),
      lintegral_finset_sum _ fun i _ => hcm i]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
    exact lintegral_enorm_sq_lt_top (hS (b i : H) ξ)
  · intro g
    let l : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
        map_add' := fun x y => by simp [inner_add_right]
        map_smul' := fun c x => by simp [inner_smul_right] }
    have h := sq_le_of_basis l b ⟨(u : H), huS⟩
    show ‖l ⟨(u : H), huS⟩‖ₑ ^ 2 ≤ ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖l (b i)‖ₑ ^ 2
    rw [sum_enorm_sq, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h

end GlobalTheory.CompanionTheory.RgKMaj
end
end

