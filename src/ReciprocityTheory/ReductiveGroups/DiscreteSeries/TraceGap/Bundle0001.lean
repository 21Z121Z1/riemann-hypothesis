import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0008

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FockWeightWedgeLowerModes
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem gb_rhoN_eq (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c = ε a) : rhoN ε a = rhoN ε b := by
  have h := lfD_cnt (fun c => ε c ≠ ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c ≠ ε a).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc'.2.2 (hc c hc'.1 hc'.2.1)
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

theorem gb_rhoC_ge (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h := lfD_cnt (fun c => ε c = ε a) hab
  have h1 : (univ.filter fun c => c = a ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = b ∧ ε c = ε a).card = 1 := by
    rw [lfD_single]; simp [he]
  simp only [rhoC, ← he]
  rw [h1, h2] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  have : (0 : ℝ) ≤ ((univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card : ℝ) := Nat.cast_nonneg _
  linarith

theorem gb_phSum_le (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : phSum Ph a ≤ oppCount ε a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.2 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.1 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_fst_le ε Ph hnc a
  linarith

theorem gb_phSum_ge (ε : Fin n → Bool) {Ph : Finset (Fin n × Fin n)} (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2)
    (a : Fin n) : -(oppCount ε a : ℝ) ≤ phSum Ph a := by
  unfold phSum; rw [sum_root_apply]
  have h0 : (0:ℝ) ≤ ((Ph.filter fun y => y.1 = a).card : ℝ) := Nat.cast_nonneg _
  have h3 : ((Ph.filter fun y => y.2 = a).card : ℝ) ≤ oppCount ε a := by exact_mod_cast card_snd_le ε Ph hnc a
  linarith

theorem dirac_block {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph) {W : Submodule ℂ M}
    (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W) : BlockAnti ε (lam - phSum Ph) := by
  classical
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  intro a b hab he
  simp only [Pi.sub_apply]
  by_cases hc : ∃ c, a < c ∧ c < b ∧ ε c ≠ ε a
  · obtain ⟨c, hac, hcb, hce⟩ := hc
    have g1 := hh a c (Ne.symm hce)
    have g2 := hh c b (by rw [← he]; exact hce)
    rw [abs_of_pos (sub_pos.mpr (hmono hac))] at g1
    rw [abs_of_pos (sub_pos.mpr (hmono hcb))] at g2
    have pa := gb_phSum_le ε hnc a
    have pb := gb_phSum_ge ε hnc b
    have ob : oppCount ε b = oppCount ε a := by unfold oppCount; rw [he]
    rw [ob] at pb
    have oc : 2 ≤ oppCount ε c := by
      unfold oppCount
      have hsub : ({a, b} : Finset (Fin n)) ⊆ univ.filter fun x => ε x ≠ ε c := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        simp only [mem_filter, mem_univ, true_and]
        rcases hx with rfl | rfl
        · exact Ne.symm hce
        · rw [← he]; exact Ne.symm hce
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hab.ne] at this
    have hsum := oppCount_add ε (Ne.symm hce)
    have oc' : (2:ℝ) ≤ oppCount ε c := by exact_mod_cast oc
    linarith
  · push Not at hc
    obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW' a b hab he
    have hC := gb_rhoC_ge ε hab he
    have hR := gb_rhoN_eq ε hab he hc
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
    have : (0:ℝ) ≤ N := Nat.cast_nonneg _
    linarith

theorem dirac_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {Ph : Finset (Fin n × Fin n)} (hPh : IsPosNC ε Ph)
    (hne : Ph.Nonempty) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - phSum Ph) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hb := dirac_block hg hE hPh hW
  obtain ⟨hmono, h, hh, hn⟩ := hg
  have hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2 := fun x hx => (hPh x hx).2
  have hW' : IsKIrrHW ε E (lowK ε (lam - phSum Ph)) W := by
    have : lowK ε (lam - phSum Ph) = lowK ε lam - phSum Ph := by unfold lowK; abel
    rw [this]; exact hW
  obtain ⟨z, hzW, -, hz0, hzK⟩ := exists_nonzero_physical_highestWeight_vector_tensFock ε hE hb hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - phSum Ph - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - phSum Ph - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam =
      nsq (lam - phSum Ph) - nsq lam := by
    rw [sub_add_cancel]
    unfold casVal
    ring
  obtain ⟨x0, hx0⟩ := hne
  have hx0' := (hPh x0 hx0).1
  have hn2 : (2 : ℝ) ≤ n := by
    have := x0.2.2
    have := Fin.lt_def.mp hx0'
    exact_mod_cast (show 2 ≤ n by omega)
  have hpos : ∀ x ∈ Ph, h ≤ lam x.1 - lam x.2 := by
    intro x hx
    have := hh x.1 x.2 (hnc x hx)
    rwa [abs_of_pos (sub_pos.mpr (hmono (hPh x hx).1))] at this
  have hker := kernel_lemma ε lam (h := h) (by linarith) Ph hnc hpos
  have hcard : (1 : ℝ) ≤ Ph.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x0, hx0⟩
  have hneg : nsq (lam - phSum Ph) - nsq lam < 0 := by
    have h2n : 0 < 2 * h - n := by linarith
    have : 0 < (2 * h - n) * Ph.card := by positivity
    unfold phSum
    linarith
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((nsq (lam - phSum Ph) - nsq lam : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  nlinarith

theorem no_irreducible_at_noncompact_root_shift {ε : Fin n → Bool} {lam : Fin n → ℝ} (hg : Gap3 ε lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  have hP : phSum {(a, b)} = root a b := by simp [phSum]
  refine dirac_sharp hg hE hU (Ph := {(a, b)}) ?_ (singleton_nonempty _) (by rw [hP]; exact hW) hc
  intro x hx
  rw [mem_singleton] at hx
  subst hx
  exact ⟨hab, hε⟩

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GsBasisPhys
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def sModes (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  univ.filter fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1

def sDeg (ε : Fin n → Bool) : ℕ := (sModes ε).card

def sIdx (ε : Fin n → Bool) : Finset (Fin (n * n)) := (sModes ε).map finProdFinEquiv.toEmbedding

theorem gs_perm_prod {l1 l2 : List (Fin n × Fin n)} (h : l1.Perm l2) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ (l1.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
      σ • (l2.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨σ, hσ, e⟩ := ih
    exact ⟨σ, hσ, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_mul, neg_one_smul]
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, h1, e1⟩ := ih1
    obtain ⟨σ2, h2, e2⟩ := ih2
    refine ⟨σ1 * σ2, ?_, by rw [e1, e2, smul_smul]⟩
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num

theorem sIdx_eq (ε : Fin n → Bool) : sIdx ε = (lowerWedgeAlt ε).1 := by
  ext m
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  rw [mem_lowerWedge_iff]
  simp [sIdx, sModes]

theorem gs_basis_phys {ε : Fin n → Bool} {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    fockBasis n S ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  exact lf_cm_basis_of_not_mem (x := (i, a)) fun h => hia ((lf_mem_phys ε i a).1 (hS h))

theorem gs_basis_deg (S : Finset (Fin (n * n))) : fockBasis n S ∈ ⋀[ℂ]^S.card (Fin n × Fin n → ℂ) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  rw [hb]
  exact ExteriorAlgebra.ιMulti_range ℂ S.card ⟨_, rfl⟩

theorem sVec_eq_basis (ε : Fin n → Bool) : ∃ c : ℂ, c ≠ 0 ∧ sVec ε = c • fockBasis n (sIdx ε) := by
  have hp : (sModes ε).toList.Perm
      (List.ofFn fun i => finProdFinEquiv.symm ((sIdx ε).orderEmbOfFin rfl i)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _)
    · rw [List.nodup_ofFn]
      intro i j h
      exact ((sIdx ε).orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h)
    · ext y
      rw [List.mem_toFinset, List.mem_toFinset, Finset.mem_toList, List.mem_ofFn]
      constructor
      · intro hy
        have hm : finProdFinEquiv y ∈ sIdx ε := Finset.mem_map_of_mem _ hy
        have hr : finProdFinEquiv y ∈ Set.range ((sIdx ε).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hm
        obtain ⟨i, hi⟩ := hr
        exact ⟨i, by rw [hi]; simp⟩
      · rintro ⟨i, rfl⟩
        have hm := (sIdx ε).orderEmbOfFin_mem rfl i
        obtain ⟨a, ha, hae⟩ := Finset.mem_map.1 hm
        rw [← hae]
        simpa using ha
  obtain ⟨σ, hσ, e⟩ := gs_perm_prod hp
  refine ⟨σ, by rcases hσ with rfl | rfl <;> norm_num, ?_⟩
  rw [lfa_basis_list]
  exact e

theorem tr_sVec_props (ε : Fin n → Bool) :
    sVec ε ∈ physFock ε ∧ sVec ε ≠ 0 ∧
      (∀ a, sgE ε cpFock cmFock a a (sVec ε) = (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • sVec ε) ∧
      ∀ a b, b < a → ε a = ε b → sgE ε cpFock cmFock a b (sVec ε) = 0 := by
  obtain ⟨c, hc, e⟩ := sVec_eq_basis ε
  rw [e, sIdx_eq]
  refine ⟨Submodule.smul_mem _ _ (gs_basis_phys (lowerWedgeAlt ε).2),
    smul_ne_zero hc ((fockBasis n).ne_zero _), fun a => ?_, fun a b hba he => ?_⟩
  · rw [map_smul, lowerWedge_weight, smul_comm]
  · rw [map_smul, lowerWedge_killed_by_lowering ε hba he, smul_zero]

theorem sVec_deg (ε : Fin n → Bool) : sVec ε ∈ ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ) := by
  obtain ⟨c, -, e⟩ := sVec_eq_basis ε
  rw [e]
  have h := gs_basis_deg (sIdx ε)
  rw [sIdx, Finset.card_map] at h
  exact Submodule.smul_mem _ _ h

theorem sDeg_eq_sum (ε : Fin n → Bool) :
    (sDeg ε : ℝ) = ∑ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a := by
  have h1 : ∀ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a =
      ((univ.filter fun b => ε b = false ∧ b < a).card : ℝ) := by
    intro a ha
    rw [lf_rhoHol_sub_rhoN, if_pos (by simpa [plusIdx] using ha)]
  rw [Finset.sum_congr rfl h1]
  unfold sDeg sModes
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, plusIdx,
    Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ε i = true <;> simp [hi]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

