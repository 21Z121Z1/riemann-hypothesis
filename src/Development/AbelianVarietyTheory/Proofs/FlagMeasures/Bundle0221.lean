import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem measurable_lmul_swap :
    Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  have hc : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    refine continuous_finsetSum _ fun l _ => ?_
    fun_prop
  exact hc.measurable

theorem quotientMeasure_hypotheses_closed_bessel_subgroup {S : Set (Mat k r)} {μG μS ν : Measure (Mt k r)}
    (hS : IsClosedSub k r S) (hG : IsHaarOn (GG k r) μG) (hμS : IsHaarOn S μS)
    (hU : IsUnimod S μS) (hq : IsQuotMeas μG μS ν) :
    PI.QuotientSetting (GG k r) S μG μS ν := by
  obtain ⟨hGm, hGu⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact ⟨hGm, hS.isMatGroup, hS.1, hG, hμS, (hGu μG hG).2, hU.1, hq⟩

theorem eq_map_prod_of_isQuotMeas {μG μS ν : Measure (Mt k r)} [SFinite ν] [SFinite μS]
    (hq : IsQuotMeas μG μS ν) :
    μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  ext A hA
  have hm := measurable_lmul_swap (k := k) (r := r)
  rw [Measure.map_apply hm hA, ← lintegral_indicator_one hA,
    hq _ (measurable_one.indicator hA), ← lintegral_indicator_one (hm hA),
    lintegral_prod _ ((measurable_one.indicator (hm hA)).aemeasurable)]
  rfl

theorem weil_integrable :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S →
      IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν →
      SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧
      μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧
      (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B),
        Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧
          ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧
      (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) →
        ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  intro k r S μG μS ν hS hG hμS hU hq
  have hset := quotientMeasure_hypotheses_closed_bessel_subgroup hS hG hμS hU hq
  have : SigmaFinite μS := hμS.1
  have : SigmaFinite μG := hG.1
  have hm := measurable_lmul_swap (k := k) (r := r)

  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG one_ne_zero
  set g : Mt k r → ENNReal := fun x => ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS with hg
  have hgm : Measurable g := by
    have : Measurable (fun p : Mt k r × Mt k r => (f0 (lmulM (Matrix.of p.2) p.1) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp hm
    exact this.lintegral_prod_right'
  have hgpos : ∀ x, 0 < g x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have hmx : Measurable (fun s : Mt k r => (f0 (lmulM (Matrix.of s) x) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp (hm.comp measurable_prodMk_left)
    change ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS = 0 at h0
    rw [lintegral_eq_zero_iff hmx] at h0
    have hall : ∀ᵐ s ∂μS, False := by
      filter_upwards [h0] with s hs
      simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at hs
      exact (hf0pos _).ne' hs
    exact hμS.2.1 (Measure.measure_univ_eq_zero.mp (by simpa using hall))
  have hgint : ∫⁻ x, g x ∂ν < ⊤ := by
    have := hq (fun x => (f0 x : ENNReal)) (measurable_coe_nnreal_ennreal.comp hf0m)
    have h2 : ∫⁻ x, g x ∂ν = ∫⁻ x, (f0 x : ENNReal) ∂μG := by rw [this]; rfl
    rw [h2]
    exact hf0int.trans ENNReal.one_lt_top

  have hsig : SigmaFinite ν := by
    refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ENNReal) + 1)⁻¹ ≤ g x})
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      have hne : ((n : ENNReal) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
      have hnt : ((n : ENNReal) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp)
      calc ν {x | ((n : ENNReal) + 1)⁻¹ ≤ g x} ≤ (∫⁻ x, g x ∂ν) / ((n : ENNReal) + 1)⁻¹ :=
            meas_ge_le_lintegral_div hgm.aemeasurable hne hnt
        _ < ⊤ := ENNReal.div_lt_top hgint.ne hne
    · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
      intro x
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hgpos x).ne'
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      show ((n : ENNReal) + 1)⁻¹ ≤ g x
      refine le_trans ?_ hn.le
      exact ENNReal.inv_le_inv.mpr le_self_add
  have hmap := eq_map_prod_of_isQuotMeas (μG := μG) (μS := μS) (ν := ν) hq
  refine ⟨hsig, ?_, hmap, ?_, ?_⟩
  · have hae := GlobalTheory.QuotRightInv.ae_mem_of_quot hset
    rw [ae_iff] at hae
    simpa using hae
  · intro B _ _ _ f hf
    rw [hmap] at hf
    have hf' : Integrable (fun p : Mt k r × Mt k r => f (lmulM (Matrix.of p.2) p.1)) (ν.prod μS) :=
      (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hf
    refine ⟨hf'.integral_prod_left, ?_⟩
    rw [hmap, integral_map hm.aemeasurable hf.aestronglyMeasurable, integral_prod _ hf']
  · intro F hF hFS y hy
    exact GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset F hF (fun s hs x _ => hFS s hs x) y hy

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlag
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmFlagSub

open IsDedekindDomain Formalism.HermitianLatticesTheory

section Loc

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [hp : p.IsPrime]

theorem mem_localization_iff (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem le_localized_self (L : Submodule R W) : L ≤ localization₂ p L := fun x hx =>
  (mem_localization_iff p L x).2 ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem localization_le_of_le_localization₂ {L N : Submodule R W} (h : L ≤ localization₂ p N) : localization₂ p L ≤ localization₂ p N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff p N _).1 (h hsx)
  refine (mem_localization_iff p N x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases hp.mem_or_mem hm with h1 | h1
  · exact ht h1
  · exact hs h1

end Loc

theorem mem_of_forall_locP {E W : Type} [Field E] [NumberField E] [AddCommGroup W]
    [Module (𝓞 E) W] (N : Submodule (𝓞 E) W) (x : W)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; localization₂ P.asIdeal N)) : x ∈ N := by
  by_contra hx
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : 𝓞 E) ∈ I := by rw [hI]; trivial
    apply hx
    simpa [I] using this
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact hs (hIM (by simpa [I] using hsx))

theorem xLam_le_smul_sup_xLam :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
      (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'),
      IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' →
        XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  intro E _ _ _ S r T T' Λ g F F' hF hF' hA x hx
  obtain ⟨ξ, hξ0, hξ1, hξ⟩ := hA
  set N : Submodule (𝓞 E) S.V := Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' with hN
  apply mem_of_forall_locP
  intro P
  haveI := P.isPrime
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  swap
  · refine (mem_localization_iff _ _ _).2 ⟨g, hg, Submodule.mem_sup_left ?_⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hx.1
  obtain ⟨c, -, hc1, hc⟩ := hF.1 P
  obtain ⟨c', -, hc1', hc'⟩ := hF'.1 P
  simp only [hc1 hg, one_smul] at hc
  simp only [hc1' hg, one_smul] at hc'
  have he' : ∀ b, F'.fl.e b ∈ localization₂ P.asIdeal N := by
    intro b
    have h1 : F'.fl.e b ∈ localization₂ P.asIdeal (XLam Λ F') := by
      rw [hc']
      exact le_localized_self _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact localization_le_of_le_localization₂ _ (le_sup_right.trans (le_localized_self _ _)) h1
  have hf : ∀ n : ℕ, ∀ b : Fin r, b.1 = n → F.fl.e b ∈ localization₂ P.asIdeal N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb
      have h1 : frame F' b.castSucc - frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N :=
        localization_le_of_le_localization₂ _ (le_sup_left.trans (le_localized_self _ _)) (hξ b.castSucc P hg)
      have h2 : frame F' b.castSucc = F'.fl.e b := by simp [frame, FlagG.fvec]
      have h3 : frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N := by
        have := Submodule.sub_mem _ (he' b) h1
        rw [h2] at this
        simpa using this
      have h4 : frameAct (frame F) ξ b.castSucc =
          F.fl.e b + ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a := by
        unfold frameAct
        rw [Fin.sum_univ_castSucc, hξ0 (Fin.last r) b.castSucc (Fin.castSucc_lt_last b),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hξ1]
        simp only [frame, FlagG.fvec, Fin.snoc_castSucc, RingOfIntegers.coe_eq_algebraMap, map_zero,
          map_one, zero_smul, add_zero, one_smul, algebraMap_smul]
      have h5 : ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a ∈
          localization₂ P.asIdeal N := by
        refine Submodule.sum_mem _ fun a ha => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
        · exact Submodule.smul_mem _ _ (ih a.1 (hb ▸ hab) a rfl)
        · rw [hξ0 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab), zero_smul]
          exact Submodule.zero_mem _
      rw [h4] at h3
      simpa using Submodule.sub_mem _ h3 h5
  have hx' : x ∈ localization₂ P.asIdeal (XLam Λ F) := le_localized_self _ _ hx
  rw [hc] at hx'
  refine localization_le_of_le_localization₂ _ ?_ hx'
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hf _ a rfl

end GlobalTheory.AdmFlagSub

end
end

