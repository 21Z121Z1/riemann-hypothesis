import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaCharEqSelfOfConjugateDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conjSrc_eq {E : Type} [Field E] [NumberField E] (τ : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc τ w = preplace τ w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : Af.IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

theorem UpperTheory.thetaChar_eq_self_of_conjugate_dual :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (κ : HChar E) (m : ℕ), 0 < m → κ.OrderDvd m → ∀ β : G E Ω →* (Qbar l)ˣ, Continuous β → IsLAdicOf art ι κ 0 β → ∀ c : G (maximalRealSubfield E) Ω, Af.IsConjEl c → (∀ s s' : G E Ω, s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ → β s' = (β s)⁻¹) → GlobalTheory.ThetaPull.thetaChar κ = κ := by
  intro E Ω _ _ _ _ _ _ l _ ι art ha κ m _ _ β _ hL c hc hβ
  have hLi := isLift_conj hc
  have hval : ∀ v, κ.UnrAt v → κ.UnrAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) →
      κ.val (conjSrc (IsCMField.complexConj E).toRingEquiv v) = (κ.val v)⁻¹ := by
    intro v hv hv'
    rw [conjSrc_eq] at hv' ⊢
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
    have e1 := hL.frob_unr ha (Or.inr rfl) hv hA hσ
    have e2 := hL.frob_unr ha (Or.inr rfl) hv' (isPlaceOver_preplace hLi hAA hA) (σ := conjGal hLi σ)
      (by rw [normV_preplace]; exact isFrob_conjGal hLi hAA hσ)
    rw [hβ σ (conjGal hLi σ) (AlgEquiv.ext fun _ => rfl), Units.val_inv_eq_inv_val, e1, inv_inj, ← map_inv₀] at e2
    exact Units.ext (by rw [Units.val_inv_eq_inv_val]; exact (ι.symm.injective e2).symm)
  have hu := GlobalTheory.GalChar.unr_ae κ
  have hu' := (Function.LeftInverse.injective (GlobalTheory.ThetaPull.conjSrc_conjSrc (E := E))).tendsto_cofinite.eventually hu
  have hS := Filter.eventually_cofinite.1 (hu.and hu')
  have h : (GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ ((GlobalTheory.ThetaPull.thetaChar κ).2.1.mul κ.2.1.inv) (fun k => ?_) hS.toFinset
      fun v hv => ?_
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, κ.2.2, (GlobalTheory.ThetaPull.thetaChar κ).2.2, inv_one, one_mul]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      obtain ⟨v, rfl⟩ : ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := ⟨_, GlobalTheory.ThetaPull.conjSrc_conjSrc v⟩
      rw [GlobalTheory.ThetaPull.conjSrc_conjSrc] at hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (((GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹).comp (localIdele E _)) fun y hy => ?_
      have hy' : IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom y) := ((conjLoc_spec _ v).2.2 y.val).trans hy
      have h1 : κ.1 (localIdele E _ y) = κ.val _ := κ.val_eq hv.1 y hy
      have h2 : κ.1 (localIdele E v _) = κ.val v := κ.val_eq hv.2 _ hy'
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ThetaPull.thetaChar_apply,
        GlobalTheory.ThetaPull.conjAd_localIdele, h1, h2, hval v hv.2 hv.1, mul_inv_cancel]
  exact Subtype.ext (mul_inv_eq_one.1 h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalFrobeniusCompatibility
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one

private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero h := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add, Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩

private theorem rec_tw_diag {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem totPar_spec {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end UpperTheory.V.Af.Gu

theorem UpperTheory.total_frobenius_compatibility :
    HypothesesH → FrobTot := by
  intro P F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  have hrec : IsRec h rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc
  have hx := (H A h rc hrec).1 hl
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hsp := totPar_spec hrec n c a d ρ S hS
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero h).lpTw s = WD.lpZero h
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.total_reciprocity :
    HypothesesH → RecTot := by
  intro H E Ω _ _ _ _ _ _ n c a d hn P w ρ σ _ hP hS τ e A h rc hrc
  have L := H.litN.loc
  have h1 := GlobalTheory.FormDict.RecTLaws.locProd_eq hrc hn σ τ e
  have h2 : ∀ i, rc (cls (ParLaws.toRep (σ i))) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cls (ParLaws.toRep (ρ i)))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i => by
    have hd : ∑ _ : Fin (d i), a i = d i * a i := by simp
    exact GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos (a i) (d i) _ hd (ρ i) (σ i)
      (hS i).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E (a i) (P i) w (ρ i) (hP i))
      (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd (ρ i) (σ i) (hS i).2.2)
  rw [rec_algNorm hrc]
  change _ = (rc (cls (ParLaws.toRep τ))).lpTw _
  rw [h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

