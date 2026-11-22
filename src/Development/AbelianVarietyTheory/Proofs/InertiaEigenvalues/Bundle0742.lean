import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpreadRestrict

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem surj_conj {B : Type} [CommGroup B] (χ : G D.host.E N.Om →* B) (hA : AntiHom X.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring N.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs' : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, X.cc (X.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, X.cc.symm x = X.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap X.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap X.cc.symm.toRingHom).comap X.cc.symm.toRingHom = A := by
    ext y
    show X.cc.symm (X.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem sign_eq_one (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {S : Finset (Pl D.host.E)} {M : ℕ}
    {P v : Pl D.host.E} (hP : P ∈ S) (hv : v ∈ S) (hc : IsConjPl D.host P v) (hPa : P ∈ admissibleConjugatePairPlaces X i S M) :
    (((Y.delU_conj i S M P hP v hv hc).choose : ℤ) : ZMod (X.l i ^ M)) = 1 := by
  classical
  have hs := (Y.delU_conj i S M P hP v hv hc).choose_spec
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := conj_mem_admissibleConjugatePairPlaces hPa hc
  obtain ⟨-, P', -, -, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPa
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm.2 P (by simp)
  have hDel : GlobalTheory.GalChar.IsDel D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    have hsP : ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
      obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
      exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact surj_conj χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host X.cc (X.l i) ⟨χ, hDel⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
  obtain ⟨σ, -, hσ⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd 1)
  have e := hs σ
  rw [delU_on hY σ ⟨v, hv⟩ hva, delU_on hY σ ⟨P, hP⟩ hPa] at e
  simp only at e
  rw [GlobalTheory.GalChar.pair_eq hc, hσ, toAdd_ofAdd, mul_one] at e
  exact e.symm

theorem spread_conj (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {M : ℕ} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    {S : Finset (Pl D.host.E)} (hS : admissibleConjugatePairPlaces X i S M = S) (x : ↥(half ch (admissibleConjugatePairPlaces X i S M)) → ZMod (X.l i ^ M))
    {v P : Pl D.host.E} (hvS : v ∈ S) (hvc : v ∉ ch) (hvP : IsConjPl D.host v P)
    (hPh : P ∈ half ch (admissibleConjugatePairPlaces X i S M)) :
    spread Y i S M ch x ⟨v, hvS⟩ = x ⟨P, hPh⟩ := by
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := by rw [hS]; exact hvS
  have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
  have hPv := GlobalTheory.GalChar.isConjPl_symm hvP
  have hPaa : P ∈ admissibleConjugatePairPlaces X i (admissibleConjugatePairPlaces X i S M) M := by
    simp only [hS]
    rw [← hS]
    exact (mem_half.1 hPh).1
  rw [spread_apply, Finset.sum_eq_single ⟨P, hPh⟩, weight, if_neg hne, dif_pos ⟨hva, hPv⟩, sign_eq_one hY _ _ hPv hPaa,
    one_mul]
  · intro P' _ h'
    rw [weight, if_neg fun e : v = P'.1 => hvc (e ▸ (mem_half.1 P'.2).2), dif_neg fun h => h' (Subtype.ext
      (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hvP)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_restrict : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  intro D N X Y hY i M ch hch Q Q' hQQ hQ hQ' hsub c v hv
  by_cases hc : v ∈ ch
  · have h1 : v ∈ half ch (admissibleConjugatePairPlaces X i Q M) := mem_half.2 ⟨by rw [hQ]; exact hQQ hv, hc⟩
    have h2 : v ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨by rw [hQ']; exact hv, hc⟩
    rw [spread_of_mem Y i Q M hch c ⟨v, hQQ hv⟩ h1, spread_of_mem Y i Q' M hch _ ⟨v, hv⟩ h2]
  · have hva : v ∈ admissibleConjugatePairPlaces X i Q' M := by rw [hQ']; exact hv
    obtain ⟨-, P, -, hvP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hva
    have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
    have hPc : P ∈ ch := by
      by_contra h
      exact hc ((hch.pair _ _ hvP hne).2 h)
    have hPa' : P ∈ admissibleConjugatePairPlaces X i Q' M := conj_mem_admissibleConjugatePairPlaces hva hvP
    have hPh' : P ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨hPa', hPc⟩
    rw [spread_conj hY hch hQ c (hQQ hv) hc hvP (hsub P hPh'), spread_conj hY hch hQ' _ hv hc hvP hPh']

end GlobalTheory.SpreadRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuedMapEqOfContinuousCompletionIsoExtending
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompletionIsom

open WithZero in

theorem valuation_eq_of_lt_one_iff {K : Type} [Field K] (v v' : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ y, v y < 1 ↔ v' y < 1) (π : K) (hπ : v π = exp (-1)) (y₀ : K) (hy₀ : v' y₀ = exp (-1)) :
    ∀ y, v' y = v y := by
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hy0 : y₀ ≠ 0 := by rintro rfl; rw [map_zero] at hy₀; exact exp_ne_zero hy₀.symm
  have hexp : ∀ (w : Valuation K (WithZero (Multiplicative ℤ))) (x : K), x ≠ 0 → ∃ a : ℤ, w x = exp a :=
    fun w x hx => ⟨_, (exp_log ((Valuation.ne_zero_iff w).2 hx)).symm⟩
  have hker : ∀ z, v z = 1 → v' z = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact zero_ne_one hz
    obtain ⟨a, ha⟩ := hexp v' z hz0
    rcases lt_trichotomy a 0 with h1 | h1 | h1
    · have := (h z).2 (by rw [ha, ← exp_zero, exp_lt_exp]; exact h1)
      rw [hz] at this; exact absurd this (lt_irrefl _)
    · rw [ha, h1, exp_zero]
    · have := (h z⁻¹).2 (by rw [map_inv₀, ha, ← exp_neg, ← exp_zero, exp_lt_exp]; omega)
      rw [map_inv₀, hz, inv_one] at this; exact absurd this (lt_irrefl _)
  obtain ⟨e, he⟩ := hexp v' π hπ0
  obtain ⟨b, hb⟩ := hexp v y₀ hy0
  have he1 : e < 0 := by
    have := (h π).1 (by rw [hπ, ← exp_zero, exp_lt_exp]; omega)
    rwa [he, ← exp_zero, exp_lt_exp] at this
  have hb1 : b < 0 := by
    have := (h y₀).2 (by rw [hy₀, ← exp_zero, exp_lt_exp]; omega)
    rwa [hb, ← exp_zero, exp_lt_exp] at this
  have he2 : -1 ≤ e := by
    by_contra hc
    have := (h (π * y₀⁻¹)).2 (by
      rw [map_mul, map_inv₀, he, hy₀, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp]; omega)
    rw [map_mul, map_inv₀, hπ, hb, ← exp_neg, ← exp_add, ← exp_zero, exp_lt_exp] at this
    omega
  have hπ' : v' π = exp (-1) := by rw [he]; congr 1; omega
  intro y
  by_cases hy : y = 0
  · rw [hy, map_zero, map_zero]
  obtain ⟨a, ha⟩ := hexp v y hy
  have hz := hker (y * π ^ a) (by
    rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, ← exp_zero]; congr 1; simp)
  rw [map_mul, map_zpow₀, hπ', ← exp_zsmul] at hz
  rw [ha, eq_inv_of_mul_eq_one_left hz, ← exp_neg]
  congr 1; simp

theorem valued_v_map : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    ∀ y : w.adicCompletion E, Valued.v (i y) = Valued.v y := by
  intro E E' _ _ _ _ _ w w' i hi _ y
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have hi' : Continuous i.symm := i.toEquiv.continuous_symm_iff.2 ho
  obtain ⟨π, hπ⟩ := w.valuedAdicCompletion_surjective E (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := w'.valuedAdicCompletion_surjective E' (WithZero.exp (-1))
  refine valuation_eq_of_lt_one_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
    ((Valued.v : Valuation (w'.adicCompletion E') (WithZero (Multiplicative ℤ))).comap i.toRingHom)
    (fun x => ⟨fun hx => GlobalTheory.ConjParahoric.val_lt_one_map i.toRingHom hi hx, fun hx => ?_⟩) π hπ (i.symm ϖ) ?_ y
  · have := GlobalTheory.ConjParahoric.val_lt_one_map i.symm.toRingHom hi' hx
    simpa using this
  · simpa using hϖ

end GlobalTheory.CompletionIsom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, GlobalTheory.T.wach_lattice_expansion_at_low_level_points D HW F Cm, GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm,
    GlobalTheory.T.wachModule_saturated_exactness_crystalline D HW F Cm, GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F, GlobalTheory.T.p8_of_cmpOf D HW F Cm, GlobalTheory.T.wachModule_descent_to_tame_subextension D HW F,
    GlobalTheory.T.wachModule_uniqueness_characterisation D HW F, GlobalTheory.T.gammaSemisimpleQuotientD_statement D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F, GlobalTheory.T.defect_torsion_second_cohomology_kernel D HW F Cm,
    GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, GlobalTheory.T.local_comparison_of_cmpOf D HW F Cm⟩

end GlobalTheory.NL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.WeightParamTie

open Formalism.L2

theorem paramV_half (R : Ranks) (h : HCParam R) (j : Fin R.m) :
    NG.paramV R h j (1 / 2) = (param h j).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
  simp only [NG.paramV, param, run, Multiset.map_add, Multiset.map_map]
  congr 1
  · congr 1
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
    · refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]; push_cast; ring
  · refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]; push_cast; ring

theorem infOf_neg_rev (n : ℕ) (lam : Fin n → ℤ) :
    NG.infOf (fun k => -lam (Fin.rev k)) = (NG.infOf lam).map Neg.neg := by
  have hu : (Finset.univ : Finset (Fin n)).val = Finset.univ.val.map Fin.rev := by
    conv_lhs => rw [← Finset.univ_map_equiv_to_embedding Fin.revPerm]
    rfl
  unfold NG.infOf
  conv_lhs => rw [hu]
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  have hk : (k : ℕ) + 1 ≤ n := k.2
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem weightParam_of_levelTied : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E),
    Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) →
    (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ),
      (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  intro D M tup hL hEta hLoc i ρ
  set a := GlobalTheory.WtDual.dualWt (M.loc i).wt with ha
  have hd : (M.loc i).wt.IsDual a := GlobalTheory.WtDual.isDual_dualWt _
  obtain ⟨⟨lam, hlam, -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)
  obtain ⟨⟨lam', hlam', -⟩, -⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (ComplexEmbedding.conjugate (embT D ρ))
  have huniq := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ a (embT D ρ)).1
  have hsw := GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg _ _ a (embT D ρ) lam' hlam'
  have heq : lam = fun k => -lam' (Fin.rev k) := huniq.unique hlam hsw
  have hlam'eq : lam' = fun k => -lam (Fin.rev k) := by
    funext k; rw [heq]; simp [Fin.rev_rev]
  have key : ∀ (k : ℕ) (hk : k = D.nd.j i) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m),
      (M (D.nd.mu i) k h1 h2).wt = (M.loc i).wt := by
    intro k hk h1 h2; subst hk; rfl
  have hj : (liftIdx D i).1 + 1 = D.nd.j i := by
    have := D.nd.j_range i
    simp only [liftIdx]
    omega
  have hwt := hL.wt (D.nd.mu i) (liftIdx D i) ρ (1 / 2) a lam (hEta ρ)
    (by rw [key _ hj]; exact hd) hlam
  have hinf : D.naut.infWt i (embT D ρ) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) := by
    rw [hLoc i a _ lam hd hlam, hwt, paramV_half]
    rfl
  have e0 : embOver D ρ false = embT D ρ := rfl
  have e1 : embOver D ρ true = ComplexEmbedding.conjugate (embT D ρ) := by
    ext x
    rw [GlobalTheory.JumpDictionaryFoundation.embOver_true_apply, ComplexEmbedding.conjugate_coe_eq]
    rfl
  refine ⟨by rw [e0, hinf], ?_⟩
  rw [e1, hLoc i a _ lam' hd hlam', hlam'eq, infOf_neg_rev, ← hLoc i a _ lam hd hlam, hinf, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

end GlobalTheory.WeightParamTie
end
end

