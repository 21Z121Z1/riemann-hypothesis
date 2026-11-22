import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0728
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramTame

set_option maxHeartbeats 800000 in
theorem unramOutside_of_corr_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  intro D N art hart r Mo hMo hMr c χ hc hcorr Q hQ htame hine
  intro x hx1 hx2 hx3 hxQ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hidem := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨M, hM, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 hidem c χ hc
  choose e he hinf he1 he0 using hidem
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E M hM
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  set f := idem Q + cA D (idem Q) with hf
  have hcf : cA D f = f := by rw [hf, map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]
  have hfe : ∀ P ∈ Q, idemAt P * f = idemAt P := by
    intro P hP
    have k1 : idemAt P * idem Q = idemAt P :=
      GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hP
    have k2 : idemAt P * cA D (idem Q) = 0 := by
      rw [idem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => hQ.mul_conj hP hj
    rw [hf, mul_add, k1, k2, add_zero]
  have hdelta : ∀ P e', GlobalTheory.IdemSupport.IsDelta Φ P e' → e P = e' := fun P e' h' =>
    GlobalTheory.IdemSupport.delta_unique hΦ ((GlobalTheory.IdemSupport.tie_iff hΦ (he P).1 (hinf P) P).1 (he P).2.2) h'
  have hcomp : ∀ P, (∃ a, e P = a ∧ a * f = a) → ι (finPart D (x : AE D)) P = 1 := by
    rintro P ⟨a, hea, haf⟩
    have k : e P * (x : AE D) = e P := by rw [hea, ← haf, mul_assoc, hxQ]
    have k' : ι (finPart D (e P * (x : AE D))) P = ι (finPart D (e P)) P := by rw [k]
    have e5 : ι (finPart D (e P * (x : AE D))) = ι (finPart D (e P)) * ι (finPart D (x : AE D)) := by
      rw [map_mul (finPart D) (e P) (x : AE D), map_mul ι]
    rw [e5] at k'
    change ι (finPart D (e P)) P * ι (finPart D (x : AE D)) P = ι (finPart D (e P)) P at k'
    rwa [he1 P, one_mul] at k'
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := bridge_star_holds D.R D.host
  have hconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v → v = GlobalTheory.IdemSupport.cP P' := by
    intro P' v h
    refine (GlobalTheory.IdemSupport.eq_of_le fun y hy => ?_).symm
    refine (h (GlobalTheory.IdemSupport.cO D y) y ?_).1 hy
    rw [GlobalTheory.IdemSupport.cO_coe, ← hstar, star_star]
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 := by
        change (ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) P = 1
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
        rfl
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.locK P (k P) = 1 := by
    show χ.loc P (Formalism.L2.Host.atFin P (k P)) = 1
    by_cases hPQ : P ∈ Q ∨ ∃ P' ∈ Q, Formalism.BasicNotions.IsConjPl D.host P' P
    · have h1P : ι (finPart D (x : AE D)) P = 1 := by
        refine hcomp P ?_
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact ⟨idemAt P, hdelta P _ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hPQ)), hfe P hPQ⟩
        · refine ⟨cA D (idemAt P'), ?_, ?_⟩
          · rw [hconj P' P hc']
            exact hdelta _ _ (GlobalTheory.IdemSupport.delta_conj hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hP')))
          · rw [← hcf, ← map_mul, hfe P' hP']
      have ht : χ.TameAt P := by
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact htame P hPQ P (Or.inl rfl)
        · exact htame P' hP' P (Or.inr hc')
      refine ht _ hun ?_
      rw [h1P] at b'
      have e4 : ((Formalism.L2.Host.atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          -(1 - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4, Valuation.map_neg]
      simpa using b'
    · push_neg at hPQ
      obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
      exact GlobalTheory.ToricDistribution.Corr.unr hart hcorr hB (hine P hPQ.1 hPQ.2 B hB) _ hun
  show ((χ.locK P (k P) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory.UnramTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LowCoefPos

theorem integral_lowCoefSq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i hP v hv hI
  have hθ : IsInfFam R.θ := hL.models.inf
  have : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1

  have hrep : ∀ ρ (x : (R.MW i (sg0 D A)).H ρ), Continuous fun h : GA D (Wc D i) =>
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h) x := by
    intro ρ x
    have hmem : ∀ h : GA D (Wc D i), (R.MW i (sg0 D A)).fr ρ * infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h * ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ UJset ((R.MW i (sg0 D A)).ε ρ) :=
      fun h => GlobalTheory.DualCoef.frame_mem (R.MW i (sg0 D A)) ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Wc D i) h ρ)
    exact (((R.MW i (sg0 D A)).ds ρ).2.2.1.2.2 x).comp_continuous
      ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (Wc D i).gram (hθ ρ))).matrix_mul
        continuous_const) hmem
  have hc : Continuous (lowCoefSq R i v) := by
    unfold lowCoefSq
    refine (continuous_finsetProd _ fun ρ _ => ?_).norm.pow 2
    exact continuous_const.inner (hrep ρ _)

  have h0 : ∀ h, 0 ≤ lowCoefSq R i v h := fun h => by unfold lowCoefSq; positivity

  have h1 : lowCoefSq R i v 1 = 1 := by
    unfold lowCoefSq
    have e : ∀ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) 1)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ = 1 := by
      intro ρ
      rw [GlobalTheory.PointAtPlaceHom.infMat_one, GlobalTheory.DualCoef.rep_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hv ρ]
      simp
    simp [e]

  set O : Set (GA D (Wc D i)) := GlobalTheory.AutMult.toFin (Wc D i) ⁻¹'
    {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} with hO
  have hOo : IsOpen O := (GlobalTheory.LevelOpen.isOpen_levG _ _ _).preimage (GlobalTheory.AutMult.continuous_toFin _)
  have hOs : O ⊆ realLev R i := by
    intro h hh
    exact ⟨_, (GlobalTheory.AutMult.toInf (Wc D i) h).2, _, hh, (GlobalTheory.AutMult.toInf_mul_toFin h).symm⟩
  have h1O : (1 : GA D (Wc D i)) ∈ O := by
    show ((GlobalTheory.AutMult.toFin (Wc D i) 1 : GfC (Wc D i)) : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)
    rw [map_one]
    exact (levW R i).one_mem
  set U : Set (GA D (Wc D i)) := {h | (1 : ℝ) / 2 < lowCoefSq R i v h} ∩ O with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const hc).inter hOo
  have h1U : (1 : GA D (Wc D i)) ∈ U := ⟨by rw [Set.mem_setOf_eq, h1]; norm_num, h1O⟩
  have hUs : U ⊆ Function.support (lowCoefSq R i v) ∩ realLev R i := by
    intro h hh
    refine ⟨?_, hOs hh.2⟩
    have := hh.1
    rw [Set.mem_setOf_eq] at this
    rw [Function.mem_support]
    linarith
  have hpos : 0 < R.νW i U := hUo.measure_pos _ ⟨1, h1U⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI]
  exact lt_of_lt_of_le hpos (measure_mono hUs)

end GlobalTheory.LowCoefPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseTransposeMemCuspFormRapidKernelSpanContraStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Global.IdeleGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseTranspose_mem_cuspFormRapidKernelSpan_contragredient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra := by
  first | exact @GlobalTheory.JSW.invT_mem_mspanR_contra | exact GlobalTheory.JSW.invT_mem_mspanR_contra | (intros; apply GlobalTheory.JSW.invT_mem_mspanR_contra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep.Generic

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem good_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (h : m + 1 < a) (hf : Good ψ (m + 1) f) :
    Good ψ m (colT ψ (m + 1) f) where
  cont := GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E a ψ hψ m f hf
  left := GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E a ψ hψ m f h hf
  law k hk y g := by
    rcases Nat.lt_or_ge (m + 1) k with h1 | h1
    · exact GlobalTheory.T.columnWhittakerTransform_keeps_later_law E a ψ m f hf k h1 y g
    · obtain rfl : k = m + 1 := by omega
      exact GlobalTheory.T.unipotentColumnWhittakerTransform_column_law E a ψ hψ m f hf y g
  van := GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero E a ψ hψ m f h hf

theorem hl_of_good {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) {k : ℕ} (hk : k ≤ m) (c : UnipotentBlockColumnIndex a k k → E) (g : GA E a) :
    f (ratGL E a (blkU c) * g) = f g := by
  refine hf.left _ (fun i j h => isMir_blkU c i j ?_) g
  omega

theorem colT_add (hψ : StdPsi ψ) {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ (m + 1) f) (hf' : Good ψ (m + 1) f') :
    colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := by
  funext g
  have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) _ _
    (per_coef hψ (eLast a (m + 1)) hf.cont (hl_of_good hf le_rfl) g)
    (per_coef hψ (eLast a (m + 1)) hf'.cont (hl_of_good hf' le_rfl) g)
  simp only [colT, coefF, mul_add]
  exact this

theorem colT_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) :
    colT ψ (m + 1) (fun g => c * f g) = fun g => c * colT ψ (m + 1) f g := by
  funext g
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  ring

theorem whit_good (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f →
    Good ψ 0 (whit ψ m f) ∧ (f ≠ 0 → whit ψ m f ≠ 0) := by
  induction m with
  | zero => exact fun _ f hf => ⟨hf, id⟩
  | succ m ih =>
    intro h f hf
    have h1 : m + 1 < a := by omega
    obtain ⟨h2, h3⟩ := ih (Or.inl (by omega)) (good_colT hψ h1 hf)
    exact ⟨h2, fun h0 => h3 (GlobalTheory.T.unipotentColumnWhittakerTransform_ne_zero E a ψ hψ m f h1 hf h0)⟩

theorem whit_add (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Good ψ m f → Good ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have h1 : m + 1 < a := by omega
    rw [whit_succ, whit_succ, whit_succ, colT_add hψ hf hf']
    exact ih (Or.inl (by omega)) (good_colT hψ h1 hf) (good_colT hψ h1 hf')

theorem whit_smul (m : ℕ) (c : ℂ) (f : GA E a → ℂ) : whit ψ m (fun g => c * f g) = fun g => c * whit ψ m f g := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [whit_succ, whit_succ, colT_smul, ih]

theorem whit_rt (m : ℕ) (f : GA E a → ℂ) (h g : GA E a) : whit ψ m (fun x => f (x * h)) g = whit ψ m f (g * h) := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    rw [whit_succ, whit_succ, ← ih]
    congr 1
    funext x
    simp only [colT, coefF, mul_assoc]

def locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) Circle where
  toFun y := ⟨ψ (sFin E (sLoc E w y)), by simpa [Submonoid.unitSphere] using hψ.norm _⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' x y := by
    apply Circle.ext
    change ψ (sFin E (sLoc E w (x + y))) = ψ (sFin E (sLoc E w x)) * ψ (sFin E (sLoc E w y))
    rw [map_add, map_add, AddChar.map_add_eq_mul]

theorem coe_locPsi (hψ : StdPsi ψ) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    (locPsi hψ w y : ℂ) = ψ (sFin E (sLoc E w y)) := rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem isGeneric_of_isLocComp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    GlobalTheory.LocGL.IsGeneric σ.ρ := by
  rintro E _ _ _ a P w σ ⟨f, hf0, hf⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end GlobalTheory.CuspRep.Generic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.PermPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]⟩

theorem permGL_conj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (g : Matrix (Fin n) (Fin n) k) (σ i) (σ j) := by
  have : ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      σ.toPEquiv.toMatrix * (g : Matrix (Fin n) (Fin n) k) * σ.symm.toPEquiv.toMatrix := rfl
  rw [this, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

theorem constEquiv_piTensor_detRep {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (L : ∀ _ : Fin n, GL (Fin 1) k)
    (t : ⨂[ℂ] _ : Fin n, ℂ) :
    PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ (piTensor (fun a => detRep (Fin 1) (χ a)) L t) =
      (∏ a, (χ a (GeneralLinearGroup.det (L a)) : ℂ)) * PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, piTensor_tprod, PiTensorProduct.constantBaseRingEquiv_tprod, detRep, ofChar_apply,
      detChar_apply, Finset.prod_mul_distrib, smul_eq_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

theorem isSubquotient_multiProd_prinSeries {n : ℕ} (e : (Σ _ : Fin n, Fin 1) ≃ Fin n)
    (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (multiProd e fun a => detRep (Fin 1) (χ a)) (prinSeries χ) := by
  let f : Fin n ≃ Fin n := (Equiv.sigmaUnique (Fin n) fun _ => Fin 1).symm.trans e
  let σ : Equiv.Perm (Fin n) := f.symm
  let P : GL (Fin n) k := permGL σ
  have hf : ∀ a (i : Fin 1), e ⟨a, i⟩ = f a := fun a i => by
    rw [Subsingleton.elim i 0]; rfl
  have hq : ∀ p : parab k (points (Fin n)), P * (p : GL (Fin n) k) * P⁻¹ ∈ parab k e := fun p => by
    refine mem_parab_iff.2 fun a b i j hab => ?_
    rw [hf, hf, permGL_conj_apply]
    simpa [σ] using mem_parab_iff.1 p.2 a b () () hab
  let κ := (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv
  let Ψ : IndSp e (piTensor fun a => detRep (Fin 1) (χ a)) →ₗ[ℂ]
      IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin n)).symm.toMonoidHom) :=
    { toFun := fun F => ⟨⟨fun g => κ (F.1.1 (P * g)), fun p g => by
          let q : parab k e := ⟨P * p * P⁻¹, hq p⟩
          have e1 : P * ((p : GL (Fin n) k) * g) = (q : GL (Fin n) k) * (P * g) := by
            simp only [q, mul_assoc, inv_mul_cancel_left]
          have hdet : ∀ a, GeneralLinearGroup.det (leviProj k e q a) =
              GeneralLinearGroup.det (leviProj k (points (Fin n)) p a) := fun a => by
            ext
            simp only [GeneralLinearGroup.val_det_apply, det_unique]
            rw [leviProj_apply, leviProj_apply, hf]
            show ((P * p * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (f a) (f a) = _
            rw [permGL_conj_apply]
            simp [σ]
          have hd : deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) =
              deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) := by
            rw [deltaHalf_apply, deltaHalf_apply]
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hdet, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
          beta_reduce
          rw [e1, parInd_law]
          generalize F.1.1 (P * g) = t
          show κ ((deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) : ℂ) •
              piTensor (fun a => detRep (Fin 1) (χ a)) (leviProj k e q) t) =
            (deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂ) •
              ofChar (torusChar χ) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) p)) (κ t)
          rw [map_smul, hd, ofChar_apply, torusChar_apply]
          congr 1
          refine (constEquiv_piTensor_detRep χ _ t).trans ?_
          rw [Units.coe_prod]
          congr 1
          exact Finset.prod_congr rfl fun a _ => by rw [hdet]; rfl⟩,
        MultiIrr.mem_smooth_of_eventually _ ((MultiIrr.eventually_of_smooth F).mono fun u hu x => by
          show κ (F.1.1 (P * (x * u))) = κ (F.1.1 (P * x))
          rw [← mul_assoc, hu])⟩
      map_add' := fun F G => Subtype.ext (Subtype.ext (funext fun x => map_add κ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => map_smul κ _ _)) }
  refine .of_injective ⟨Ψ, fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    fun F F' h => ?_
  · show κ (F.1.1 (P * x * g)) = κ (F.1.1 (P * (x * g)))
    rw [mul_assoc]
  · refine Subtype.ext (Subtype.ext (funext fun x => κ.injective ?_))
    have h1 : κ (F.1.1 (P * (P⁻¹ * x))) = κ (F'.1.1 (P * (P⁻¹ * x))) :=
      congrFun (congrArg (fun φ => φ.1.1) h) (P⁻¹ * x)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h1

end GlobalTheory.PermPrin

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenericsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locations_distinguished_by_generics : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  first | exact @GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | exact GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | (intros; apply GlobalTheory.CoefDuty.sameLoc_iff_heckeCong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxCompactUnitaryConjRelIndexEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxCompactUnitary_conj_relIndex_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  first | exact @GlobalTheory.UnimodMass.umax_relIndex_conj | exact GlobalTheory.UnimodMass.umax_relIndex_conj | (intros; apply GlobalTheory.UnimodMass.umax_relIndex_conj <;> assumption)
end

