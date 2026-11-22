import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0387
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0382
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGood
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RoadU.holdsS_all_crys : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  intro hIn hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨Pc, hPc⟩ := hQL E Q.K Q.two a ha π hQ3
  have hres := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π Pc hPc r hr
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E Q.K l a ha π χ Pc hPc hsc
  have hin : InScope .good l Pc χ' := ⟨hχ'.1, hχ'.2.1, hQ4 Pc hPc⟩
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk Pc).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a Pc w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys Pc ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' :=
    hgood Q.K Ω l ι a ha Pc χ' hin _ hres w' (hQ2 w' hund) B hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CsdScopeOfLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.CsdLift

theorem evenReal (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (h : Even (Module.finrank ℚ (maximalRealSubfield E))) :
    Even (Module.finrank ℚ (maximalRealSubfield M)) := by
  have hE : Module.finrank ℚ E = Module.finrank ℚ (maximalRealSubfield E) * 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
  have hM : Module.finrank ℚ M = Module.finrank ℚ (maximalRealSubfield M) * 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield M) M, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield M) M]
  have hEM : Module.finrank ℚ M = Module.finrank ℚ E * Module.finrank E M :=
    (Module.finrank_mul_finrank ℚ E M).symm
  obtain ⟨k, hk⟩ := h
  refine ⟨k * Module.finrank E M, ?_⟩
  have : Module.finrank ℚ (maximalRealSubfield M) * 2 = (k * Module.finrank E M) * 2 + (k * Module.finrank E M) * 2 := by
    rw [← hM, hEM, hE, hk]; ring
  omega

theorem unramUp (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M))
    (h : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) (w.under (𝓞 E)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield M)) w.asIdeal := by
  set v := w.under (𝓞 E) with hvdef
  have hv : v.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) = ⊥ := by
    haveI := v.isMaximal
    haveI : (v.asIdeal.under (𝓞 (maximalRealSubfield E))).IsMaximal := Ideal.IsMaximal.under _ _
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal
        (E ≃ₐ[maximalRealSubfield E] E),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E)
        (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  apply GlobalTheory.isUnramifiedAt_of_inertia_eq_bot (maximalRealSubfield M) M w.asIdeal w.ne_bot
  have hcard : Nat.card (M ≃ₐ[maximalRealSubfield M] M) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  haveI : Fact (Nat.card (M ≃ₐ[maximalRealSubfield M] M)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (w.asIdeal.inertia (M ≃ₐ[maximalRealSubfield M] M)) with h1 | h1
  · exact h1
  exfalso
  have hc : IsCMField.complexConj M ∈ w.asIdeal.inertia (M ≃ₐ[maximalRealSubfield M] M) := h1 ▸ Subgroup.mem_top _
  have hcE : IsCMField.complexConj E ∈ v.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) := by
    intro y
    have := hc (algebraMap (𝓞 E) (𝓞 M) y)
    show _ ∈ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))
    rw [Ideal.mem_comap]
    have e : algebraMap (𝓞 E) (𝓞 M) (IsCMField.complexConj E • y - y) =
        IsCMField.complexConj M • algebraMap (𝓞 E) (𝓞 M) y - algebraMap (𝓞 E) (𝓞 M) y := by
      rw [map_sub]
      congr 1
      apply RingOfIntegers.ext
      first
        | exact (GlobalTheory.LiftPolar.conj_algebraMap (y : E)).symm
        | simpa using (GlobalTheory.LiftPolar.conj_algebraMap (y : E)).symm
    rw [e]
    exact this
  rw [hv, Subgroup.mem_bot] at hcE
  exact IsCMField.complexConj_ne_one E hcE

theorem val_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).val w = 1 := by
  rfl

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem compNorm_quadChar_pow (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    compNorm E (quadChar E ^ a) = 1 := by
  rw [map_pow, compNorm_quadChar, one_pow]

theorem main : JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (π' : CuspSub M a), IsLift π π' → InScope .csd l π (quadChar E ^ a) → InScope .csd l π' (quadChar M ^ a) := by
  intro hJ hG E M _ _ _ _ _ _ _ l a ha π π' hL hS
  have hF := GlobalTheory.automorphicFormsFiniteGL
  obtain ⟨⟨χ', hreg', -⟩, -⟩ := GlobalTheory.LiftPolar.main hF hJ hG E M l a ha π _ π' hL ⟨hS.1, hS.2.1, trivial⟩
  obtain ⟨-, hpol, ⟨hx, heven, hns⟩, -⟩ := hS
  refine ⟨hreg', ⟨fun v => by rw [locInf_pow, quadChar_locInf], ?_⟩, ⟨?_, ?_, ?_⟩, rfl⟩
  · rw [compNorm_quadChar_pow]
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha π' 1 ?_
    have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π _ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [(GlobalTheory.LiftPolar.tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hs, B, hB⟩
    rw [compNorm_quadChar_pow] at hs
    have e1 := GlobalTheory.LiftPolar.cPl_under (E := E) w
    have e2 := GlobalTheory.LiftPolar.normV_cPl w
    have e3 := GlobalTheory.LiftPolar.normV_cPl (w.under (𝓞 E))
    have hf := GlobalTheory.LiftPolar.normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨unrAt_one w, _, _, h1, h2, ?_⟩
    simp only [val_one, Multiset.map_map, Function.comp_def, mul_one, inv_one, inv_pow, inv_inv]
  · obtain ⟨x, d, hd, hx2⟩ := hx
    exact ⟨algebraMap E M x, d, hd, by rw [← map_pow, hx2]; simp⟩
  · exact evenReal E M heven
  · intro w hw
    have hv : ¬ IsSplitAt (w.under (𝓞 E)) := fun h => hw (GlobalTheory.IndDataDown.isSplitAt_of_under E M _ w rfl h)
    obtain ⟨hl, hu, B, hB⟩ := hns _ hv
    refine ⟨fun h => hl ?_, unramUp E M w hu, ⟨_, hL.sat w _ B (GlobalTheory.LiftPolar.normV_under w) hB⟩⟩
    show (l : 𝓞 E) ∈ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))
    rw [Ideal.mem_comap, map_natCast]
    exact h

end GlobalTheory.CsdLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧ InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  first | exact @GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | exact GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | (intros; apply GlobalTheory.GoodCsdTwist.exists_goodCsd_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderTwists
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

end GlobalTheory.RoadU.FinTwist

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

theorem isAlg_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {κ : HChar K} {m : ℕ} (hm : 0 < m)
    (h : κ ^ m = 1) : κ.IsAlg 0 := fun k => isAlgPos_zero_of_orderDvd hm h k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (P : CuspSub K n) {κ : HChar K}
    (hκ : κ.IsAlg 0) (τ : K →+* ℂ) : (CG.mk (P.twist κ)).infChar τ = (CG.mk P).infChar τ := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 0 hκ τ]
  simp

end GlobalTheory.RoadU.FinTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSDRAllOfGood
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

set_option maxHeartbeats 1000000 in

theorem holdsS_dR_all_of_good : Inputs → SphericalLevelCondition .good .dR → SphericalLevelCondition .all .dR := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w _ B hB
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js
  obtain ⟨Q, hdec, hsplit, hram, hgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQL E Q.K Q.two a ha π hram
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hS.all
  have hrP := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' :=
    hG Q.K Ω l ι a ha P χ' ⟨hχ'.1, hχ'.2.1, hgood P hP⟩ _ hrP w' (hsplit w' hu) _ hBP
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres

end GlobalTheory.RoadU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsAlt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnrDescent

theorem main : Inputs → SphericalLevelCondition .good .unr → SphericalLevelCondition .all .unr := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB hl A h
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hsc.all
  have hscG : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hrP : Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hG Q.K Ω l ι a ha P χ' hscG (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) hrP w' (hQsplit w' hunder) B hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e

end GlobalTheory.UnrDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTorusActionRot
section
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n k : ℕ} (A : HolAtlas M n)

structure IsTorusAction (act : (Fin k → UnitAddCircle) → M → M) : Prop where

  cont : Continuous fun p : (Fin k → UnitAddCircle) × M => act p.1 p.2

  smooth : ∀ i j, ContDiffOn ℝ ∞
    (fun q : (Fin k → ℝ) × V n => A.e i (act (fun a => ((q.1 a : ℝ) : UnitAddCircle)) ((A.e j).symm q.2)))
    {q | q.2 ∈ (A.e j).target ∧ act (fun a => ((q.1 a : ℝ) : UnitAddCircle)) ((A.e j).symm q.2) ∈ (A.e i).source}

  holo : ∀ t, A.IsHolo A (act t)

  zero : ∀ y, act 0 y = y

  add : ∀ s t y, act (s + t) y = act s (act t y)

def torusAvg (act : (Fin k → UnitAddCircle) → M → M) (α : A.Fld) : A.Fld := fun x =>
  ∑ S, (∫ t, (bas n).repr (A.pullback A (act t) α x) S) • bas n S

def TypeGe (p : ℕ) (α : A.Fld) : Prop :=
  ∀ x S, (bas n).repr (α x) S ≠ 0 → p ≤ (S.filter (·.val < n)).card

def rot (t : Fin 1 → UnitAddCircle) (v : V 1) : V 1 := (AddCircle.toCircle (t 0) : ℂ) • v

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtMStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  first | exact @GlobalTheory.TwV.DelA.tieDel_all_steps | exact GlobalTheory.TwV.DelA.tieDel_all_steps | (intros; apply GlobalTheory.TwV.DelA.tieDel_all_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  first | exact @GlobalTheory.LiftPolar.main | exact GlobalTheory.LiftPolar.main | (intros; apply GlobalTheory.LiftPolar.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.UnrTwist

theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    UpperTheory.V.Af.tw (UpperTheory.V.Af.tw r μ) μ⁻¹ = r := by
  ext s i j
  simp [UpperTheory.V.Af.tw_val, smul_smul]

theorem algSat_eq' (n q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [UpperTheory.V.Af.algSat, Multiset.bind_singleton, Multiset.map_map]

end GlobalTheory.RoadU.UnrTwist

open GlobalTheory.RoadU.UnrTwist in
theorem GlobalTheory.RoadU.holdsS_good_unr : Inputs → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  intro _ hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB hl
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, H⟩ := GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := H l ι κ m (isAlgPos_of_isAlg hκ)
  have hrv : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) :=
    Units.continuous_val.comp hr.1
  have htv : Continuous fun g => ((UpperTheory.V.Af.tw r μ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμc).smul hrv
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := by
    refine Units.continuous_iff.2 ⟨htv, ?_⟩
    simp only [← map_inv]
    exact htv.comp continuous_inv
  have hT : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hc : UpperTheory.V.Af.FrobEig ι (UpperTheory.V.Af.tw r μ) w
      (UpperTheory.V.Af.algSat a (normV w) (B.map (· * κ.val w))) :=
    hcsd E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hS' (UpperTheory.V.Af.tw r μ) hT w hw _ hB' hl
  have hce : UpperTheory.V.Af.Bc.CharEig ι μ⁻¹ w ((κ.val w : ℂ))⁻¹ := by
    refine fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [MonoidHom.inv_apply, (hμ.unr_iff hart (Or.inl hl) hA).2 hu s hs, inv_one]
    · rw [MonoidHom.inv_apply, map_inv, inv_inv, hμ.frob_unr hart (Or.inl hl) hu hA hσ, map_inv₀, RingEquiv.apply_symm_apply]
  have h2 := UpperTheory.frobenius_eigenvalues_twist E Ω l ι a _ μ⁻¹ w _ _ hc hce
  rw [tw_tw_inv] at h2
  convert h2 using 1
  simp only [algSat_eq', Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  field_simp
end

