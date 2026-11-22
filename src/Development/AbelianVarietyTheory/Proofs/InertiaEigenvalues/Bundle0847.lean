import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0839
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicForms_levelGroup_eq_twistLevel : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  first | exact @GlobalTheory.MtLev.levMem | exact GlobalTheory.MtLev.levMem | (intros; apply GlobalTheory.MtLev.levMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfHyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BaseChangeClosing

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem conclusion1_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
      CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D := by
  intro hNT hB hMW hGU hSC hL D T A hCG hAU
  obtain ⟨hP, hS, hSat⟩ := GlobalTheory.T.rec_product_speh_satake hGU hSC hL D.nd D.naut T
  exact GlobalTheory.DefiniteBCFrozen.baseChangeDefinite_of_cmDatum_recLaws D (recT T hL) hNT hB
    (GlobalTheory.DiscreteSpectrumCM.discreteSpectrum_of_discreteSpectrumGL hMW D.host.E) hP hS hSat
    (GlobalTheory.T.cuspidal_of_local_langlands hL D T hCG) (GlobalTheory.T.unitary_of_local_langlands hL D T A hAU)

end GlobalTheory.BaseChangeClosing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpanStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlip_maps_halfTranslates_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (s : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → s ≠ 0 → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → om (z⁻¹, 1) f₀ = s • ∑ y ∈ Y, heisO ψ V W y f₀ → ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → e' = e - eT + cA D eT → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (s • F) = f := by
  first | exact @GlobalTheory.FlipTranslates.flip_translates | exact GlobalTheory.FlipTranslates.flip_translates | (intros; apply GlobalTheory.FlipTranslates.flip_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BasePairChar

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem unrAt_of_unramAt {c : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hc : GlobalTheory.WeilParts.UnramAt ε c) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.LFun.UnrAt c w := by
  subst hw
  have key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).2 fun P => by
      rw [show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) =
        Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]
      by_cases e : P = w
      · subst e; rw [GlobalTheory.LFun.finSingle_self]; exact hy.le
      · rw [GlobalTheory.LFun.finSingle_ne e, map_one]
  obtain ⟨α, rfl, h1, -⟩ := hε
  intro y hy
  have hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) =
      (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1 := by
    refine GlobalTheory.LFun.tens_ext ?_ ?_
    · simp only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]
    · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      have e2 := GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y
      refine FiniteAdeleRing.ext _ fun P => ?_
      simp only [map_mul, map_sub, map_one, e2]
      have hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E
          (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) =
          GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl
      rw [hA]
      change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P *
          (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1
      rw [GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]
      by_cases hP : P = w
      · subst hP
        rw [GlobalTheory.LFun.finSingle_self]
        have : α (P.under (𝓞 D.host.F)) = 1 := h1
        rw [this, map_one, one_mul]
      · rw [GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]
  have h := hc _ hs (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold Formalism.L2.Host.IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h).trans (map_one _)

open Formalism.L2.JoinChr in
set_option maxHeartbeats 1000000 in

theorem base_pair_char : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ bad : ℕ, (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1 := by
  intro D V W B hB χ hc bad hbad
  classical
  refine ⟨fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have hPg : GlobalTheory.ExportSeries.SplitSet B.G.Pg := by
      obtain ⟨P, h1, -, h3⟩ := hB.places.split
      exact h3.mono h1
    have hu : GlobalTheory.StepLaw.UnrOff (B.mu * B.eta⁻¹) (B.G.Pg ∪ B.de.Q) :=
      (GlobalTheory.StepLaw.UnrOff.mul
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.unram hPg Finset.subset_union_left)
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hB.de.unram hB.de.split Finset.subset_union_right)).mul
        (GlobalTheory.ExportSeries.TupleChars.unrOff_of_unramEverywhere hB.eta.2.1 _).inv
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq hc Q).1 (unrAt_of_unramAt hε (hu _ ε hε fun PP hPP he => ?_) rfl)
    have hm : (bad : 𝓞 D.host.E) ∈ PP.asIdeal := hbad PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP he with h | h
    · exact hQ (h ▸ hm)
    · rw [h, GlobalTheory.IdemSupport.mem_cP, map_natCast] at hm
      exact hQ hm
  · obtain ⟨e, he⟩ := GlobalTheory.StdFrames.exists_isIdemAt hQ
    have he' : Formalism.L2.NTheta.IsIdemAt (cA D e) (GlobalTheory.IdemSupport.cP Q) :=
      GlobalTheory.MovedIdem.isIdemAt_conj he fun x => GlobalTheory.IdemSupport.mem_cP Q x
    have p1 := GlobalTheory.HeckeDetChar.isPlIdem he
    have p2 := GlobalTheory.HeckeDetChar.isPlIdem he'
    have hs : star ((Formalism.L2.Host.upF D.host.F k : D.host.Eˣ) : D.host.E) = (Formalism.L2.Host.upF D.host.F k : D.host.Eˣ) :=
      (D.sp.cm.fixed _).2 ⟨k, rfl⟩
    let y : (AE D)ˣ := locU p1.1 (Formalism.L2.Host.upF D.host.F k)
    have h1 := hc.2 Q e p1 _ y (locU_val p1.1 _)
    have h2 := hc.2 _ (cA D e) p2 (Formalism.L2.Host.upF D.host.F k) (Units.map (cA D).toMonoidHom y) (by
      change cA D (y : AE D) = _
      rw [locU_val, locE, locE, map_add, map_one, map_mul, map_sub, map_one, GlobalTheory.IdemSupport.cA_incA, hs])
    have r2 : ResEta D B.eta 1 := hB.eta.2.2.1
    have r0 : ResEta D B.mu0 0 := GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.real
    have r1 : ResEta D B.de.chi 0 := GlobalTheory.SplitChange.resEta_zero_of_triv r2 hB.de.real
    have hconj : (B.mu * B.eta⁻¹) (Units.map (cA D).toMonoidHom y) = ((B.mu * B.eta⁻¹) y)⁻¹ := by
      simp only [GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ConjAdjWeil.chi_conj r0,
        GlobalTheory.ConjAdjWeil.chi_conj r1, GlobalTheory.ConjAdjWeil.chi_conj r2, mul_inv, inv_inv]
    rw [Formalism.L2.Host.HChar.resFin_apply, GlobalTheory.ClassScalarValue.above_eq, Finset.prod_pair hQ.symm]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, ← h1, ← h2, hconj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.BasePairChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

section Op

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def opP (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (c : WO S T →₀ ℂ) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  ∑ y ∈ c.support, c y • (GlobalTheory.SplitScalar.heisL ψ S T y * om (1, h))

theorem opP_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (c : WO S T →₀ ℂ) (h : GA D T)
    (f : WO S T → ℂ) : opP ψ S T om c h f = comb ψ S T c (om (1, h) f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, GlobalTheory.SplitScalar.heisL_apply, comb,
    Finsupp.sum]

theorem opP_comm {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) {e : AE D} {c : WO S T →₀ ℂ}
    (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {B : Module.End ℂ (WO S T → ℂ)} (hB : CommAt ψ S T e B)
    (hBh : ∀ f, IsThetaFunO ψ S T f → B (om (1, h) f) = om (1, h) (B f)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    B (opP ψ S T om c h f) = opP ψ S T om c h (B f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, (hB _ (hpres _ _ hf)).2 y (hc y hy), hBh f hf]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {y : WO S T} (hy : IsHalf e y) : y.map (infPart D) = 0 :=
  Matrix.ext fun a b => by
    rw [Matrix.map_apply, ← hy a b, RingHom.map_mul, he, zero_mul]
    rfl

theorem opP_theta {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) (hψ : IsStdChar D ψ (-1)) {e : AE D}
    (he : infPart D e = 0) {c : WO S T →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opP ψ S T om c h f) := by
  rw [opP_apply, comb, Finsupp.sum]
  exact theta_sum _ _ f hf fun y hy =>
    theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_half he (hc y hy)) (hpres _ _ hf))

end Op

end GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

set_option maxHeartbeats 800000 in

theorem placeOp_keep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv h hh c hc f hT hCl hL
  have hW := hω i t
  obtain ⟨-, -, hcA, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hε := (hfin v).2.2
  have hεe := placeIdem_eq hε
  have hinf := (hfin v).1
  have hce := hcA (.inl v)
  have hpres := hW.om_pres

  have hk : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
      R.ωP i t (κ⁻¹, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ⁻¹, 1) φ) ∧
      R.ωP i t (κ, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ, 1) φ) := by
    intro κ hs φ hφ
    have h1 := suppF_of_drop hs hε
    rw [hεe] at h1
    have h2 := (suppGroup _ (1 - idem D (.inl v))).inv_mem h1
    have hcomm : ∀ k : GA D (Vc D i), ∀ ψ', R.ωP i t (k, 1) (R.ωP i t (1, h) ψ') = R.ωP i t (1, h) (R.ωP i t (k, 1) ψ') := by
      intro k ψ'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        one_mul, mul_one, one_mul]
    exact ⟨opP_comm hpres hc h (commAt_om hW h2) (fun ψ' _ => hcomm _ ψ') hφ,
      opP_comm hpres hc h (commAt_om hW h1) (fun ψ' _ => hcomm _ ψ') hφ⟩
  have hth := opP_theta hpres hW.std hinf hc h hT.1
  rw [← opP_apply]
  refine ⟨⟨hth, fun κ hκ hs => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hth, fun c' hc' h0 => ?_⟩⟩
  · rw [(hk κ hs f hT.1).2, hT.2 κ hκ (suppIn_of_drop hs), map_smul]
  · obtain ⟨w, hw, how⟩ := hov
    have h0 := hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
    unfold avgW at h0 ⊢
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h0, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : mirC R i PP a tr z g = 0
    · rw [hg, zero_mul, zero_smul, zero_smul, map_zero]
    · rw [map_smul, (hk (κ g) (hsup g hg) f hT.1).1]
  ·
    have hu : ∀ u ∈ c'.support, ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
        heisO R.ψ _ _ u (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (heisO R.ψ _ _ u φ) := by
      intro u hu φ hφ
      have hoff := hc' u hu
      have he0 : idem D (.inl v) • u = 0 := Matrix.ext fun a b => by
        rw [Matrix.smul_apply, smul_eq_mul, ← hεe]
        exact hoff.2 v hv _ hε a b
      have hact : actO (Vc D i) (Wc D i) 1 h u = u := by
        have hM : Formalism.L2.Theta.mt (Wc D i) h - 1 = idem D (.inl v) • (Formalism.L2.Theta.mt (Wc D i) h - 1) :=
          Matrix.ext fun a b => (hh a b).symm
        rw [actO, inv_one, mt_one, Matrix.mul_one]
        conv_lhs => rw [← sub_add_cancel (Formalism.L2.Theta.mt (Wc D i) h) 1]
        rw [Matrix.add_mul, Matrix.one_mul, hM, Matrix.smul_mul, ← Matrix.mul_smul, he0, Matrix.mul_zero, zero_add]
      have := opP_comm hpres hc h (commAt_heis hW.std hce hoff.1 he0)
        (fun ψ' hψ' => by rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, hW.om_heis _ _ _ _ hψ', hact]) hφ
      rwa [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply] at this
    have h1 := hL.2 c' hc' h0
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h1, map_finsuppSum]
    refine Finset.sum_congr rfl fun u hu' => ?_
    dsimp only
    rw [map_smul, hu u hu' f hT.1]

end GlobalTheory.DownLift.GenSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  first | exact @GlobalTheory.LatTranslate.lat_translate | exact GlobalTheory.LatTranslate.lat_translate | (intros; apply GlobalTheory.LatTranslate.lat_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenformStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, DownEig R i t := by
  first | exact @GlobalTheory.DownEigen.downEig | exact GlobalTheory.DownEigen.downEig | (intros; apply GlobalTheory.DownEigen.downEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTupleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualType_residueChars_unramified_tuple : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q → (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧ GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  first | exact @GlobalTheory.ExportSeries.TupleChars.tuple_chars | exact GlobalTheory.ExportSeries.TupleChars.tuple_chars | (intros; apply GlobalTheory.ExportSeries.TupleChars.tuple_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelicStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  first | exact @GlobalTheory.LevelSeries.flip_central_exists | exact GlobalTheory.LevelSeries.flip_central_exists | (intros; apply GlobalTheory.LevelSeries.flip_central_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldCurveStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_field_curve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  first | exact @GlobalTheory.DeepCoeff.exists_coeff_unramified | exact GlobalTheory.DeepCoeff.exists_coeff_unramified | (intros; apply GlobalTheory.DeepCoeff.exists_coeff_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZeroStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  first | exact @GlobalTheory.LevelSeries.exists_invariant_form_idemSum | exact GlobalTheory.LevelSeries.exists_invariant_form_idemSum | (intros; apply GlobalTheory.LevelSeries.exists_invariant_form_idemSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunctionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_components_of_adelic_invariant_function : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  first | exact @GlobalTheory.CompFactor.exists_factor_comp | exact GlobalTheory.CompFactor.exists_factor_comp | (intros; apply GlobalTheory.CompFactor.exists_factor_comp <;> assumption)
end

