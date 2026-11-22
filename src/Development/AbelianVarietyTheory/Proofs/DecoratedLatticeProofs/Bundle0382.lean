import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemDen
open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem conjP_eq_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ Q = cP Q :=
  HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

def evQ (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E where
  toFun z := Φ z Q
  map_one' := by rw [map_one]; rfl
  map_mul' a b := ev_mul a b Q
  map_zero' := ev_zero Q
  map_add' a b := ev_add a b Q

theorem delta_mem {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)}
    {x : AE D} (h : IsDelta Φ P x) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ x Q ∈ Q.adicCompletionIntegers D.host.E := by
  by_cases hQ : Q = P
  · subst hQ; rw [h.2.1]; exact (Q.adicCompletionIntegers D.host.E).one_mem
  · rw [h.2.2 Q hQ]; exact (Q.adicCompletionIntegers D.host.E).zero_mem

end GlobalTheory.OffIdemDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPNotMemOfIdemSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerLift

theorem conjP_notMem_of_isIdemSum {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro P hP hP'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have horth := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_conj_orth hes hsum hc P hP (Formalism.L2.Col.conjPrime₂ P) hP'
  have h1 : Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.Col.conjPrime₂ P))) P := by
    refine GlobalTheory.MovedIdem.isIdemAt_conj (hes _ hP') fun x => ?_
    show x ∈ P.asIdeal ↔ Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) ∈ P.asIdeal
    have : Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) = x := by
      apply RingOfIntegers.ext
      simp [Formalism.L2.Col.cO]
    rw [this]
  have heq : cA D (es (Formalism.L2.Col.conjPrime₂ P)) = es P :=
    (GlobalTheory.ExportSeries.idemAt_eq h1).symm.trans (GlobalTheory.ExportSeries.idemAt_eq (hes P hP))
  rw [heq, (hes P hP).1.1] at horth
  have hI := hes P hP
  rw [horth] at hI
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := (hI.2 x hx0).1 hxP
  rw [zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem natCast_smul_inv_smul {E : Type} [Field E] [NumberField E] {a b : ℕ} (c : ℕ) (hc : 0 < c)
    (y : Formalism.L2.Col.HomE E a b) : ((c : 𝓞 E)) • ((c : E)⁻¹ • y) = y := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc0, one_smul]

set_option maxHeartbeats 800000 in

theorem exists_rep_add_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ (SX : Finset (VV D.what₂.Tau S.rank T.rank)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → ∀ (px : VV D.what₂.Tau S.rank T.rank → Formalism.L2.Col.HomE D.host.E S.rank T.rank), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → ∀ g : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (∀ P ∈ SS, (c : D.host.E) • g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) → ∃ x ∈ SX, ∀ P ∈ SS, g + px x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS he N N' hN hN' c hc SX hSX px hpx g hg
  have hSS := conjP_notMem_of_isIdemSum he
  have hAA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.leading_constant_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  have hspan : ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    Formalism.L2.Ker.lf_span _ hAA N N' hN.1.fg hN'.1.span_eq_top
  have hneg : ∀ P ∈ SS, (c : D.host.E) • (-g) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := fun P hP' => by
    rw [smul_neg]; exact neg_mem (hg P hP')
  have hL := Formalism.L2.Ker.lift_exists_alt D.host.E S.rank T.rank SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c hc hSS hspan (-g) hneg
  obtain ⟨hsA, hsP⟩ := hL
  generalize Formalism.L2.Ker.liftS SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c (-g) = s at hsA hsP
  have hmem : embH (tauE D) δ s ∈ AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c :=
    ⟨s, hsA, rfl⟩
  obtain ⟨x, hxS, hxL⟩ := hSX.2.2 _ hmem
  obtain ⟨β, hβ, hβe⟩ := hxL
  have hne : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hβs : β = s - px x := by
    apply Formalism.L2.Ker.embH_inj (tauE D) hP.ne
    rw [map_sub, (hpx x hxS).2]
    exact hβe
  refine ⟨x, hxS, fun P hPS => ?_⟩
  have h1 : s + g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    have h2 := hsP P hPS
    rw [sub_neg_eq_add] at h2
    have h3 : ((c : 𝓞 D.host.E)) • ((c : D.host.E)⁻¹ • (s + g)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      Submodule.smul_mem _ _ h2
    have e3 := natCast_smul_inv_smul c hc (s + g)
    rwa [e3] at h3
  have h4 : β ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hβ⟩
  have e5 : g + px x = (s + g) - β := by rw [hβs]; abel
  rw [e5]
  exact sub_mem h1 h4

end GlobalTheory.PerLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorPairForm
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

theorem op_col (W : RealPack ex) (u w : D.what₂.Word) (hwu : w = u) (hc : W.P.I.wU w = W.P.I.wU u)
    (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (hT : IsCol W u T (colC W u x)) :
    (((pwOf W.S W.Q.hin w).op (ramCrd (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) x) : HHX W.S.X) : L2X W.S.X) =
      PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T := by
  subst hwu
  have hi : ∀ i : Fin (W.P.Dc.a (W.P.I.wU w)), Fin.cast (congrArg W.P.Dc.a hc).symm i = i := fun i => Fin.ext rfl
  have hfun : (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) =
      (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) := by
    funext i
    exact congrArg (fun k => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single k (1 : D.what₂.LL))))) (hi i)
  rw [hfun]
  have hr : Fintype.linearCombination ℂ (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) x =
      D.eMu w (colC W w x) := by
    refine (Fintype.linearCombination_apply ℂ _ x).trans ?_
    simp [colC, map_sum, map_smul]
  refine op_eq (pwOf W.S W.Q.hin w) _ T ?_
  show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr w) W.S.Y.hK T = _
  refine hT.trans ?_
  show _ = ((Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ _ x) : (D.mem w).A.Mu0) : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)
  exact congrArg (fun z : (D.mem w).A.Mram => (z : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)) hr.symm

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

theorem pairForm : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → PairForm W v := by
  intro hDS hCusp D L hT Gi Gl Kc Yd cX ex W hB v hv
  have hM := (GlobalTheory.MiTop.botHyp_match W hB).2.2.2.2.2
  obtain ⟨v₀, hv₀, hF⟩ := exists_eval (W.Q.seeEval hB.see.2) W.Q.instEq W.Q.ιS_eq
  have key : ∃ l : ℂ, l ≠ 0 ∧ ∀ e : W.Q.Rl.HE.H,
      W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
        rowOf W e (PiTensorProduct.tprod ℂ v₀) = l • rowOf W e (PiTensorProduct.tprod ℂ v) := by
    by_cases hl : ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v
    · obtain ⟨l, hl0, hl⟩ := hl
      exact ⟨l, hl0, fun e _ => (congrArg (rowOf W e) hl).trans ((rowOf W e).map_smul l _)⟩
    · refine ⟨1, one_ne_zero, fun e he => ?_⟩
      by_cases h0 : rowOf W e = 0
      · rw [h0]
        exact (smul_zero (1 : ℂ)).symm
      · obtain ⟨F, h1, h2, -⟩ := hF ⟨W.Q.Rl.HE.e e, he⟩
        exact absurd (GlobalTheory.T.unit_vector_rows_conjugate hDS hCusp W hB v₀ v hv hv₀ (rowOf W e) (hM e he) h0 F h1 h2) hl
  obtain ⟨l, hl0, hl⟩ := key
  refine ⟨starRingEnd ℂ (W.Q.uS * (W.Q.κS : ℂ)) * l, mul_ne_zero ?_ hl0, ?_⟩
  · have hu : W.Q.uS ≠ 0 := by
      intro h
      have := W.Q.uS_norm
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact (map_ne_zero _).2 (mul_ne_zero hu (Complex.ofReal_ne_zero.2 W.Q.seeK.1.ne'))
  intro e he u m hm x x' hx T b hTc hP
  obtain ⟨φ, hφ, rfl⟩ := hP
  refine (inner_join (twQ W.P) W.Dcf W.Spf (cxW W).zs W.P.Zs W.Q.zs W.P.Dc W.Q.dc W.S.Y.hK W.S.G W.Q.wdD
    (fun y => pwOf W.S W.Q.hin (W.Q.wdD y)) W.Q.bR (W.Q.sp.trans W.Q.spPin) W.Q.sEE W.Q.sEEc W.Q.sEEj e m (W.P.I.wU u) hm
    x' x hx.symm).trans (congrArg (cj (twQ W.P)) ?_)
  obtain ⟨F, h1, -, h3⟩ := hF ⟨W.Q.Rl.HE.e (Tw.out e), he⟩
  have hz := (congrArg (fun b => (((pwOf W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd b x) : HHX W.S.X) : L2X W.S.X))
    (funext (hB.pins.bR_read (W.P.I.wU u)))).trans
    (op_col W u (W.Q.wdD (W.P.I.wU u)) (W.Q.wdD_wU u) (W.Q.wU_wdD (W.P.I.wU u)) x T hTc)
  refine Eq.trans ?_ (inner_smul_star W.Q.instEq _ _ _ l (W.Q.uS * (W.Q.κS : ℂ)) (hl (Tw.out e) he) F φ _ h1 hφ _ _ h3 hz)
  exact congrArg (fun y => ⟪Tw.out y, (pwOf W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd (W.Q.bR (W.P.I.wU u)) x)⟫_ℂ)
    (W.Q.seeDef e he)

end GlobalTheory.MiTop.PairingL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem PM_map {r : ℕ} {B : Type} [CommRing B] (f : AE D →+* B) (M : Matrix (Fin r) (Fin r) (AE D)) :
    (PM M).map f = f (eps D) • M.map f + f (1 - eps D) • (1 : Matrix (Fin r) (Fin r) B) := by
  ext i j
  simp only [PM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul]
  split_ifs <;> simp

theorem cT_PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) =
      eps D • cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D)) := by
  unfold cT
  rw [PM_map, RingHom.map_sub, RingHom.map_one, sig_eps, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem PM_unit {r : ℕ} (J M : Matrix (Fin r) (Fin r) (AE D))
    (hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * J * M = J) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) * J * PM M = J := by
  rw [cT_PM, PM]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add, hM]
  rw [← add_smul, add_sub_cancel, one_smul]

def PGL (D : D7) (r : ℕ) : GL (Fin r) (AE D) →* GL (Fin r) (AE D) where
  toFun g := ⟨PM g.1, PM (g⁻¹).1, by rw [← PM_mul, Units.mul_inv, PM_one], by rw [← PM_mul, Units.inv_mul, PM_one]⟩
  map_one' := Units.ext PM_one
  map_mul' a b := Units.ext (PM_mul a.1 b.1)

theorem PGL_mem (V : HSp D) (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    PGL D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  PM_unit _ g.1 hg

def pf (V : HSp D) (h : GA D V) : GA D V :=
  (⟨PGL D V.rank (matHom V h), PGL_mem V (matHom V h) (Subtype.property (h : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram)))⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem mt_pf (V : HSp D) (h : GA D V) : Formalism.L2.Theta.mt V (pf V h) = PM (Formalism.L2.Theta.mt V h) := rfl

theorem pf_one (V : HSp D) : pf V 1 = 1 := by
  apply Subtype.ext
  show PGL D V.rank (matHom V 1) = 1
  rw [map_one, map_one]

theorem pf_fin (V : HSp D) (h : GA D V) : pf V h ∈ GfC V := by
  show infHom V (pf V h) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (pf V h)).map (infPart D) = 1
  rw [mt_pf, PM_map, infPart_eps, RingHom.map_sub, RingHom.map_one, infPart_eps, sub_zero, zero_smul, zero_add, one_smul]

theorem finM_pf (V : HSp D) (h : GA D V) : finM V rfl (pf V h) = finM V rfl h := by
  rw [finM_rfl, finM_rfl, mt_pf, PM_map, toEAf_eps, RingHom.map_sub, RingHom.map_one, toEAf_eps, sub_self, zero_smul, add_zero, one_smul]

theorem continuous_pf (V : HSp D) : Continuous (pf V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h :=
    Units.continuous_val.comp continuous_subtype_val
  have hP : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => PM M :=
    (continuous_const_smul _).add continuous_const
  refine Continuous.subtype_mk (f := fun h => PGL D V.rank (matHom V h)) (Units.continuous_iff.2 ⟨hP.comp hm, ?_⟩) _
  have e : (fun h : GA D V => ((PGL D V.rank (matHom V h))⁻¹ : GL (Fin V.rank) (AE D)).val) =
      fun h => PM (Formalism.L2.Theta.mt V h⁻¹) := by
    funext h
    rw [← map_inv, ← map_inv]; rfl
  rw [e]
  exact hP.comp (hm.comp continuous_inv)

end GlobalTheory.AdForm.RdLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConjStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLatticeHeight_selfDual_lattices_eq_conj : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  first | exact @GlobalTheory.Core.Rk.IP.hgtL_eq_conj_of_selfDual | exact GlobalTheory.Core.Rk.IP.hgtL_eq_conj_of_selfDual | (intros; apply GlobalTheory.Core.Rk.IP.hgtL_eq_conj_of_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbZeroTrivialWittDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.FinPl.LastInhab

open GlobalTheory.Unf.Inhab

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem eventually_charUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : Pl D in Filter.cofinite, CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ intAt D (· = v) := by
    refine ⟨Ideal.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun w => ?_⟩, ?_⟩
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, h1, sub_self]
    · rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, GlobalTheory.FinPl.compAt, RingHom.comp_apply, h2 _ w.2, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]; exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  obtain ⟨y, hy, hye⟩ : ∃ y, y ∈ intAt D (· = v) ∧ (x : AE D) - 1 = N • y := ⟨_, hv _ ha, e⟩
  refine hker x ⟨h1, h3, h4⟩ ⟨finPart D y, hy.2, ?_⟩
  rw [← RingHom.map_one (finPart D), ← RingHom.map_sub, hye]
  exact (finPart D).toAddMonoidHom.map_nsmul _ _

end GlobalTheory.FinPl.LastInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charExponent_infinity_kernel_shift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_exp_shifts | exact GlobalTheory.AdForm.TwDat.chr_exp_shifts | (intros; apply GlobalTheory.AdForm.TwDat.chr_exp_shifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierHyperbolicTermsNearRefereStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_hyperbolic_terms_near_reference : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  first | exact @GlobalTheory.ScalW.ef_near_ref | exact GlobalTheory.ScalW.ef_near_ref | (intros; apply GlobalTheory.ScalW.ef_near_ref <;> assumption)
end

