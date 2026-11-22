import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0196
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0202
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0541
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0210
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0209
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0850
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0135
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0094
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0212

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadAtExistsM
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem readAt_exists_m_alt (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hR : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) (i : D.nd.Loc)
    (s : SplitPlace D.host.E) :
    ∃ X : ReadAt P.T i s.w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w ∧
      (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (X.row σ).toIrrRep) ∧
      (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (X.rep Q).toIrrRep) ∧
      (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w X.mu) ∧
      IsComp P.cf.eta s.w X.eta := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have HR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)
  have hlaws : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := HR.recLaws
  have hrow : ∀ σ, ∃ τ : Irr (s.w.adicCompletion D.host.E) D.R.r,
      D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s τ.toIrrRep := by
    intro σ
    by_cases hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥
    · obtain ⟨τ, hτ⟩ := GlobalTheory.T.isotypic_row_local_split_exists D P.rep (D.nd.j i) (hR i).some σ hσ s
      exact ⟨Irr.ofIrrRep τ, fun _ => hτ⟩
    · exact ⟨default, fun h => absurd h hσ⟩
  choose row hrow using hrow
  have hrep : ∀ Q : D.naut.AV i, ∃ τ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t),
      IsLocS (n := D.R.nV) (P.H.av.S i Q) s τ.toIrrRep := by
    intro Q
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
    exact ⟨Irr.ofIrrRep τ, hτ⟩
  choose rep hrep using hrep
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hmuC := P.chr.muC i j0 hj0
  obtain ⟨μ, hμ, -, hμu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.tp.tup (D.nd.mu i) j0) s.w
  have hμU : GlobalTheory.SmGL.IsUnitaryChar μ := hμu (hmuC ▸ (P.chr.e1 (D.naut.muC i)).2)
  have hμP : IsComp (P.chr.e1 (D.naut.muC i)).1 s.w μ := hmuC ▸ hμ
  have eμ := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P (D.naut.muC i) s.w μ hμP
  obtain ⟨η, hη, -, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E P.cf.eta⁻¹ s.w
  have hηP : IsComp (P.chr.e1 D.naut.etaTinv).1 s.w η := P.chr.etaTinv ▸ hη
  have eη := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P D.naut.etaTinv s.w η hηP
  have hun : GlobalTheory.SplitWeil.IsUnram η := by
    have := (hlaws.sph 1 (Irr.ofDet 1 η hηP.1)).1
      (by rw [← eη]; exact (P.T.unr s.w _).1 (D.naut.etaTinv_def s.w).1)
    intro x hx
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    have hI : (fun _ : Fin 1 => x) ∈ torusO (s.w.adicCompletion D.host.E) (Fin 1) := fun _ => hx
    have h2 := hv ⟨_, iwahori_le_KO _ _ (diagT_mem_iwahori hI)⟩
    have h3 : Matrix.GeneralLinearGroup.det (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) = x := by
      ext; simp [val_diagT]
    have h4 : (η x : ℂ) * (show ℂ from v) = (show ℂ from v) := by
      have h5 : detRep (Fin 1) η (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) v = (show ℂ from v) := by
        exact h2.trans (by simp)
      have h6 := (ofChar_apply (detChar (Fin 1) η) (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x)
        (show ℂ from v)).symm.trans h5
      rw [detChar_apply, h3] at h6
      exact h6
    ext
    exact (mul_eq_right₀ hv0).1 h4
  refine ⟨⟨_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w, row, rep, μ, η⁻¹, ⟨hμ.1, hμU⟩, ⟨hηP.1.inv, fun x hx => by simp [hun x hx]⟩,
    fun σ hσ => (P.row i).1 σ s _ (hrow σ hσ), fun Q => ?_, fun c hc => ?_, fun c hc => ?_⟩,
    rfl, hrow, hrep, fun j hj => ?_, ⟨hη.1.inv, fun x => ?_⟩⟩
  · rw [D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ (hrep Q)
  · rw [eμ]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 μ hμP.1) hc).symm
  · rw [inv_inv] at hc
    rw [eη]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 η hηP.1) hc).symm
  · have : j = j0 := Fin.ext (by simp only [j0]; omega)
    subst this
    exact hμ
  · rw [MonoidHom.inv_apply, hη.2 x]
    exact inv_inv _
end GlobalTheory.TrueReading
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecTStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recProd_recSpeh_recSatake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | exact _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | (intros; apply _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroChr
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem rowChi_conj_of_mem_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hPl : _root_.GlobalTheory.MiTop.PlacedAlt f B) (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀)
    (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : β = (_root_.GlobalTheory.Fam.pk_z W).βY 0)
    (Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank) (hLz : Lz = _root_.GlobalTheory.LevZero.datZero_alt W)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq) :
    ∀ k ∈ levS (D.sp.Y 0) β Lz, rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) β Lz k := by
  obtain ⟨kk, i1, i2, i3, i4, ι, v, o, n, G, pl, hcis, hvis, htie, hshape, hpin, hread, hbot⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hW u f B kk ι v o n G pl ⟨hcis, hvis, htie, hshape, hpin, hread, hbot⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hBl := hbot.lev h0
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.BaseChain.com_z W).Pg := hBot.typ
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (f.c.V 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (f.c.V 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (f.c.V 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes W.Q.Rl.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes f.c.ψ (f.c.bes 0 D.R.rS h0).d 1 (vecB (f.c.bes 0 D.R.rS h0).o (f.c.bes 0 D.R.rS h0).ζ) : GA D (f.c.V 0) → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes W.Q.Rl.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  have hred : ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (k : GA D (D.sp.Y 0)),
      redFn (finE (D.sp.Y 0) s * β) PP (finE (D.sp.Y 0) (s * k * s⁻¹)) = redFn β PP (finE (D.sp.Y 0) k) := fun PP k => by
    rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]
  subst hβ hLz
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
    (fun k : GA D (D.sp.Y 0) => rowChi W.S.X W.Q.instEq (s * k * s⁻¹) =
      levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi W.S.X W.Q.instEq (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k := q
    have q₂ : rowChi W.S.X W.Q.instEq (s * k' * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k' := q'
    rw [GlobalTheory.ChrMatch.levChi_mul (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi,
      map_mul, Prod.snd_mul, W.S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) h0 hBot
      PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.RowBesChar.rowChi_conj_eq_psiBes D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B hE PP.1 (G (pl.symm PP)).q.e
      (G (pl.symm PP)).q.split (hBot.loc PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (GlobalTheory.ChrMatch.suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi W.S.X W.Q.instEq
      (s * ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * n * (show GA D (D.sp.Y 0) from f.g.b 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro (b : GA D (D.sp.X 0)) hb hk
    have hk' : (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
      rw [hemb b]; exact hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hW u f B hbot.trace hbot.adapted a₀ hH0 b hb).2 hk'
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    subst ht
    have h3 := (congrArg (rowChi W.S.X W.Q.instEq) e).trans h1
    rw [hemb b] at h3
    exact h3
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    show rowChi W.S.X W.Q.instEq (s * k * s⁻¹) = levChi (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) k
    rw [GlobalTheory.PrinFrame.rowChi_eq_one D W.S.X W.Q.instEq hE (_root_.GlobalTheory.BaseChain.com_z W).Pg hTP hBot.com.split _ hSt _ (hmem k hk)
      (fun PP hPP => (hred PP k).trans (hr1 PP hPP))]
    exact (GlobalTheory.ChrMatch.levChi_of_red_one _ _ _ rfl rfl hr1).symm
set_option maxHeartbeats 1000000 in
theorem row_character_eq_extension_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl a₀ hH0 a ha hac hSt κ hκ hκS hP _
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    have := GlobalTheory.Chain.StepVac.rank_Yc (D := D) (j := 0) (Nat.zero_le _)
    exact le_of_eq (this.trans (by simp))
  have hM := _root_.GlobalTheory.T.central_adapted_element_property_alt W hW u f B hPl a₀ hH0 a ha hac hSt
  obtain ⟨β, hβ⟩ : ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), β = (_root_.GlobalTheory.Fam.pk_z W).βY 0 := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Formalism.L2.DIV.LevDat D.host.E ℂ (D.sp.Y 0).rank, Lz = _root_.GlobalTheory.LevZero.datZero_alt W := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = _root_.GlobalTheory.MiTop.translationElement f B a₀ a := ⟨_, rfl⟩
  have hfr : _root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a = finE (D.sp.Y 0) s * β := by rw [hs, hβ]; rfl
  have hSt' : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset) := by
    rw [← hfr]; exact hSt
  have key := _root_.GlobalTheory.LevZeroChr.rowChi_conj_of_mem_alt W hW u f B hPl a₀ hH0 a hac _ s rfl hs β hβ Lz hLz hSt'
  have hM' : ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) →
      rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H → κ ∈ rowJ W.S.X W.Q.instEq := by
    rw [← hfr, hLz]; exact fun κ h1 h2 h3 => (hM κ h1 h2).2 h3
  have hκS' : finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β) := by rw [← hfr]; exact hκS
  have hP' : rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ) ∈ Lz.P.H := by rw [← hfr, hLz]; exact hP
  suffices hgoal : rowChi W.S.X W.Q.instEq κ =
      ((ext1 Lz.P.H Lz.P.chi (rTup (finE (D.sp.Y 0) s * β) Lz (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) by
    rw [← hfr, hLz] at hgoal; exact hgoal
  have e1 : Lz.s = 0 := by rw [hLz]; rfl
  have e2 : Lz.Q = ∅ := by rw [hLz]; rfl
  have e3 : (D.sp.Y 0).rank ≤ Lz.r := by rw [hLz]; exact hn
  clear hκS hP hM hSt hfr hs hβ hLz
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  have hmem : ∀ k ∈ levS (D.sp.Y 0) β Lz, s * k * s⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    intro k hk
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine hM' _ (hfin s k hf) hs' ?_
    rw [hfe, GlobalTheory.FrameConj.rTup_conj]
    exact hl.2
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  rw [hfe, GlobalTheory.FrameConj.rTup_conj] at hP' ⊢
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) β Lz := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS'
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS', fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ e3 _,
        fun PP hPP => absurd (e2 ▸ hPP) (Finset.notMem_empty _)⟩, hP'⟩
  refine (key hmem k₀ hk₀).trans ?_
  unfold levChi levFn
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
end GlobalTheory.LevZeroChr
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TypeRec GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem rowTruth_of_labelTie_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep :=
  _root_.DiscreteGroups.sglob.DzType.Rt.typeLab_of_local_m_alt
end DiscreteGroups.sglob.DzType.Rt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScOfSck
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem sc_of_sck_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (h : _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL) : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShortVectorWeightBound
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace GlobalTheory.HSShortRoad
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem short_vector_weight_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  intro h2 _hDG hSz hF
  obtain ⟨C₂, c₂, H₂⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison h2
  have H₄ := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (Closed.and (Closed.and _root_.GlobalTheory.HSApp.wtBig_run_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz))
    (Closed.and (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz) (Closed.and hSz hF))) ?_
  intro eps Fm CH heps h
  obtain ⟨⟨⟨_, -, a₁⟩, ⟨_, -, a₂⟩⟩, ⟨_, -, a₃⟩, ⟨_, -, a₄⟩, ⟨_, -, a₅⟩⟩ := h
  have e₆ : _root_.GlobalTheory.CovTop.EventuallyAtAllPoints Fm fun x _ ι _ => 6 * C₂ ≤ (Fm.L x ι).sc.L := by
    refine ⟨(6 * C₂) ^ eps⁻¹, fun x hx hle ι p _ => ?_⟩
    have hx1 := Fm.L_x x ι hx
    have he := Fm.L_eps x ι
    have h0 : (0 : ℝ) ≤ 6 * C₂ := by positivity
    show _ ≤ (Fm.L x ι).sc.x ^ (Fm.L x ι).sc.eps
    rw [hx1, he]
    calc 6 * C₂ = ((6 * C₂) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h0 heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hle heps.le
  obtain ⟨x0, a⟩ := ((((a₁.and a₂).and a₃).and a₄).and a₅).and e₆
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨⟨b₁, b₂⟩, b₃⟩, b₄⟩, b₅⟩, hCL⟩ := a x hx hle ι p hp
  clear a a₁ a₂ a₃ a₄ a₅ e₆
  have hW := b₁ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := b₂ i hi
  obtain ⟨hLaw, hIn, hL, hM, hFs, hfr, -, -, hf8, hr, hc₁, hκ2, hPP, -, -, -, -, hwt⟩ := b₃ i hi Y hY
  have s1 : 1 ≤ (Fm.L x ι).sc.b := (b₄ i).1
  have s2 : (Fm.L x ι).sc.b ≤ (Fm.parT x hx ι).PP * kap p i := (b₄ i).2.2.2.2.2.1
  have hFl := b₅ i hi Y hY
  have hdim := (GlobalTheory.T.anchoredWeight_indefiniteLift_gaps p (Fm.params x hx ι) i hi).2.1
  clear b₁ b₂ b₃ b₄ b₅
  unfold zBase at hPP hwt
  have hY' : Y.Good _ (391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2) := hY.1
  replace H₂ := fun la a b c Z => H₂ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY' _ hL hM hFs hfr le_rfl _ hFl
    (by rwa [abs_neg]) la a b c Z
  replace H₄ := H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY'
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hgap : ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ FlagTan.dimFlag (dat p i) + 1 := by
    have : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ FlagTan.dimFlag (dat p i) + 1 := by
      rw [hdim]
      generalize (Fm.D x ι).R.f = f at hf8 ⊢
      generalize (Fm.D x ι).R.r = r at hr ⊢
      have : 9 * r ≤ r.choose 2 := by
        rw [Nat.choose_two_right]
        exact (Nat.le_div_iff_mul_le two_pos).2 (by nlinarith [Nat.mul_le_mul_left r (show 18 ≤ r - 1 by omega)])
      nlinarith [Nat.mul_le_mul_left f this, Nat.mul_le_mul hf8 hr]
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := le_mul_of_one_le_left (by linarith) hfr1
  have hZ : 1 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) := hL.trans hLZ
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hPk : 1 ≤ (Fm.parT x hx ι).PP * kap p i := s1.trans s2
  have hκpos : 0 < kap p i := by
    by_contra hneg
    have h0 : (Fm.parT x hx ι).PP * kap p i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPP0 (not_lt.1 hneg)
    exact absurd (hPk.trans h0) (by norm_num)
  have hκ : 1 ≤ kap p i := one_le_sz hκpos
  have hZ3 : 0 ≤ (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 := by positivity
  refine ⟨zero_le_one.trans hPk, fun Z j hj => ?_⟩
  have hg := gapGe_wt hW j
  have ha := antitone_of_gapGe (by positivity) hg
  have hb : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j τ) ((dat p i).p - 1) :=
    fun τ => hgap.trans (hg τ ((dat p i).p - 1) (by omega))
  have hs := hwt j hj
  have h1 := hs.trans (le_mul_of_one_le_left (by positivity) one_le_two)
  have hX := H₂ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha hb
    (log_size_le (by positivity) hL hfr hκ hκ2 (by positivity) (le_trans (le_of_eq (sum_univ_inst _)) h1)) Z
  obtain ⟨n, w, Λ, hSG, hΛ, _hn⟩ := hX
  have hY4 := H₄ ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ : WtPar (dat p i)).wt j) ha (fun τ => le_trans (by omega) (hb τ))
  obtain ⟨_hGA, hGO⟩ := hY4
  have hsp := span_of_shortGen hSG (hGO Z).2.2
  obtain ⟨hmem, hspan⟩ := hsp
  refine ⟨n, w, hmem, hspan, fun q σ => ?_⟩
  have hΛ' : Real.log Λ ≤ (Fm.parT x hx ι).PP * kap p i := by
    refine hΛ.trans (le_trans ?_ (bound_le c₂ hZ (hCL.trans hLZ) hPP hκ))
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ hZ3) le_rfl) c₂
    exact le_trans (le_of_eq (sum_univ_inst _)) hs
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hSG.one_le
  calc _ ≤ Λ := hSG.le q σ
    _ = Real.exp (Real.log Λ) := (Real.exp_log hΛ0).symm
    _ ≤ _ := Real.exp_le_exp.2 hΛ'
end GlobalTheory.HSShortRoad
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_path_weight_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => 0 ≤ PP * kap p i ∧ ∀ Z, ∀ j ≤ lenT p i PP, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j)), (∀ q, v q ∈ latOn Y.U Z _) ∧ Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j) 0) σ (v q).1 ≤ Real.exp (PP * kap p i) := by
  first | exact @_root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt | exact _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt | (intros; apply _root_.GlobalTheory.HSShortRoad.short_vector_weight_bound_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TauTrue
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.tauTrue_alt {a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C} (x : TauTrue a.exp) : TauTrue ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).exp := (by with_unfolding_all exact (x :))
end
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEigenCompatibilitySixth
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_sixth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  first | exact @_root_.GlobalTheory.EigStrInert.str_inert_tyz | exact _root_.GlobalTheory.EigStrInert.str_inert_tyz | (intros; apply _root_.GlobalTheory.EigStrInert.str_inert_tyz <;> assumption)
end
end

