import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarCharacterSquareEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

theorem rowChi_conj_of_mem (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)
    (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1)
    (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hE : GlobalTheory.Core.Mi.IdE S.X) (hB : d.Base)
    (hTP : IsTypePlaces d.c.Pg) (hPG : GlobalTheory.LocMod.PinGBy G cG) (hLev : LevX (F₀ u) d h0)
    (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (hBl : B.lev = d.B 0 D.R.rS h0) (hAd : B.Adapted (S.tr u).wt)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = d.t 0)
    (hs : s = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * d.bot.β)) ↔
      ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset))
    (hmem : ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, s * k * s⁻¹ ∈ rowJ S.X S.inst) :
    ∀ k ∈ levS (D.sp.Y 0) d.bot.β d.bot.L, rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hemb : ∀ b, embA B.d B.o b = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b : GA D (d.st 0).V) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (d.st 0).V) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (d.bes 0 D.R.rS h0).d : Subgroup (GA D (d.st 0).V)) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  have hps : psiBes d.c.ψ B.d 1 (vecB B.o B.ζ) =
      (psiBes d.c.ψ (d.bes 0 D.R.rS h0).d 1 (vecB (d.bes 0 D.R.rS h0).o (d.bes 0 D.R.rS h0).ζ) : GA D (d.st 0).V → ℂ) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => psiBes d.c.ψ L.d 1 (vecB L.o L.ζ)) hBl)
  refine GlobalTheory.T.level_group_property_closed_mul D u d τ G cG h0 hB hTP hPG
    (fun k : GA D (D.sp.Y 0) => rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k) ?_ ?_ ?_ ?_
  · intro (k : GA D (D.sp.Y 0)) hk (k' : GA D (D.sp.Y 0)) hk' q q'
    show rowChi S.X S.inst (s * (k * k') * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L (k * k')
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    have q₁ : rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k := q
    have q₂ : rowChi S.X S.inst (s * k' * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k' := q'
    rw [levChi_mul (D.sp.Y 0) d.bot.β d.bot.L hk hk', ← q₁, ← q₂, e, rowChi, rowChi, rowChi, map_mul, Prod.snd_mul,
      S.Y.hK.2.2.2.1 _ (hmem k hk).2 _ (hmem k' hk').2, star_mul']
  · intro PP (n : GA D (D.sp.Y 0)) q hn hq hl hk
    have h2 := GlobalTheory.T.level_zero_element_reduction D u d τ G cG h0 hB hTP hPG PP n q hq hl hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      rw [hs]; group
    have hj := hmem (t⁻¹ * n * t) (by rw [ht]; exact hk)
    rw [e] at hj
    have h1 := GlobalTheory.T.flag_support_split_places D S.X S.inst u d.c.ψ _ B hE PP.1 (G PP).q.e (G PP).q.split (G PP).idem (hTP.1 PP.1 PP.2) _
      (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn') (suppAt_conj _ _ _ _ hl.1) hj
    subst ht
    show rowChi S.X S.inst (s * ((show GA D (D.sp.Y 0) from d.t 0)⁻¹ * n * (show GA D (D.sp.Y 0) from d.t 0)) * s⁻¹) = _
    refine (congrArg _ e).trans (h1.trans (Eq.trans ?_ h2.symm))
    rw [GlobalTheory.CharLaws.psiBes_conj]
    exact congrFun hps n
  · intro b hb hk
    have h1 := (GlobalTheory.T.bessel_adapted_translate_level D u F₀ S d h0 hE hB hLev B hBl hAd a₀ hH0 b hb).2 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX S.X S.inst).symm (1, S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [hemb b] at e
    subst ht
    exact (congrArg _ e).trans h1
  · intro (k : GA D (D.sp.Y 0)) hk hr1
    obtain ⟨hr, ξ, hL⟩ := (hB.st 0 hm).lev
    have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
    show rowChi S.X S.inst (s * k * s⁻¹) = levChi (D.sp.Y 0) d.bot.β d.bot.L k
    rw [GlobalTheory.T.row_level_reduction_criterion D S.X S.inst hE d.c.Pg hTP hB.com.split _ hSt _ (hmem k hk) (fun PP hPP => by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.redFn_conj]; exact hr1 PP hPP), hLb]
    exact (levChi_of_red_one _ _ _ rfl rfl hr1).symm

theorem star_character_square_eq : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → IsTypePlaces d.c.Pg → GlobalTheory.FinPl.PinOff o → GlobalTheory.LocMod.PinGBy G o.cG → (∀ z, z ∈ (d.x 0).L ↔ z ∈ (F₀ u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β)) ↔ ((iotaX S.X S.inst κ).1 = 1 ∧ (iotaX S.X S.inst κ).2 ∈ S.X.B.I.Kset)) → ∀ (hr : D.R.r ≤ (D.sp.Y 0).rank) (κ : GA D (D.sp.Y 0)), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) → (iotaX S.X S.inst κ).2 ∈ S.X.K2 → ∀ hP : (fun PP : d.c.Pg => upperLeftBlock hr (redFn (finE (D.sp.Y 0) (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0)) * d.bot.β) PP.1 (finE (D.sp.Y 0) κ))) ∈ d.c.P.H, star (S.X.chi2 (iotaX S.X S.inst κ).2) = ((d.c.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
  intro D u F₀ S d k _ _ _ _ ι o G h0 hE hB hTP hPO hPG hLat hLev B hBl hAd a₀ hH0 a ha hac hSt hr κ hκ hκS _ hP
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr', ξ, hL⟩ := (hB.st 0 hm).lev
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := (hB.st 0 hm).rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hM := GlobalTheory.T.off_type_pinned_local_groups D u F₀ S d k ι o G h0 hE hB hTP hPO hPG hLat hLev B hBl hAd a₀ hH0 a ha hac hSt hr
  have hLb : d.bot.L = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := hL
  have key := rowChi_conj_of_mem u F₀ S d o.τ G o.cG h0 hE hB hTP hPG hLev B hBl hAd a₀ hH0 a hac _ _ rfl rfl hSt
  generalize ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0) = s at *
  have hfin : ∀ s k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) → s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := fun s k hk => by
    rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff S.X S.inst] at hk ⊢
    rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  rw [hLb] at key
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hP' : (fun PP : d.c.Pg => upperLeftBlock hr (redFn d.bot.β PP.1 (finE (D.sp.Y 0) k₀))) ∈ d.c.P.H := by
    simpa only [hfe, GlobalTheory.FrameConj.redFn_conj] using hP
  have hk₀ : k₀ ∈ levS (D.sp.Y 0) d.bot.β (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) := by
    refine ⟨?_, ?_⟩
    · have := hfin s⁻¹ _ hκ
      rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
    · show finE (D.sp.Y 0) k₀ ∈ lev _ _ _ _
      rw [mem_lev, mem_parLev]
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
      exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hκS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
        fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP'⟩
  have h1 := key (fun k hk => by
    obtain ⟨hf, hl⟩ := hk
    change finE (D.sp.Y 0) k ∈ lev _ _ _ _ at hl
    rw [mem_lev, mem_parLev] at hl
    have hf' := hfin s k hf
    have hs' : finE (D.sp.Y 0) (s * k * s⁻¹) ∈ St (finE (D.sp.Y 0) s * d.bot.β) := by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hl.1.2.1
    refine ⟨((hSt _).1 ⟨hf', hs'⟩).1, (hM _ hf' hs').2 ?_⟩
    simp only [hfe, GlobalTheory.FrameConj.redFn_conj]
    exact hl.2) k₀ hk₀
  refine h1.trans ?_
  have e0 : (⟨_, hP⟩ : d.c.P.H) = ⟨_, hP'⟩ := Subtype.ext (by simp only [hfe, GlobalTheory.FrameConj.redFn_conj])
  rw [e0]
  have hl2 : rTup d.bot.β (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B) (finE (D.sp.Y 0) k₀) ∈
      (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).P.H := hP'
  unfold levChi levFn
  rw [extendOne_of_mem _ hl2]
  have e1 : (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).s = 0 := rfl
  have e2 : (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).Q = ∅ := rfl
  simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

end GlobalTheory.ChrMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdB
section
noncomputable section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ChiZero

open GlobalTheory.Mem.Col2.MemChart

theorem redAt_eq_one_of_congAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n D : ℕ} (hD : 1 ≤ D)
    (P : Pl E) (w : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (h : GlobalTheory.TwU.CongAt P D w.1) : redAt 1 P w = 1 := by
  obtain ⟨_, y, rfl⟩ := w
  have e : redAt 1 P ⟨frGL 1 y, ⟨y, rfl⟩⟩ = bc (resS F P) y := by
    show bc (resS F P) (pullFr 1 ⟨frGL 1 y, ⟨y, rfl⟩⟩) = _
    rw [pullFr_frGL]
  rw [e]
  have e1 : frGL 1 y = intGL F E n y := by simp [frGL]
  apply Units.ext
  ext a b
  obtain ⟨s, hs, hm⟩ := h a b
  have hq : ((Formalism.L2.Col.qOf P : ℕ) : E) ≠ 0 := by
    have : Formalism.L2.Col.qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqm : Ideal.Quotient.mk P.asIdeal ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  have key : oToS F E s * ((y.1 - 1) a b) = oToS F E ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ^ D * ⟨_, hm⟩ := by
    apply Subtype.ext
    have c1 : ∀ r : 𝓞 E, ((oToS F E r : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E r) := fun _ => rfl
    have c2 : (((y.1 - 1) a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((frGL 1 y).1 - 1) a b := by
      rw [e1, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [Subring.coe_mul, Subring.coe_mul, SubmonoidClass.coe_pow, c1, c1, c2, ← map_pow, map_natCast]
    show _ = _ * (_ * (_ * _))
    rw [mul_left_comm, ← mul_assoc (iA F E (_ ^ D)), ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one, one_mul]
  have k2 := congrArg (resS F P) key
  rw [map_mul, map_mul, map_pow, resS_oToS, resS_oToS, hqm, zero_pow (by omega), zero_mul] at k2
  haveI := P.isPrime
  have k3 := (mul_eq_zero.1 k2).resolve_left (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at k3
  show resS F P (y.1 a b) = (1 : Matrix (Fin n) (Fin n) (kP P)) a b
  rw [k3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem dia_of_base (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} {g k : GA B n}
    (k1 : ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    {p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs Q} (h : PtOf (g * k) p) :
    g ∈ UAd B.sp.cm n ∧ (decoOf ((B.primes X).vT u) (B.primes X).vGs g).dia (diaT (Pr := B.primes X) u) = p.deco := by
  refine GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul _ _ B.sp.cm n _ _ Q g _ p _ h k1 k2 fun P r j hr => ?_
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
    have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
      (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact @Ne.isUnit (Res P.1) _ _ h0
  have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
      Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
    unfold diaT
    rw [dif_pos hu]
    rfl
  rw [e]
  exact k3 P r j hr

abbrev levelZeroSubgroupOfWord (u : B.Word) : Subgroup (GA B (B.R.N 0)) :=
  levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp

abbrev typ0 (u : B.Word) : levelZeroSubgroupOfWord I u →* ℂˣ :=
  levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)

set_option maxHeartbeats 1000000 in

theorem stepZeroChartLevel_mem_columnLevel_of_stdBase (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a 0).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a 0).Cl → GA B (B.R.N 0)} {st : ∀ c, (I.stp u a 0).Stab c → GL (Fin (B.R.N 0)) B.host.E}
    {k : Ch → GA B (B.R.N 0)} (hR : I.Reads u a 0 chOf Lb U chi y st k) (c : (I.stp u a 0).Cl)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) (k (chOf c)) = 1)
    (x : U (chOf c)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (hq : PtOf (y c * x.1 * k (chOf c)) q) :
    ∃ hx : x.1 ∈ levelZeroSubgroupOfWord I u, chi (chOf c) x = typ0 I u ⟨x.1, hx⟩ := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  obtain ⟨κ, h1, h2, -⟩ := (hR.lev c x.1 q hq).1 x.2
  subst h2
  have hg := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) (hR.pt c)
  have hx := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) hq
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)
  have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := hΛ c.1 ▸ κ.2.1.2
  have hxU : x.1 ∈ levelZeroSubgroupOfWord I u := (mem_levU _ _ _ _ _).2 ⟨hJ, by rw [hr]; exact inv_mem hm⟩
  refine ⟨hxU, Units.ext ((hR.chr c x κ h1 hq).trans (Eq.symm ?_))⟩
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩ = (⟨κ.2.1.1, hm⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((Chart0.lvG I a c.1).chr κ.2.1 * (Chart0.lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

theorem stepZeroColumnLevelType_eq_of_congruent_typePrimes (u : B.Word) (x x' : levelZeroSubgroupOfWord I u)
    (h : ∀ w ∈ (B.primes X).vGs, ∃ D, 1 ≤ D ∧ GlobalTheory.TwU.CongAt (F := B.host.F) (E := B.host.E) w D (x.1⁻¹ * x'.1)) :
    typ0 I u x = typ0 I u x' := by
  have e : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x') = 1 := by
    apply Subtype.ext
    funext w
    obtain ⟨D, hD, hc⟩ := h w.1 w.2
    exact redAt_eq_one_of_congAt hD w.1 ⟨(x⁻¹ * x').1, congruence_subgroup_le_stabilizer _ _ _ (unipotentLevel_le_mirabolicLevel _ _ _ _ _ (x⁻¹ * x').2)⟩ hc
  have e2 : typ0 I u (x⁻¹ * x') = 1 := by
    show (((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x')))⁻¹ = 1
    rw [e, map_one, inv_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at e2
  exact e2

end GlobalTheory.Fam.ChiZero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam
open GlobalTheory.Fam.ChiZero GlobalTheory.Mem.Col2.MemChart

set_option maxHeartbeats 4000000 in

theorem chi_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x x' hxx
  have hPr := l.pr
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨n, hn, hfin⟩ := hA.fin 0 (Nat.zero_le _) (A.chOf 0 c)
  obtain ⟨x₁, e₁, ⟨q, hq⟩, hcg⟩ := GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt I hI hP l Z u a 0 (Nat.zero_le _) (A.bad 0) (Ch 0) (A.chOf 0)
    (A.K 0 (Nat.zero_le _)) (A.kb 0) hR c ⟨n, hn, fun κ _ => hfin κ⟩ x
  obtain ⟨hx₁, f₁⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u a hR c (fun w hw => by
    rw [hβ]
    exact (kStd_spec hPr u _).2.1 _ fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩) x₁ q hq
  obtain ⟨k, hR'⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c', -⟩ := hR'.onto ()
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  let yc : TC.GA B (B.R.N 0) := (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').1
  let xg : TC.GA B (B.R.N 0) := x'.1
  have hxg : xg ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).to0.cls0.lev.U_eq x'.1).1 x'.2).1
  have hyc : yc ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').2
  obtain ⟨p0, hp0, -⟩ := hR'.k_std ()
  have hk : k () ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.uni
  obtain ⟨q', hq'⟩ : ∃ q' : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0, TC.PtOf (yc * xg * k ()) q' :=
    GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem B.sp.cm I.twistPrimes_reference_tuple_eq_empty (mul_mem (mul_mem hyc hxg) hk)
  obtain ⟨hx', f'⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u I.mu0 hR' c' (fun w hw =>
    hR'.k_off () _ (fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩)
      (fun ⟨P, hP, _⟩ => by rw [I.twistPrimes_reference_tuple_eq_empty] at hP; exact Finset.notMem_empty _ hP) (Or.inl rfl)) x' q' hq'
  refine e₁.symm.trans (f₁.trans (Eq.trans (Eq.symm ?_) f'.symm))
  refine stepZeroColumnLevelType_eq_of_congruent_typePrimes I u _ _ fun w hw => ?_
  have hw' : w ∈ GlobalTheory.Mem.Col2.AdT.SBof I a := Finset.mem_union_left _ hw
  refine ⟨(I.cst a).D ⟨w, hw'⟩, (hI.idx_ok a).cst_ok.D_pos _, ?_⟩
  have h1 := hcg ⟨w, hw'⟩
  rw [(GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a (B.R.N 0) 0 ⟨w, hw'⟩ x.1).1, hxx] at h1
  exact h1

end GlobalTheory.Fam
end

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodingeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' (PP.under (𝓞 D.host.F))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  first | exact @GlobalTheory.PlaceModelComb.main | exact GlobalTheory.PlaceModelComb.main | (intros; apply GlobalTheory.PlaceModelComb.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.SymChain.SymData.RowLam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sum_sum_lt {ι κ' : Type} [Fintype ι] [Fintype κ'] (f : ι → κ' → k)
    (hf : ∀ i j, valuation k (f i j) < 1) : valuation k (∑ i, ∑ j, f i j) < 1 := by
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hf i j)

theorem psi_inv_mul_eq_one (ψ : AddChar k Circle) (ϖ : kˣ) (hψ : GlobalTheory.SplitWeil.HasConductor ψ 1)
    (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {t : k} (ht : valuation k t < 1) :
    ψ (((ϖ⁻¹ : kˣ) : k) * t) = 1 := by
  have h1 := (hψ 1).2 (by simp)
  apply h1
  have hle : valuation k t ≤ valuation k (ϖ : k) := (hϖ t).1 ht
  rw [map_mul, map_one]
  calc valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k t
      ≤ valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k (ϖ : k) := by gcongr
    _ = 1 := by rw [← map_mul]; simp

end GlobalTheory.SymChain.SymData.RowLam

open GlobalTheory.SymChain.SymData.RowLam in
theorem GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  intro k _ _ _ _ s κ S x M hM hsup
  have hS := S.sym.2 x
  have hsimple : valuation k (GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k)) < 1 := by
    unfold GlobalTheory.RootEx.simpleSum
    apply val_sum_sum_lt
    intro i j
    split_ifs with h
    · exact hsup i j h
    · simp
  have hdiff : valuation k (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ -
      ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) < 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply val_sum_sum_lt
    intro a b
    split_ifs with h
    · simpa [Matrix.toBlocks₁₁] using hM a b
    · simp
  have e1 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hsimple
  have e2 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hdiff
  have e3 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁) =
      S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) := by
    rw [mul_sub, AddChar.map_sub_eq_div] at e2
    exact div_eq_one.mp e2
  rw [hS, e1, e3]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDownStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  first | exact @GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | exact GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | (intros; apply GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardMultiplicityCuspidalRealTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  first | exact @GlobalTheory.Corev.LiftUp.liftUp_mult | exact GlobalTheory.Corev.LiftUp.liftUp_mult | (intros; apply GlobalTheory.Corev.LiftUp.liftUp_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threeOrbits_gluedCore_atPlace : ∀ D : D7, GlobalTheory.FinPl.OrbitGlued D := by
  first | exact @GlobalTheory.FinPl.orbitGlued | exact GlobalTheory.FinPl.orbitGlued | (intros; apply GlobalTheory.FinPl.orbitGlued <;> assumption)
end

