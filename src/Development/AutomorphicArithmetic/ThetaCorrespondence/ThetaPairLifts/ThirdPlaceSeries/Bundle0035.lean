import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0304
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0308
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Formalism.LocalToGlobal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0309
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerMore
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.IsoComp
open GlobalTheory.CompRed
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  intro hL D P i x f' hf' hf0 sp c hc
  classical
  have hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV =>
      (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite := by
    intro ϖ hϖ k
    obtain ⟨N, hN, hNJ⟩ := (P.M.loc i).J_open
    exact GlobalTheory.T.finite_image_heckeSet_split_place_cosets D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ
  unfold eigC at hf'
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hf'
  obtain ⟨g, hgmem, hgsum⟩ := hf'
  have hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q := by
    intro Q hQ
    by_cases h : D.naut.ptV i Q = some x
    · refine ⟨h, ?_⟩
      have := hgmem Q
      rwa [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)] at this
    · exfalso
      have := hgmem Q
      rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot] at this
      exact hQ this
  obtain ⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]
  set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef
  have hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q := by
    rw [← hgsum, Finsupp.sum, map_sum]
  have hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro Q hQ
    have hy := (hg' Q (Finsupp.mem_support_iff.1 hQ)).2
    rw [P.H.av.typeV] at hy
    exact hy
  have hind := isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)
  have hQ0s : Q0 ∈ g.support := Finsupp.mem_support_iff.2 hQ0
  refine ⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩
  · rw [← (P.M.loc i).real_range]
    exact ⟨g Q0, rfl⟩
  · intro h
    exact hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
  · intro ϖ hϖ k hk
    set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k
    set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
      fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef
    have htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun Q hQ =>
      Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ))
        (Submodule.smul_mem _ _ (hGiso Q hQ))
    have htsum : ∑ Q ∈ g.support, t Q = 0 := by
      simp only [t]
      rw [Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk,
        sub_self]
    have hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]
    have hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j) := by
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)
      obtain ⟨hne, hQs⟩ := Finset.mem_erase.1 hQ
      exact (le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne)
        (htmem Q hQs)
    have h0 : t Q0 = 0 := Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2
    exact sub_eq_zero.1 h0
end GlobalTheory.IsoComp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
structure RowsAAlt (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  g4p : _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
def SummandsSuffice (D : D7) : Prop :=
  _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D → SumRepresentations.tieLab D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, LamPos D (D.nd.mu i) (D.nd.j i)) →
    ThetaOne D → _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
structure LinkedData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 where
  P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X
structure LinkedDataNamed {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (T : _root_.GlobalTheory.NRows.LinkedData hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t
structure LinkedInputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Type 1 extends toRowSideFamily : _root_.GlobalTheory.NRows.LinkedData hL D where
  named : _root_.GlobalTheory.NRows.LinkedDataNamed toRowSideFamily
structure PointConditions' (D : D7) : Prop where
  a : _root_.GlobalTheory.NRows.RowsAAlt D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L
namespace Inputs
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (I : _root_.GlobalTheory.NRows.LinkedInputs hL D)
include I
theorem _root_.GlobalTheory.NRows.LinkedInputs.hypO : SumRepresentations.hypO D := I.named.hypO
theorem _root_.GlobalTheory.NRows.LinkedInputs.c1 : GlobalDatumCompatibility D := I.named.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.bc : SphericalInertData.Conclusion1 D := I.named.bc
theorem _root_.GlobalTheory.NRows.LinkedInputs.lam : LamUsed D := I.named.lam
theorem _root_.GlobalTheory.NRows.LinkedInputs.isot : SumRepresentations.adm8 D := I.named.isot
theorem _root_.GlobalTheory.NRows.LinkedInputs.ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser
theorem _root_.GlobalTheory.NRows.LinkedInputs.typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ
theorem _root_.GlobalTheory.NRows.LinkedInputs.e0loc : GoodIdempotentFixesLocalisationForms D := goodIdempotentFixes_of_onlySeriesOfLabelActs I.ser
set_option linter.unusedSectionVars false in
theorem _root_.GlobalTheory.NRows.LinkedInputs.mtPar : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie
theorem _root_.GlobalTheory.NRows.LinkedInputs.adm1 : SumRepresentations.adm1 D := base_change_automorphic_of D I.bc I.c1
theorem _root_.GlobalTheory.NRows.LinkedInputs.admAt (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D :=
  ⟨⟨a.tie0, I.hypO, I.adm1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩
theorem _root_.GlobalTheory.NRows.LinkedInputs.Conclusion1 (h : _root_.GlobalTheory.NRows.SummandsSuffice D) (a : _root_.GlobalTheory.NRows.RowsAAlt D) (b : RowsB D) : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D :=
  h (I.admAt a b) a.tieLab b.rowSize a.hecke I.lam.loc b.thetaOne a.g4p
end Inputs
end GlobalTheory.NRows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRtEqOfGoodInert
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj h hh Pp hG hI v hv g κ hκ hT
  have hstd := hX.stdV j
  have hprime := GlobalTheory.InertFrameLoc.isPrimeIdem_tensAt hI rfl
  have hsupp := GlobalTheory.InertFormFix.suppF_of_trivOutside D hX.hF (Formalism.IndefR.Links.Vc D j) D.R.nV (hX.PV j) hstd Pp _ _ hprime v hv κ hT
  obtain ⟨c, hc⟩ := X.given.core.lev.βV j
  rw [one_pow] at hc
  have ls := (GlobalTheory.LevSplit.lev_split (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.ΛV j) 1
    (Formalism.IndefR.RecTie.datVP X.R j (X.tupT (D.nd.mu i)) (X.R.levR X.F false)) hc).2 Pp _ _ hprime
    (by
      intro h1
      have : ((1 : ℕ) : 𝓞 D.host.E) = 1 := Nat.cast_one
      rw [this] at h1
      exact Pp.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP hPP)
  have hK : (hX.PV j).ψ κ ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ := (hstd.2 κ).1 hκ
  have hlev := (ls.1 _ hsupp).2 hK
  have hchi := ls.2.1 _ hlev hsupp
  have hfix : ∀ (x : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) y,
      X.fn hμ j x (y * (hX.PV j).ψ κ) = X.fn hμ j x y := by
    intro x y
    have hm := ((X.IL.jMt (D.nd.mu i) hμ j) x).2
    obtain ⟨-, hm2⟩ := hm
    have e1 := hm2 ((hX.PV j).ψ κ) hlev y
    unfold GlobalTheory.NJoin.RealAt.fn
    rw [e1]
    rw [hchi]
    exact one_smul ℂ _
  have key : ∀ (j' : ℕ) (e : j.1 + 1 = j') (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m) (x : D.what₂.Mt (D.nd.mu i) j'),
      NG.rt D.host.E D.R.nV κ ((P.M (D.nd.mu i) j' h1 h2).real x) = (P.M (D.nd.mu i) j' h1 h2).real x := by
    intro j' e h1 h2 x
    subst e
    funext y
    show (P.M _ _ h1 h2).real x (y * κ) = _
    rw [hX.real (D.nd.mu i) hμ j x (y * κ), hX.real (D.nd.mu i) hμ j x y, ← mul_assoc, map_mul, hfix]
  exact key _ hj _ _ g
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting
namespace Formalism.L2.SG.SpectralTiesReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
structure STiesRAlt (R : _root_.Formalism.L2.RecTAlt ex) extends STies D where
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u ((R.T.cols.forms u).to0)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (hF : FinX Y) (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : Formalism.L2.SG.RowDict.GoodOp X
  rowTie : ∀ hF : FinX Y, Formalism.L2.SG.RowDict.RowDictTie X G (hI hF).eHH
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D
end Formalism.L2.SG.SpectralTiesReal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSidePq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2
namespace SelJ
variable {D : D7} {X : Col.Fields}
end SelJ
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def SelInAlt (R : _root_.Formalism.L2.RecTAlt ex) (Side : Set (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  ∀ μ, ∀ P ∈ Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K),
    ∀ P', SelJ.Carried R.T.ker.seam P P' → P' ∈ Side
def SelectedSideOfPrimeAbove (R : _root_.Formalism.L2.RecTAlt ex)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  (∀ v, NG.OverPl (Pq v) v) ∧ _root_.Formalism.L2.SelInAlt R (Set.range Pq)
end
end Formalism.L2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInert
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.NJoin.sysParam_at_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  intro _ _ D P X _ _ _ _ i hμ j hj x _ f _ y _ h0 h hh s hs w hw _
  obtain ⟨B, hB⟩ := GlobalTheory.DownLift.Params.paramsV X.R X.given.core j (X.tupT (D.nd.mu i)) h hh s y hs h0
  exact ⟨B w, hB _ (by simpa using hw) w rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamSplit
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStr
theorem sysParam_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  intro _ hL D P X _ _ _ _ i hμ j hj x _ f _ y _ hy0 h hh s hy w hw _
  obtain ⟨B, hB⟩ := GlobalTheory.DownLift.Params.paramsV X.R X.given.core j (X.tupT (D.nd.mu i)) h hh s y hy hy0
  exact ⟨B w, hB _ hw w rfl⟩
end GlobalTheory.EigStr
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeNZJoin
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
theorem typeNZRec_of_join_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact of_cast hj _ fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0
end GlobalTheory.TypeNZJoin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValInert
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ValInert
theorem val_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  intro _ hL D P X _ _ _ _ i hμ j hj w hG hI c hc
  have hcw := conjSelf D w hI
  have hLv : X.R.toLevCh.Is X.A.μ0 := X.recR.base.lev
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG
  have hm0 : (X.R.C.mu0 j).UnrAt w := (X.R.C.isMu0 j).unr w fun k hk => hg (by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk')
  have hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra h
    rcases (hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr h)).2 hc
  have hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]
  have hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) := by
    rw [P.chr.muC i j hj, hxi, X.cfEq]
    rfl
  have hu : D.naut.unr (D.naut.locG (D.naut.muC i) w) := (P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))
  have haa : a = a⁻¹ := by
    have e := (D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2
    rw [ha, Multiset.map_singleton] at e
    exact Multiset.singleton_inj.1 e
  have hns := notSplit D w hcw
  have heu := (D.naut.etaTinv_def w).1
  have hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]
  have hc1 : c = a * (-1 : ℂ)⁻¹ := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton] at hc
    exact (Multiset.singleton_inj.1 hc).symm
  have hcc : c = c⁻¹ := by
    have h1 : (-1 : ℂ)⁻¹ = -1 := by norm_num
    rw [hc1, mul_inv, inv_inv, ← haa, h1]
  have hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 =
      X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]
  have hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w :=
    (P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)
  have hc2 := P.chr.frob _ w hut
  rw [hc] at hc2
  have hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹ := by
    rw [Multiset.singleton_inj.1 hc2, hte]
    simp
  have hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w =
      (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ := by
    rw [← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w,
      ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]
    first
      | rfl
      | (simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)
      | (unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)
  rw [hv, hcc, hc3, inv_inv]
end GlobalTheory.ValInert
end
end

