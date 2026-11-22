import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0215
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0214
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0137
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0218
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0199
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0192
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0202
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.DzGoodVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0216
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0217
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0801
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSide
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem locOf_eq_alt {π : NG.AutRep D.host.E D.R.nV} {w : PlE D.host} {x} (hx : LocAt π w x) :
    _root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w = (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x) := by
  have hex : ∃ x, LocAt (clsA π).rep w x := by
    obtain ⟨s, σ, hs, -, -⟩ := hx
    subst hs
    exact locAt_of_split _ s
  unfold _root_.GlobalTheory.AutQuot.locOf_alt
  rw [dif_pos hex, locAt_unique (rep_iso π) hex.choose_spec hx]
end
end GlobalTheory.AutQuot
namespace GlobalTheory.AutQuot
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
theorem f_sph_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : NG.OverPl w v) : (∃ v', NG.OverPl w v' ∧ (clsA π).rep.SphericalAtPlace v') ↔ π.SphericalAtPlace v := by
  constructor
  · rintro ⟨v', hv', hs⟩
    rw [overPl_unique hv hv']
    exact _root_.UpperTheory.One.M.New.sphAt_iso (rep_iso π) hs
  · intro hs
    exact ⟨v, hv, _root_.UpperTheory.One.M.New.sphAt_iso (autIso_symm (rep_iso π)) hs⟩
theorem unr_locOf_of_sphAt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (hs : π.SphericalAtPlace s.v) :
    D.naut.unr (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) := by
  obtain ⟨x, hx⟩ := locAt_of_split π s
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx, T.unr, Equiv.apply_symm_apply]
  exact _root_.GlobalTheory.T.locRecT_unr_of_sphAt hL D π s x hx hs
theorem f_locPol_alt (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ)
    (J : Subgroup (GAf D.host.E D.R.nV)) (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV))
    (f : GAf D.host.E D.R.nV → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) (c : ℕ → ℂ)
    (hc' : ∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) :
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep w) ((1 - (D.R.nV : ℝ)) / 2)) := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_localComponent_conj_splitPlace D π s w hc
  obtain ⟨hun, hpol⟩ := _root_.GlobalTheory.T.spherical_vector_fixed_local_alt hL D π s w ϖ hc hu J hJ f hf hf0 hfix c hc' x hx
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T hx]
  have hu2 : D.naut.unr (D.naut.lpTw ((T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) x))
      ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [T.unr, T.tw, Equiv.apply_symm_apply]; exact hun
  unfold galPol
  rw [T.frobEig _ _ hu2, T.tw, Equiv.apply_symm_apply]
  exact hpol
theorem e_locOf_eq_locRecT_of_isLocS (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS π.S s σ) :
    T.e s.w (_root_.GlobalTheory.AutQuot.locOf_alt hL D T (clsA π).rep s.w) =
      _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 s.w) (GlobalTheory.LocLanglands.cls σ) := by
  rw [_root_.GlobalTheory.AutQuot.locOf_eq_alt hL D T ⟨s, σ, rfl, hσ, HEq.rfl⟩, Equiv.apply_symm_apply]
set_option maxHeartbeats 1000000 in
theorem exists_nbc_auSide_true_of_empty (hE : IsEmpty D.nd.Loc) :
    ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  ⟨{ _root_.GlobalTheory.AutQuot.boundaryConditionOfNoLocal hL D T hE with
      sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ (AUq.rep X).SphericalAtPlace v
      embAV_sph := fun i => isEmptyElim i },
    { cls := fun _ _ _ π => clsA π
      surj := fun _ _ _ X => ⟨X.rep, AUq.cls_rep X⟩
      iso := fun _ _ _ π π' => clsA_eq_iff π π'
      mult := fun _ _ _ π => GlobalTheory.T.automorphic_multiplicity_eq_of_iso _ _ _ _ (rep_iso π)
      sph := fun _ _ _ π w v _ hv => _root_.GlobalTheory.AutQuot.f_sph_alt D π w v hv
      sat := fun _ _ _ π v w hv Dv hα => f_sat D π v w hv Dv hα
      clsWt := fun _ _ _ a => clsW a
      surjWt := fun _ _ _ Y => ⟨Y.rep, WtQ.cls_rep Y⟩
      isoWt := fun _ _ _ a b => clsW_eq_iff a b
      wt := fun _ _ _ π a hd => f_wt D π a hd
      infW := fun _ _ _ a τ lam hl => f_infW D a τ lam hl
      locUnr := fun _ _ _ π s hs => _root_.GlobalTheory.AutQuot.unr_locOf_of_sphAt hL D T π s hs
      locPol := fun _ _ _ π s w ϖ hc hu J hJ f hf hf0 hfix c hc' => _root_.GlobalTheory.AutQuot.f_locPol_alt hL D T π s w ϖ hc hu J hJ f hf hf0 hfix c hc' },
    fun _ _ _ π s σ hσ => _root_.GlobalTheory.AutQuot.e_locOf_eq_locRecT_of_isLocS hL D T π s σ hσ⟩
end
end GlobalTheory.AutQuot
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem GlobalTheory.AutQuot.exists_nbc_auSide_auTrue_of_isEmpty : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), IsEmpty D.nd.Loc →
    ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt (setBC D C)), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (setBC D C) T A :=
  fun hL D hE T => _root_.GlobalTheory.AutQuot.exists_nbc_auSide_true_of_empty hL D T hE
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRow
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
variable {D : D7} (m : Mv D)
theorem Mv.rowLoc_alt {D : D7} (m : Mv D) {C : NChoice D} (a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : _root_.Formalism.L2.RowLocTiedAlt D a.gal.lp F) : _root_.Formalism.L2.RowLocTiedAlt m.D ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = kc% rep := eq_of_heq (kc% hF)
  subst e
  exact (@_root_.Formalism.L2.RowLocTiedAlt.mk (_) (_) (_)
    (sat := kc% x.sat)
    )
theorem exists_nonempty_nMore_upL (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z))
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0')
    (hs : RowsSame t t') (hg : HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo))
    (hj : ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1)
    (hser : ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq'))
    {tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch} {tp' : TupTied (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch)}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch tp)
    (a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch) tp') (hA : _root_.GlobalTheory.LayerMove.AtSameAltAlt (mvOf w Z S' N h) a a')
    (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y) (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) r t.r.z.geo xd) :
    ∃ r' : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st (upL Z S' N h)).toD7) a' t'.r.z.R t'.r.z.F t'.r.z.cG t'.r.Y,
      Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st (upL Z S' N h)).toD7) r' t'.r.z.geo (xdUp S' N h xd)) := by
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = kc% (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) := eq_of_heq (kc% hg)
  subst e7
  obtain ⟨nt', all', chr_eq', host', frameN', chrN', chrGal', Pq', Pq_over', pq', jE_eq', mt_eq', Pq_eq', hlow', split', ratIn',
    r1', r2', r3', depth'⟩ := a'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hA
  have e8 : all' = kc% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all) := eq_of_heq (kc% s1)
  have e9 : Pq' = kc% a.Pq := eq_of_heq (kc% s2)
  subst e8 e9
  obtain ⟨kKs, hk, nexp, hecke, grp, rowLoc, S_eq, hL_eq, rep_eq⟩ := r
  obtain ⟨ad, fi, hrow, cHk, eig, ser, tau, geo, ok, th, xda, large, labc, zeta, pht⟩ := e
  obtain ⟨geo⟩ := geo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, IL', _, _, _, eFT', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨eW', _⟩, _⟩ := Y'
  have e10 : eW' = kc% t.r.Y.mj.eW := eq_of_heq (kc% hs.eW)
  subst e10
  obtain ⟨Sb, ev, hSb, hev, hE⟩ := eig
  obtain ⟨i1, i2, i3⟩ := s7 ⟨labc, zeta, pht⟩
  obtain ⟨l1, l2, l3, l4, l5, lv⟩ := grp.lvl
  refine Nonempty.elim (hser kKs hk nexp (kc% kKs) (kc% hk) (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := kc% nexp.fi)
    (geq := kc% nexp.geq)
    (rho := kc% nexp.rho)
    (chi := kc% nexp.chi)
    (eF := kc% nexp.eF)
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (kc% (HEq.refl kKs)) (kc% (HEq.refl nexp.fi)) (kc% (HEq.refl nexp.eF)) a.all (kc% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)
    (kc% (HEq.refl ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)) ad.PV (@fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).ψ)
      (inj := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).inj)
      (into := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).into)
      (onto := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).onto))
    (kc% (HEq.refl fun i => (ad.PV i).ψ)) a.Pq (kc% a.Pq) (kc% (HEq.refl a.Pq)) ser) fun ser' => ?_
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NormRealisationData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (kc% kKs) (kc% hk)
    (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := kc% nexp.fi)
    (geq := kc% nexp.geq)
    (rho := kc% nexp.rho)
    (chi := kc% nexp.chi)
    (eF := kc% nexp.eF)
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (@_root_.Formalism.IndefR.NX.NExpRealH.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (hL := kc% hecke.hL)
    (hs := kc% hecke.hs)
    (cHk := kc% hecke.cHk)
    (cHk_zero := kc% hecke.cHk_zero)
    (cHk_unit := kc% hecke.cHk_unit)
    (cHk_pow := kc% hecke.cHk_pow)
    (hkEq := kc% hecke.hkEq)
    )
    (@_root_.Formalism.L2.DIV.GrpTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (card := kc% grp.card)
    (e0 := kc% grp.e0)
    (lvl0 := kc% grp.lvl0)
    (psi0 := kc% grp.psi0)
    (idxSharp := kc% grp.idxSharp)
    (lvl := ⟨kc% l1, kc% l2, kc% l3, kc% l4, kc% l5,
      ⟨kc% lv.place, kc% lv.comp, kc% lv.gen, kc% lv.p0, kc% lv.chi0, kc% lv.ps, kc% lv.chis⟩⟩)
    )
    (kc% ((mvOf w Z S' N h).rowLoc_alt a.all _ (kc% (Formalism.L2.Col.rowFrameOf (w.D (upL Z S' N h)) _ eFT')) (kc% hs.rep) rowLoc))
    (kc% (s3.trans S_eq)) (kc% (s4.trans hL_eq)) (kc% ((s5.trans rep_eq).trans hs.rep.symm)), ⟨@_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (@_root_.GlobalTheory.HeightCounting.MtAd.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (PV := @fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).ψ)
      (inj := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).inj)
      (into := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).into)
      (onto := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).onto))
    (std := kc% ad.std)
    (eW := kc% ad.eW)
    (read := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => kc% ((ad.read (kc% x1) (kc% x2) (kc% x3) (kc% x4) (kc% x5)).trans
      (congrFun_heq (g := (t.r.Y.IL.jMt (kc% x1) (kc% x2) (kc% x3) (kc% x4)).1) (f := kc% (IL'.jMt x1 x2 x3 x4).1)
        (kc% (hj (kc% x1) (kc% x2) (kc% x2) (kc% x3) (kc% x4))) _).symm))
    (rat := kc% ad.rat)
    (wt := kc% ad.wt)
    (id := kc% ad.id)
    )
    (kc% fi)
    (@Formalism.IndefR.NX.NExpHeckeRowX.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (kc% hrow.tie))
    (kc% cHk)
    ⟨kc% Sb, kc% ev, kc% hSb, kc% (s6.trans hev), fun i σ k P α Rr hd => kc% (hE (kc% i) (kc% σ) k (kc% P) (kc% α) (kc% Rr)
      ⟨kc% (@HkDat.split (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.offS (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.odd (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.le (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.elt (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.reps (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd)⟩)⟩
    (kc% ser'
    )
    (kc% ((mvOf w Z S' N h).tauTrue_alt tau))
    ⟨@_root_.GlobalTheory.GeoTie.ThetaTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (side := @fun x1 => @fun x2 => @fun x3 => @_root_.GlobalTheory.GeoTie.SideTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
      (pt := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).pt)
      (cover := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).cover)
      (ev_eq := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).ev_eq)
      (fmUr := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).fmUr)
      (hk := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk)
      (hk_none := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk_none))
    (isUnramified₂ := kc% geo.isUnramified₂)
    ⟩
    (kc% ok) (kc% th) (kc% xda) (kc% ((mvOf w Z S' N h).large large)) (kc% i1) (kc% i2) (kc% i3)⟩⟩
end GlobalTheory.LayerMove
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem exists_true_reading_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    ∃ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S ∧ _root_.GlobalTheory.SplitRead.LawsAlt S ∧ SuppLaws S := by
  intro hAF hL D P hR
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have hex : ∀ w : PlE D.host, IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
    intro w hw
    obtain ⟨w', hw'⟩ := GlobalTheory.ToricFactor.exists_isConjPl w
    obtain ⟨s, -, hs, -⟩ :=
      GlobalTheory.SplitConjPlace.splitEx_all D w' (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hw hw')
    exact ⟨s, GlobalTheory.ToricFactor.isConjPl_unique hs (GlobalTheory.ToricFactor.isConjPl_symm hw')⟩
  have key : ∀ i (w : PlE D.host), IsSplitPl D.host w → ∃ X : ReadAt P.T i w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w ∧
      ∀ (s : SplitPlace D.host.E), s.w = w → ∀ Y : ReadAt P.T i s.w, HEq Y X →
        (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (Y.row σ).toIrrRep) ∧
        (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (Y.rep Q).toIrrRep) ∧
        (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w Y.mu) ∧
        IsComp P.cf.eta s.w Y.eta := by
    intro i w hw
    obtain ⟨s₀, rfl⟩ := hex w hw
    obtain ⟨X, h1, h2⟩ := _root_.GlobalTheory.TrueReading.readAt_exists_m_alt hAF hL D P hR i s₀
    refine ⟨X, h1, fun s hs Y hY => ?_⟩
    obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq D.host.E s s₀ hs
    obtain rfl := eq_of_heq hY
    exact h2
  choose S hS using key
  refine ⟨S, ⟨fun i w hw => (hS i w hw).1, fun i s hw σ hσ => ((hS i s.w hw).2 s rfl _ HEq.rfl).1 σ hσ,
    fun i s hw Q => ((hS i s.w hw).2 s rfl _ HEq.rfl).2.1 Q,
    fun i w hw j hj => ?_, fun i w hw => ?_⟩, fun i w hw => ?_, fun i w hw => ?_⟩
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.1 j hj
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.2
  · rw [(hS i w hw).1]
    exact (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)).recLaws
  · rw [(hS i w hw).1]
    exact _root_.UpperTheory.Zero.LLC.IsRecT.recSupp (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
end GlobalTheory.TrueReading
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllOfLocal
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
theorem goodFTAll_of_local_alt : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ k v, DiscreteGroups.sglob.DzType.Rt.TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hL D T Rw rep L hRow hDep hLT hDZ hTP hVec σ
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := _root_.GlobalTheory.T.exists_isRc_classMap_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := _root_.GlobalTheory.T.exists_comp_irrSm_locR_eq_rc hL D T I rc hrc Rw rep hRow hDep
  have hP : DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc :=
    DiscreteGroups.sglob.DzType.Rt.labParamLe_of D L rc hG (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D T I rc hrc) hDZ (hTP I rc hrc)
  have hSC := GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree hG D L hLT
  obtain ⟨V, _, _, ρ, W, x, hconj, hx0, hxW, hxe⟩ := hVec I cp hcomp σ
  exact _root_.DiscreteGroups.sglob.DzType.Rt.good_of_vector_row_m D Rw L rc cp hLT hP hcls hSC hcp V ρ W σ hconj x hx0 hxW hxe
end DiscreteGroups.sglob.DzType.Rt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisBis
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.InertialTypes
theorem main_alt_alt : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine _root_.GlobalTheory.TameType.inertialType_of_tame_m_alt _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact _root_.UpperTheory.One.M.split_param_of_typeBlock _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm
end GlobalTheory.InertialTypes
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem isobaricRigid_of_pin_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.JacquetShalika →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), IsobaricRigid D.nd D.naut := by
  intro hF hJ hL D P
  have := GlobalTheory.CuspRep.host_isCMField D.host
  exact GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ.1 (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF P.cg)
end GlobalTheory.NPin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftOfMovedTwistStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_package_twist_heq_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt | exact _root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.LiTw.li_copy_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepOfReadingLaws
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repOfLoc_of_isTrue_laws : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.repOfLocal_h_alt | exact _root_.UpperTheory.One.M.repOfLocal_h_alt | (intros; apply _root_.UpperTheory.One.M.repOfLocal_h_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ConjPlaceDual
end GlobalTheory.ConjPlaceDual
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDual_of_labAll : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ConjDual D := by
  first | exact @_root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt | exact _root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.ConjPlaceDual.depthZero_tame_alt <;> assumption)
end
end
end

