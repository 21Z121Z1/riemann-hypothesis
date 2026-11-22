import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0711

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelSideW

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]

open Classical in

theorem qe_image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {S S' : Set ℕ} (hS : S = S') {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)} (hsel : HEq sel sel')
    {tup : D.what₂.Tup → Formalism.L2.DIV.Tup X.F X.E X.K S} {tup' : D.what₂.Tup → Formalism.L2.DIV.Tup X'.F X'.E X'.K S'} (htup : HEq tup tup')
    (μ : D.what₂.Tup) :
    (Col.QE sel (tup μ : DIV.Chr X.F X.E X.K)).image (Host.CT.plMap s.iE) =
      (Col.QE sel' (tup' μ : DIV.Chr X'.F X'.E X'.K)).image (Host.CT.plMap s'.iE) := by
  subst hX
  subst hS
  cases hs
  cases hsel
  cases htup
  rfl

open Classical in

theorem qe_image_std {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    {L : SizeData₂ (w.D Z)} {hT : GatTies (w.D Z)} {Gi : Formalism.MainNotions.G.Inst (w.D Z) L} {Gl : Formalism.MainNotions.G.LatInst (w.D Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.D Z)} {cX : ExtraC} {ex : Extra (w.D Z) L hT Gi Gl Kc Yd cX}
    (t : Formalism.L2.Ker.KerEntTied ex) (h : TC.StdKer w.I w.l Z t) (μ : (w.D Z).what₂.Tup) :
    (Col.QE t.sel (t.tup μ : DIV.Chr t.X.F t.X.E t.X.K)).image (Host.CT.plMap t.seam.iE) = w.I.Q μ := by
  rw [qe_image_congr h.X_eq h.seam h.S h.sel h.tup μ]
  exact image_refl _ rfl _

end GlobalTheory.Mem.R3.SelSideW

namespace GlobalTheory.Mem.R3.SelSideW

theorem de_pin {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core.a.Pq v).asIdeal) :
    (q.core.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK := by
  have hm : q.core.a.Pq v ∈ Set.range q.w.I.sel := q.core.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.1 v' hv] at this
  rw [← hv']
  exact this

theorem de_pin' {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde' : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core.a.Pq v).asIdeal) :
    (q.core.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK' := by
  have hm : q.core.a.Pq v ∈ Set.range q.w.I.sel := q.core.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde' v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P'_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.2 v' hv] at this
  rw [← hv']
  exact this

open Classical in
set_option maxHeartbeats 4000000 in

theorem selected_side_realization : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : RealIn x R (sS.toSTiesR R)) (r : RecIn y) (HD : Formalism.L2.HostDatumC R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → Formalism.L2.SelSideRT R (divisionPairOfAdelicFormsFaceColumnsData x) (realTOf y) (realRecOf r) HD q.core.a.Pq := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x ax y r HD hHD
  have hQ := qe_image_std q.w q.Z R.T.ker hR.k.std
  have hsel : Set.range q.core.a.Pq = Set.range q.w.I.sel := q.core.sel
  have hlev0 := (twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a).2.2.1
  have hlev : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x.R.Q (x.Y.tupT μ)) (q.w.I.Q μ) := by
    have key : ∀ x' : TwIn q.O.ex, a.x = x' →
        ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x'.R.Q (x'.Y.tupT μ)) (q.w.I.Q μ) := by
      rintro x' rfl μ hμ
      exact (hlev0 μ hμ).1
    exact key x (eq_of_heq ax)
  refine ⟨⟨q.core.a.Pq_over, ?_⟩, ?_, ?_, ?_⟩
  · intro μ P hP P' hC
    have hP'eq : P' = Host.CT.plMap R.T.ker.seam.iE P :=
      HeightOneSpectrum.ext (hC.trans (SelJ.carried_plMap R.T.ker.seam P).symm)
    subst hP'eq
    have hm : Host.CT.plMap R.T.ker.seam.iE P ∈ q.w.I.Q μ := hQ μ ▸ Finset.mem_image_of_mem _ hP
    obtain ⟨v, -, hv, -⟩ := q.w.I.exists_of_mem_Q hm
    rw [hsel]
    exact ⟨v, hv⟩
  · intro μ hμ
    rw [hQ μ]
    exact (eq_of_heq (hlev μ hμ)).symm
  · intro v hv
    rw [hHD]
    exact de_pin q v hv
  · intro v hv
    rw [hHD]
    exact de_pin' q v hv

end GlobalTheory.Mem.R3.SelSideW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem exists_params_atMem (hL : GlobalTheory.Published.LocalLanglandsGL) :
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L) := by
  refine (evG_of_ev GlobalTheory.PrimIn.AtData.ev_params).imp fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_⟩
  obtain ⟨L, -, -, hp, -⟩ := hK (w.st Z) hO t.etaF fun v hv j h1 h2 => by
    have key : ∀ v', (w.D Z).what₂.muAt v' = (w.D Z).what₂.mu0 → v' ∉ Wt := by
      intro v' he hw
      have he' : (w.st Z).W.muAt v' = (w.st Z).C.mu0 := he
      rw [t.mu.on v' hw] at he'
      have h1 := t.mu.tw v'
      rw [he', t.mu.mu0] at h1
      exact (TwFin.tw_fin B f T).2.1 v' h1.symm
    change (w.D Z).what₂.Aj j v = 0
    replace hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := hv
    have a := t.untw v (key v hv) j h1 h2
    have b := t.untw _ (key _ (((w.D Z).what₂.muAt_conj v).trans hv)) j h1 h2
    unfold Formalism.BasicNotions.Rows.Data.Aj
    rw [hv, a.1, a.2, b.1]
    rfl
  exact ⟨L, hp⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

set_option maxHeartbeats 2000000 in

theorem ev_params_withLoc : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    (∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L)) ∧
      ∀ Lc : LocAll (lay0 X.toD7), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  have hGam : ∀ u, Real.log (D.mem u).A.GamP = K.C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * K.s.L := fun u => by
    have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
    rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl
  refine ⟨?_, fun Lc => ?_⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
      (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s (withLoc Lc) (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx)
      hP.rank hP.val (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN (withLoc Lc) L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem stepW_start_ev {Q : Ctx → Prop} (h : Ev Q) : StepW Start fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

theorem aj_zero_at_state : StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
    ∀ v, (Dof x).what₂.muAt v = (Dof x).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → (Dof x).what₂.Aj j v = 0 := by
  refine StepW.of_all fun K B f T w hO hF hS P x v hv j h1 h2 => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have e1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ e1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  have H := GlobalTheory.T.indices_pairingLengths_vanish_off_twistedPlaces K B f T w hO hF ⟨hS.1, ⟨P⟩⟩ P x hex
  have key : ∀ v', (w.D x.o.Z).what₂.muAt v' = (w.D x.o.Z).what₂.mu0 → v' ∉ P.Wt := by
    intro v' he hw
    have he' : P.q.W₀.muAt v' = w.C.mu0 := he
    rw [P.q.mu.on v' hw] at he'
    have e2 := P.q.mu.tw v'
    rw [he'] at e2
    exact (TwFin.tw_fin B f T).2.1 v' (e2.symm.trans (show w.I.xi w.C.mu0 = 1 from w.l.xi0))
  change (w.D x.o.Z).what₂.Aj j v = 0
  replace hv : (w.D x.o.Z).what₂.muAt v = (w.D x.o.Z).what₂.mu0 := hv
  have a := H v (key v hv) j h1 h2
  have b := H _ (key _ (((w.D x.o.Z).what₂.muAt_conj v).trans hv)) j h1 h2
  unfold Formalism.BasicNotions.Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem exists_params_allSt : AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
    ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ((stepW_start_ev ev_params_withLoc).and aj_zero_at_state).trans
    (StepW.of_all fun _ _ _ _ w hO _ H P x => H.1 (w.st x.o.Z) hO x.etaF (H.2 P x))

theorem exists_params :
    (∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧
      AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
        ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ⟨exists_params_atMem, exists_params_allSt⟩

end GlobalTheory.HeightCounting.Up.SizePar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan

theorem genRank_le_of_inRCone_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) →
    genRank v ≤ genRank γ := by
  intro O _ bar ψ X _ _ _ m n γ v hγ hbal hnn hcone
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hk : ∀ j, ∃ k : ℕ, 0 < k ∧ ((k : ℤ) • v j) ∈ Submodule.span ℤ (Set.range γ) := by
    intro j
    obtain ⟨c, hc, e⟩ := hcone j
    have hl := apply_eq_of_toReal_eq e ℓ
    have hlin := (linearOn_iff ψ γ).1 hγ.linear c hc
    rw [← e, evalR_toReal] at hlin
    have heq : (N : ℝ) * ψ.evalZ (v j) = ℓ (v j) := by
      rw [hl, hlin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i]; ring
    obtain ⟨k, c', hk, hc'⟩ := h3 (v j) (hbal j) (hnn j) heq
    refine ⟨k, hk, ?_⟩
    rw [natCast_zsmul, hc']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose k hkpos hkmem using hk
  set K : ℕ := ∏ j, k j with hKdef
  have hK : 0 < K := Finset.prod_pos fun j _ => hkpos j
  set S := Submodule.span ℤ (Set.range γ) with hS
  have hle : Submodule.span ℤ (Set.range v) ≤ S.comap ((K : ℤ) • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨r, hr⟩ : k j ∣ K := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show ((K : ℤ) • LinearMap.id) (v j) ∈ S
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hr, Nat.cast_mul, mul_comm, mul_smul]
    exact S.smul_mem _ (hkmem j)
  let f : Submodule.span ℤ (Set.range v) →ₗ[ℤ] S :=
    (((K : ℤ) • LinearMap.id).comp (Submodule.span ℤ (Set.range v)).subtype).codRestrict S fun x => hle x.2
  have hf : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    apply Subtype.ext
    refine LinearMap.ext₂ fun a b => ?_
    have e2 := LinearMap.congr_fun₂ e a b
    simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul] at e2
    exact mul_left_cancel₀ (by exact_mod_cast hK.ne') e2
  haveI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  exact LinearMap.finrank_le_finrank_of_injective hf

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X)
    (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
      spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
        (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
    intro q ψ
    simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
  rw [e, e] at h
  have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
  simp only [Sigma.mk.inj_iff] at h2
  obtain ⟨rfl, h3⟩ := h2
  have h4 : φ = φ' := by
    have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
    ext x
    apply gam.injective
    have := congrArg (fun f => f.hom x) h5
    simpa using this
  rw [h4]

theorem GlobalTheory.spec_map_field_epi : ∀ {K C : Type} [Field K] [Field C] (gam : K →+* C) {X : Scheme} (y y' : Sp K ⟶ X), spMap gam ≫ y = spMap gam ≫ y' → y = y' :=
  fun gam _ y y' h => GlobalTheory.spec_map_field_cancel gam y y' h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarClosedIntegralLatticeAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem fixedField_star_stable_third : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x =>
    ∀ _ : LC hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGap

theorem gap_eq_sum {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hlin : φ.LinearOn γ) {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsum : toReal β = ∑ i, c i • toReal (γ i)) :
    (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (γ i) : ℝ) - N * φ.evalZ (γ i)) := by
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem starDepth_le_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro E _ _ _ H q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone H.bar X := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ H.bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.PolFan.StarGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthSetBddAboveOfUniqueCentreStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π → BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  first | exact @GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | exact GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | (intros; apply GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre <;> assumption)
end

