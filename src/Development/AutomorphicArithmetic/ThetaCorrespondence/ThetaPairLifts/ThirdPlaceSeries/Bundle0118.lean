import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0087
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0579
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActMemMK
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieMK
theorem act_mem_MK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ i g f hf
  exact ((GlobalTheory.RealGeoIn.mkStable_of_rhoGeo p.fw p.pins p.rhoGeo i) g f).2 hf
end GlobalTheory.TieMK
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  first | exact @_root_.GlobalTheory.FrameAut.autSt_of_smallSt' | exact _root_.GlobalTheory.FrameAut.autSt_of_smallSt' | (intros; apply _root_.GlobalTheory.FrameAut.autSt_of_smallSt' <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfStepsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  first | exact @_root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe | exact _root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe | (intros; apply _root_.GlobalTheory.CovTop.Assembly.covolX_of_lift_bounds_and_coreLe <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCoreStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  first | exact @_root_.GlobalTheory.DefCore.defCase_core_alt | exact _root_.GlobalTheory.DefCore.defCase_core_alt | (intros; apply _root_.GlobalTheory.DefCore.defCase_core_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCongStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_lev_sub_mem_Mb_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  first | exact @_root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | exact _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb | (intros; apply _root_.GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactAtOfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.CovTop.MeasRd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.CovTop.MeasRd
namespace GlobalTheory.CovTop.MeasRd
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem exactAt_of_rows_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.PointConditions') (hM : OneMeasure D) (i : Fin D.R.m) : ExactAt p i := by
  intro σ f
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hk : p.κ = kapTop D := KapIs.eq (κ := p.κ) p.fw.kap hTau
  have ha : wtA (p.κ i) = wtA (kapTop D i) := by rw [hk]
  have hn : (p.κ i).n = (kapTop D i).n := by rw [hk]
  have hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i := by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]
  obtain ⟨-, hd, h2⟩ := hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv
  have hmod := p.charW.base.models
  obtain ⟨h0, ht, he, -⟩ := h2 _ _ (hmod.νW i)
  obtain ⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ) := ⟨_, rfl⟩
  have hs := sgAt_mk_eq D.what₂.embLL σ
  rw [← hs_def] at hs
  show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _
  rw [← hs_def]
  have hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ) := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; exact GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)
  have hgood := goodEmb_goodOf p.T.Q.c (res p.T s)
  have hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgood
  obtain ⟨-, hrange, hip⟩ := hmod.HW i s
  by_cases hf0 : f = 0
  · subst hf0
    have hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0 := by
      rw [map_zero]; rfl
    have hz := petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
      (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0
    rw [map_zero, norm_zero, zero_mul, zero_smul] at hz
    rw [hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]
  set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    with hy
  have hy0 : y ≠ 0 := fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))
  set x := (p.R.toRealDat.FW i).j s y with hx_def
  have hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s := hrange ▸ LinearMap.mem_range_self _ x
  set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def
  have hf' : f' ∈ scalarForms p.T i (gd p.T s) := by
    have := ((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood
    show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))
    rw [modelWt_wtZ, ← ha, ← hn]
    exact this
  have hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f' := by
    by_cases hgs : GoodEmb p.T.Q.c (res p.T s)
    · have hgd' : gd p.T s = res p.T s := by show goodOf _ _ = _; rw [goodOf, if_pos hgs]
      have hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgs
      have hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H,
          ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
            ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) :
              Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) =
              hV' ▸ p.T.phiJ ((i : ℕ) + 1) (res p.T s) (wtA (p.κ i)) (g : p.T.R ((i : ℕ) + 1)) := by
        by_contra hne
        have hj0 := p.fw.ev0 i s hgs hV' hne
        have hli := (hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)
        rw [hj0] at hli
        exact hli.ne_zero 0 (LinearMap.zero_apply _)
      refine Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (p.fw.ev i s hgs hV' hpre f).trans ?_
      show phiC p.T hV' (wtA (p.κ i)) _ = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha]
      exact phiC_congr hgd'.symm _ _ _ _
    · have hgd' : gd p.T s = resC p.T s := by show goodOf _ _ = _; rw [goodOf, if_neg hgs]
      have hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)
      obtain ⟨v, hv, hvf⟩ := (p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)
      refine Or.inr ⟨hgs, v, hv, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (hvf f).trans (funext fun g => ?_)
      show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha, phiC_congr hgd' hV hVc]
  have e := (he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2
  rw [← hip, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f' := by
    have : (((‖x‖ ^ 2 : ℝ)) : ℂ) = _ := (Complex.ofReal_pow _ _).trans e
    exact_mod_cast this
  rw [hf'_def, probSq_rdU] at e'
  unfold petW
  rw [← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]
  rfl
end GlobalTheory.CovTop.MeasRd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), B.Q.Rl.toRealDat.ExAt ∧ JEvBar B.T B.Q.Rl.toRealDat B.κ ∧ GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀ ∧ EvInj B.T B.Q.Rl.toRealDat B.v₀ := by
  first | exact @_root_.GlobalTheory.FireAtRealisation.fire_alt | exact _root_.GlobalTheory.FireAtRealisation.fire_alt | (intros; apply _root_.GlobalTheory.FireAtRealisation.fire_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.FlatVal
variable {D : D7} {L : SizeData₂ D}
theorem flat_val_alt : _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  intro hF
  refine Closed.imp (Closed.and hF (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩
  obtain ⟨x0, h⟩ := h1.and h2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨a, b⟩ := h x hx hle ι p hp
  have hN := b i
  have hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _ := a i hi Y hY
  have hT := p.fw.laws
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hpos := Inhab.rank_pos _ hT.pins _ hj
  refine ⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩
  · rw [hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]
    have e : ∀ u v : ℝ, -u - v + u = -v := fun u v => by ring
    rw [e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)
  · exact (GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1
      fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)
end GlobalTheory.CovTop.FlatVal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameClose
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.FamTraceChiCol
end GlobalTheory.FamTraceChiCol
noncomputable section
namespace GlobalTheory.FamTraceChiCol
set_option maxHeartbeats 4000000 in
theorem frame_close_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → ∀ g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → (∀ p q : Fin (I.rec7 l Z).R.k, valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inl p) (Sum.inl q) - g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q))) < 1) ∧ ∀ p q : Fin ((a.G i).s + 1), q.val = p.val + 1 → valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val (Sum.inr p) (Sum.inr q)) < 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i x hx g hg
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hrJ := (_root_.GlobalTheory.T.true_geometry_local_data_alt W hW u a ha hat row col hc κ hκ y hy).1 hyU
  have hb : a.g.b 0 ∈ GfC (Yc (I.rec7 l Z) 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hxe : embA a.d.B.d a.d.B.o κ ∈ GfC ((I.rec7 l Z).sp.Y 0) := GlobalTheory.Corev.EmbAGfC.embA_mem_GfC_fin _ _ _ _ _ _ _ _ κ hκ
  have hSt := ((_root_.GlobalTheory.FamTrace.Rows.mem_rJ_iff_finE_mem_St_and_block_mem W _ (mul_mem (mul_mem (inv_mem hb) hxe) hb)).1 hrJ).1
  obtain ⟨e, he, hM⟩ := hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hid := (hG.idem i).1
  have hn : (Yc (I.rec7 l Z) 0).rank = (I.rec7 l Z).R.r := by
    rw [(I.rec7 l Z).sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have hr : (I.rec7 l Z).R.r ≤ (Yc (I.rec7 l Z) 0).rank := hn.ge
  have hmi : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega
  have hbes : (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 _ hmi →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hmi _ _
    exact key _ (ha.bot.1 hmi) _ _ HEq.rfl HEq.rfl
  have hm := GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ hbes κ g hg
  let σ := e.symm.trans (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _))
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo (a.G i).q (a.pl i).1 hid _ _ _ _ _
    (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
      GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
      ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.submatrix σ σ) hM ?_ hSt
  swap
  · have hs : ∀ (A : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (Fin (Yc (I.rec7 l Z) 0).rank) (a.G i).k)
        (M : Matrix (Fin (Yc (I.rec7 l Z) 0).rank) (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1)) (a.G i).k),
        A * M.submatrix id σ = (A * M).submatrix id σ := fun A M => by
      ext r c'; simp [Matrix.mul_apply]
    have e1 : ((Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr) *
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β =
        ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val := by
      have hm' : (Formalism.L2.Theta.mt (Yc (I.rec7 l Z) 0) ((embA a.d.B.d a.d.B.o) κ)).map (a.G i).q.pr =
          ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β * (GlobalTheory.RootEx.embX ((a.G i).s + 1) g).val *
            ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ := hm
      rw [hm', Matrix.mul_assoc, Matrix.mul_assoc, Frame.γβ, Matrix.mul_one]
    refine Eq.trans (hs _ _) ?_
    refine Eq.trans ?_ (Matrix.submatrix_mul_equiv _ _ id σ σ).symm
    rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, ← Units.val_mul]
    congr 1
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel_left]
  have hidx : ∀ (p : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a' : Fin (I.rec7 l Z).R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → e.symm (Fin.castLE hr a') = .inl p := fun p a' ha => by
    rw [Equiv.symm_apply_eq]
    refine Fin.ext ?_
    rw [he]
    rcases p with p | p <;> exact ha
  have main : ∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r),
      p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q →
      valuation (a.G i).k ((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k).val p q -
        (((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl p))
            (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _) (.inl q)))) < 1 := by
    intro p q p' q' hp hq
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((_root_.GlobalTheory.FamTraceChi.reductionYZero_alt W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ *
      embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q')
    have h1 := hx p q p' q' hp hq z hz
    have h2 := key (Fin.castLE hr p') (Fin.castLE hr q') z (by
      rw [hz]; exact congrFun (congrFun (GlobalTheory.SeeConjReord.rankBlock_val_eq_submatrix_of_le_rank hr hn.le _) p') q')
    simp only [Matrix.submatrix_apply, σ, Equiv.trans_apply, hidx p p' hp, hidx q q' hq] at h2
    have e : ∀ s t w : (a.G i).k, s - t = (s - w) + -(t - w) := fun s t w => by ring
    rw [e _ _ ((ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E))]
    exact Valuation.map_add_lt _ h1 (by rw [Valuation.map_neg]; exact h2)
  refine ⟨fun p q => ?_, fun p q hpq => ?_⟩
  · have hpr : p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have hqr : q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; unfold Ranks.r; omega
    have h := main (.inl p) (.inl q) ⟨p.val, hpr⟩ ⟨q.val, hqr⟩ rfl rfl
    have h11 := GlobalTheory.LevX.conj_embX_val (a.G i).S.ϖ
      (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h11' := congrFun (congrFun h11 (.inl (.inl p))) (.inl (.inl q))
    rw [GlobalTheory.StepData.stdOrd_eps, GlobalTheory.StepData.stdOrd_eps] at h
    exact h11' ▸ h
  · have hpr : (I.rec7 l Z).R.k + p.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := p.2; unfold Ranks.r; omega
    have hqr : (I.rec7 l Z).R.k + q.val < (I.rec7 l Z).R.r := by
      have := (a.G i).hs; have := q.2; unfold Ranks.r; omega
    have h := main (.inr p) (.inr q) ⟨_, hpr⟩ ⟨_, hqr⟩ rfl rfl
    have h22 := conj_embX_toBlocks₂₂ (a.G i).S.ϖ
      (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)) g
    have h22' := congrFun (congrFun h22 p) q
    have hne : p ≠ q := fun h => by rw [h] at hpq; omega
    rw [Matrix.one_apply_ne hne] at h22'
    have hs1 : ∀ r : Fin ((a.G i).s + 1), stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ((a.G i).s + 1) (Nat.zero_add _)
        (.inl (.inr r)) = .inr r := fun r => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block _ _ 0 _ _ r
    rw [hs1, hs1] at h
    change valuation (a.G i).k (_ - ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q) < 1 at h
    have e0 : ((((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _))⁻¹ *
          GlobalTheory.RootEx.embX ((a.G i).s + 1) g *
          ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).bas 0 ((a.G i).s + 1) (Nat.zero_add _)).val.toBlocks₂₂ p q = 0 := h22'
    rw [e0, sub_zero] at h
    exact h
end GlobalTheory.FamTraceChiCol
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodWAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.GoodWCore
end GlobalTheory.CovTop.GoodWCore
namespace GlobalTheory.CovTop
theorem goodW_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz),
    p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m,
      GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i) :=
  fun p _ _ i => GoodWCore.goodW_core p.T p.fw.laws _ ⟨Nat.le_add_left _ _, i.2⟩ (p.κ i)
    (GlobalTheory.GoodLat.Obj.latFull p.T p.fw.laws p.fw.kap i)
end GlobalTheory.CovTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HasGramAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.GramPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem hasGram_at_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → RecTied D L → ∀ i : Fin D.R.m, HasGram (nrmR p.R.toRealDat i) :=
  fun p hp _ i => hasGram_of_unif p.R.toRealDat hp.prim.unif i
end GlobalTheory.CovTop.GramPt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostNStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
end

