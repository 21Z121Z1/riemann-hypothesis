import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0837
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0179
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0071
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EtaSizeRecursion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfAttached
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0618
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0119
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemAnd
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLambdaInvariantBound
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamAll
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covering_lambda_all_places_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  intro hP hG hM
  have hc := _root_.UpperTheory.Lit.Tam.integral_cusp_slope_power_bound_alt_alt hP hG
  have hH : _root_.GlobalTheory.CovTop.HostNAlt 1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.T.lift_weight_numerator
  refine Closed.imp ((((hc.and hM).and hH).and hG).and hW) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨⟨⟨⟨A1, hA1, hc⟩, ⟨Cm, hCm, hm⟩⟩, ⟨Ah, hAh, hh⟩⟩, ⟨Cg, -, hg⟩⟩, ⟨Cw, -, hw⟩⟩ := h
  refine ⟨A1 + (Ah + 1) + (⌈2 * Cm⌉₊ : ℝ), by have := Nat.cast_nonneg (α := ℝ) ⌈2 * Cm⌉₊; linarith, ?_⟩
  obtain ⟨x0, H⟩ := (((hc.and hm).and hh).and hg).and hw
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := H x hx hle ι p hp
  have hH1 := c i
  have hX : 10 ≤ (Fm.L x ι).sc.x := hH1.big.2.1.trans hH1.big.2.2.1
  have hb : 0 ≤ (Fm.L x ι).sc.b := le_trans (by positivity) hH1.room
  exact le_rpow_of_add hX hb hA1 (by linarith [hH1.poly.1]) hCm (unitE_le p i hH1 (e i))
    ((slopeMax_all_le p i Cm (d i) (b i)).trans (by linarith [a i]))
end GlobalTheory.CovTop.LamAll
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLambdaBound_of_gram_meas : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  first | exact @_root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | exact _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | (intros; apply _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLinkedOfEq
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.Top.Bl
theorem exists_linked_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (hB : ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ)
      (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
      q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b))
    (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex) (hR' : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') (c : ℝ) {D : D7} {O : Obj D} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (he : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) (hsc : O.L.sc = K.s)
    (hv : Val K.C K.cD K.ch O.L) (n : {n : ℕ × ℕ // D.s.Del = (n.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (n.2 : ℝ)}) :
    ∃ b : _root_.GlobalTheory.Fc.BundleCondition D O c, ∃ (q' : WPt p.s K) (b' : _root_.GlobalTheory.Fc.BundleCondition (q'.w.D q'.Z) q'.O c), Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q' b') ∧
      (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c) = ⟨q'.w.D q'.Z, q'.O, b'⟩ := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  obtain ⟨b, -, hW⟩ := hB q R' hR' c n hsc hv
  exact ⟨b, q, b, hW, rfl⟩
theorem exBL_isLinked_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hA hW hRay hL p hWit hZe hB
  refine ⟨fun _ _ _ _ _ => True, GlobalTheory.Fc.largeBaseProperty_true, ?_⟩
  unfold GlobalTheory.Fc.ExB
  refine GlobalTheory.Fc.EvP.mono (fun κ K _ H => ?_) (GlobalTheory.Fc.EvP.and hZe hB)
  intro β hβ c
  obtain ⟨q, hq, hE⟩ := hWit K β hβ.1
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hO : Over β.X.toD7 K.P K.Lv := by
    obtain ⟨sp, hT, hY, hA', hV, hz, e, -⟩ := β.c.isOver
    exact ⟨sp, hT, hY, hA', hV, hz, β.X, e, rfl⟩
  have hP : K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} :=
    hG.host.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLT : Formalism.L2.Host.LevelTied β.D :=
    GlobalTheory.Mem.HD.levelTied_of_levEx _ ((GlobalTheory.Mem.HD.levEx_of_over _ _ _ hO hP).2 _ _)
  have hD : β.D = q.w.D q.Z := congrArg Sigma.fst hq
  have hLT' : Formalism.L2.Host.LevelTied (q.w.D q.Z) := hD ▸ hLT
  obtain ⟨R', hR'⟩ := _root_.GlobalTheory.T.exists_reciprocity_record_compatible hA hW hRay hL p K q hLT' (H.1 q) hE
  obtain ⟨R, he⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_bdRec_of_eq_alt hq R' c
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_linked_of_eq_alt H.2 q R' hR' c R he β.sc hv ⟨(_, _), hv.Del_eq, hv.eta_eq⟩
end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConjStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_datum_rational_normalization_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∀ (n : ℕ) (a : Fin n → NX.KB p.Sx ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
        (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
        p.nexp.eF ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) (Nat.le_add_left _ _) j.2 f =
          ∑ k, a k ⊗ₜ[p.Sx.Ks] g k →
      ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
        ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
          ∑ k, τ (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k)) • evW p.nexp p.v₀ j (g k).val =
            c • ∑ k, ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expConj_alt | exact _root_.GlobalTheory.BigOn.Exp.expConj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expConj_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHoldsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_flat_estimate : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfIsTriple
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
end Triple
theorem adm1_adm8_selfDual_noJump_of_isTriple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀)
    (hF : FrobDense D) (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h2 : BlochKatoReduction.adm2 D) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    BlochKatoReduction.adm1 (bk0 D) ∧ BlochKatoReduction.adm8 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump (bk0 D) i s :=
  _root_.GlobalTheory.TripleGal.adm1_adm8_selfDual_noJump_of_tripleAttN D (bk0 D) hF (fun _ _ => ⟨_, ⟨D.locT _⟩⟩) h2 (_root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple S hF hG h)
end GlobalTheory.TripleLocal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenVol
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PenVol
end GlobalTheory.PenVol
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.PenVol.pen_vol_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 = B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨U0, hU0le, hU0c, hU0⟩ := _root_.GlobalTheory.T.true_geometry_step_relation_alt W hW u a ha haT j hj
  have hI : I.Ok := hW.tr.ok
  have hP : TC.Pins B X := hW.tr.pins.some
  have hjm : j ≤ B.R.m := by omega
  have key : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α,
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) * ((J.A.U j (J.ι j α)).relIndex U0 : ℝ) =
        GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 ∧
      ((J.A.U j (J.ι j α)).relIndex U0 : ℂ) = J.wt j α ∧
      GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 ∧ (J.A.U j (J.ι j α)).relIndex U0 ≠ 0 := by
    intro t J hR α
    obtain ⟨hle, hidx⟩ := hU0 t J hR α
    have hrep := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j hjm (J.ι j α)).1
    refine ⟨GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (a.g.x j).vol _ _ hle hU0le hU0c hrep.opn, ?_,
      GlobalTheory.AdForm.PinInhab.volLev_ne_zero hI haT.pinX.inf j (a.g.x j).vol (J.ι j α) hrep,
      GlobalTheory.PenVol.relIndex_ne_zero_of_open (GfC _) _ _ hU0le hU0c hrep.opn⟩
    rw [hidx, Nat.cast_prod, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight (J.G i) (J.E i)]
    exact GlobalTheory.PenVol.wt_cast _ (J.E i).wt (by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega) (α i)
  by_cases hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t0, J0, hR0, ⟨α0⟩⟩ := hex
    obtain ⟨h1, -, h3, h4⟩ := key t0 J0 hR0 α0
    refine ⟨(GlobalTheory.SeeSaw.volLev (a.g.x j).vol U0 : ℂ), ?_, fun t J hR α => ?_⟩
    · rw [← h1]; exact_mod_cast mul_ne_zero h3 (Nat.cast_ne_zero.2 h4)
    · obtain ⟨e1, e2, -, -⟩ := key t J hR α
      rw [← e2, ← e1]; push_cast; ring
  · exact ⟨1, one_ne_zero, fun t J hR α => absurd ⟨t, J, hR, ⟨α⟩⟩ hex⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfRefinedTheta
section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.ToWeight
theorem refinedSum_weight_of_refinedTheta_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := fun hP hS hF hT =>
  Closed.imp (Closed.and (Closed.and hT (_root_.GlobalTheory.BadLog.logSum_badPrimes_le_alt hS))
      (Closed.and hF (Closed.and (_root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds hS) (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS))))
    fun Fm _ _ ⟨⟨⟨C₁, h₁, hT⟩, C₂, h₂, hB⟩, ⟨_, _, hF⟩, ⟨_, _, hZ⟩, _, _, hW⟩ => by
      obtain ⟨x0, h⟩ := ((hT.and hB).and hF).and (hZ.and hW)
      refine ⟨C₁ + (30 + C₂), by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
      obtain ⟨⟨⟨hT, hB⟩, hF⟩, hZ, hW⟩ := h x hx hle ι p hp
      obtain ⟨S, e, s, hS, hs, he⟩ := hT i hi Y hY u1 hq
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hZ i
      obtain ⟨w1, w2, -, -, -, -, -, -, w3⟩ := hW i hi u1 hq
      have hB := hB i hi Y hY
      have hm : 2 * ((nCol (dat p i) / 2 : ℕ) : ℝ) ≤ nCol (dat p i) := by exact_mod_cast Nat.mul_div_le _ 2
      have hsz := size_le (by exact_mod_cast z5) (by exact_mod_cast z6) z2 (Nat.cast_nonneg _) hm z4 z3 h₂ hB
      refine ⟨_, _, _, primeSum_add (Fm.D x ι).host.E (B := badPrimes p.T.Q.H Y.d.l₂)
        (a := ((nCol (dat p i) / 2 : ℕ) : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r)) hS badPrimes_prime (by positivity), ?_,
        fun q hq' => ?_⟩
      · have a1 := mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP))
        have a2 := mul_le_mul_of_nonneg_left z1 (show (0 : ℝ) ≤ 30 + C₂ by positivity)
        unfold zBase at a2
        linarith
      · refine (_root_.GlobalTheory.T.reference_exponent_valuation_bound hP _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, hi.le⟩ hY.1 w1 w2 ⟨_, hF i hi Y hY⟩ u1
          (shift (dat p i) u1 (nCol (dat p i))) (nCol (dat p i) / 2) (1 / 2500) q hq').trans ?_
        rw [EReal.coe_add]
        exact add_le_add (w3 ▸ he q hq') le_rfl
end GlobalTheory.RefSum.ToWeight
end
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | exact _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | (intros; apply _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt <;> assumption)
end
end
end

