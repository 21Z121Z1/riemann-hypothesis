import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfClassSumsSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
section
noncomputable section

namespace GlobalTheory.LiftSpanClauses

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.OneMapTuples GlobalTheory.OneMapAll
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

open GlobalTheory.PinnedClassSum GlobalTheory.GeoLevel GlobalTheory.Member Formalism.L2.Host

set_option maxHeartbeats 2000000 in

theorem clsEx_of_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsFam → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → GlobalTheory.OneMapTuples.ClsEx O (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hF ⟨tie⟩ _ i Tp tup O hLL hO t x _
  have hT := tie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr : 1 ≤ D.R.r := by
    have h1 := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2.1
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  obtain ⟨hd, hA₂, hnab⟩ := hO.cov t
  obtain ⟨-, -, hxi, ⟨e, -, hφ⟩, hMb, hQ, -⟩ := hO.tuple t
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨n, hn, ho⟩ := hL.xi_fin (tup t)
  obtain ⟨xi', hx1, -, hx3, hx4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi _) n hn ho
    (hL.xi_triv _) (hL.xi_tame _)
  have hxx : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨z, hz⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g z hz).trans (hx1 g z hz).symm)
  have hxN : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) ^ (m * n) = 1 := fun g => by
    rw [hxx, mul_comm, pow_mul, hx4, one_pow]
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  obtain ⟨gramR, c0R, c0L, hfam⟩ := hF.tie
  obtain ⟨ψ, hψ⟩ := exists_psi (Wc D i) (O.dδ t) (iotaW T i) hio.emb (hpq.trans (rank_Wc i).symm) hpos hd (R.Q (tup t)) hQ
    (R.xiR (tup t)) fun P hP z =>
      hLL (GlobalTheory.RationalValues.xiR_mem R hL hF.pl_onto hF.muVal hfam.ok i (tup t) P hP z)
  have htie : (O.dδ t).PsiTie ψ := by
    refine psiTie_of_values (Wc D i) (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      (fun γ hγ => (hxx γ).trans (hx3 γ hγ)) _ _ c0 hcN (hv t) ψ fun k s u hu₀ hu hk hlift => ?_
    obtain ⟨y, -, hdet⟩ := exists_int_matrix (hL.βW i) hu
    have hres : ∀ P : R.Q (tup t), ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y) : (kP P.1)ˣ) : kP P.1) =
        resS D.host.F P.1 y.1.det := fun P => ((resS D.host.F P.1).map_det _).symm
    obtain ⟨z, hz, hval⟩ := exists_root_value (O.dδ t).l₂ hu₀ (hL.xi (tup t)) (hL.xi_tame _) (R.Q (tup t)) (R.xiR (tup t))
      (hL.xiR _) (fun P hP => (hd.2.2.2.1.le.trans Ideal.mul_le_right).trans (hQ P hP)) (fun P => (hL.Q_ram _ P).1) _ hdet _ hres
    exact (hψ k s u _ hk hlift hdet _ hres).trans (hval.symm.trans (hxi u z hz).symm)
  have hτ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  obtain ⟨τ₀⟩ := hτ
  have hnV : (κ i).n = (Vc D i).rank := (tie.kap i τ₀).2.2.trans (D.sp.V_rank _ hj.1 hj.2).symm
  have hlast : (κ i).LastPos := fun τ k hk => by
    rw [(tie.kap i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    refine GlobalTheory.LiftWeight.one_le_aPl_last D i τ _ _ ?_ hk
    simp only [Ranks.sigW]
    omega
  obtain ⟨-, cga, -, -, hrange, -⟩ := hO.io
  exact GlobalTheory.ClsVal.exists_cusp_isThClsD_unique GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) _ _ hr
    (fun σ hσ' => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ')) hT.pins.2.1.2
    (fun _ => ⟨hd, hA₂, hnab⟩)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ (Wc D i) _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      _ _ c0 hcN (hv t))
    ψ htie _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) (hnV ▸ dom_wtA (κ i))
    (GlobalTheory.lastPos_wtA_of_pins D T.Q hT.pins _ hj _ hlast)
    (fun k => datEq_of_values (Vc D i) (Wc D i) (R.βV i) (R.βW i) (hL.βW i) e (O.dδ t) hd _ hio R.Pg (R.Q (tup t))
      (fun P hP => hMb.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hP))) hQ _ (O.φ t) _ (hO.w t k)
      (fun z => (hφ z).1) (fun z => (hφ z).2) ψ hψ)
    (hO.reps t).1 hrange.le x

end Cls

section Retie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem placeEx_core {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La} (hP : ThPinsR R i jL σ' v₀ c0' ι M Mh lev)
    (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c0' := by
  obtain ⟨_, _, _, hT, hc⟩ := hP.c0
  exact GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}

set_option maxHeartbeats 1600000 in

theorem exists_retie_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hP : O.Pins κ v₀ ι x₀)
    (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : LevIs R i ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id)) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L) :
    ∃ O' : OMDat C R i Tp tup, O'.c' = O.c' ∧ O'.Pins κ v₀ ι x₀ ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  classical
  obtain ⟨c1, hc1⟩ := exists_coef_ext (W := (R.cV i).W) O.jL hP.lift.field (lamV D i) (c0L i)
  choose h J' h1 h2 h3 h4 using fun t => (hP.tuple t).reps
  have hL : ThPinsR R i O.jL (inC O.c') v₀ c1 ι C.Q.l.M (Mfr C.Q.l) lev :=
    ⟨hP.lift.field, hP.lift.std, hP.lift.v0, ⟨_, _, _, hT, hc1⟩, hlev⟩
  have h0 : ∀ t y, (∀ k, (R.HV i (tup t)).e y (fin _ (h t k)) = 0) → onQ (Wc D i) (R.thF i (tup t) y v₀) = 0 := fun t y hy => by
    have e1 := h3 t y 0 fun k => (hy k).trans (map_zero _).symm
    have e2 := h3 t 0 0 fun k => by rw [map_zero]; exact (map_zero _).symm
    rw [← e1, e2, map_zero]
    rfl
  refine ⟨{ O with
    c0' := c1, lev := lev
    thAd := fun t x => if hx : ∃ y, Place R i (tup t) (h t) c1 y x then onQ (Wc D i) (R.thF i (tup t) hx.choose v₀) else 0
    Plc := fun t x => ∃ x₀, Place R i (tup t) (h t) c1 (jVx R i (tup t) x₀) x }, rfl,
    ⟨hL, fun t => ⟨⟨h t, J' t, h1 t, placeEx_core R F hR i _ _ hL _ _, fun y x hy => ?_, fun x => Iff.rfl⟩,
      (hP.tuple t).B, (hP.tuple t).xi, (hP.tuple t).phi, (hP.tuple t).half⟩,
      ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).1⟩,
      hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩, rfl, hc1⟩
  have hx : ∃ y, Place R i (tup t) (h t) c1 y x := ⟨y, hy⟩
  refine (dif_pos hx).trans ?_
  have h5 := h0 t (hx.choose - y) fun k => by
    rw [map_sub, Pi.sub_apply, hx.choose_spec k, hy k, sub_self]
  rw [map_sub] at h5
  exact sub_eq_zero.1 h5

end Retie

def PointIdentCore : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0

section Guard

open GlobalTheory.LiftSpan

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 2000000 in

theorem liftsSpan_of_guard_core (hPI : PointIdentCore) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hR : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀))
    (hpb : T.pb = R.C.P.pb) (hio : IoExt R) (hO : OMPins T R κ v₀ O i) (hex : PinsExist T R κ v₀ i) (hG : QGuard R)
    (hspan : ClassSumsSpan (O i) (κ i)) : LiftsSpan R i (v₀ i (sg0 D A)) := by
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, -, hU⟩ := hPI D G Pl0 T0 A T R F κ v₀ hR h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hle₀, hP₀⟩ := hex hG
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := exists_retie_core O₀ hR
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := e₁ ▸ hle₀
  obtain ⟨c0, -, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  exact liftsSpan_of_ptIdent hP hspan hP₁ hlev₁ (clsEx_of_core D G Pl0 T0 A T R κ v₀ hR.lev hR.fam hW hpb i _ _ O₁ hle₁ hP₁)
    (ne_zero_of_root hr₁) (hU _ _ (O i) hO.1.ge hP rfl hc c0 hx) (hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁)

end Guard

end GlobalTheory.LiftSpanClauses

namespace GlobalTheory.LiftSpanClauses

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem liftsSpan_all_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hsz hC h1 h2 hW hio hO h0 hG
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hC.lev (hO.2.tuple ()).half
  have hex : GlobalTheory.OneMapTuples.PinsExist T R κ v₀ i := fun hG' => by
    obtain ⟨O', a, b, -⟩ := GlobalTheory.PinnedTuples.exists_pins_of_base D G Pl0 T0 A T R κ v₀ O hC.lev hC.grp.chiW hC.fam hC.models
      hC.thP.vP h1 h2 hW i hO hG'
    exact ⟨O', a, b⟩
  exact liftsSpan_of_guard_core GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum T R F κ v₀ O i hC h1 h2 hW hpb hio hO hex hG
    (GlobalTheory.ClassSumSpanCore.classSumsSpan_core D G Pl0 T0 A T R F κ v₀ O hsz hC hW hio i hO h0)

end GlobalTheory.LiftSpanClauses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}}

def addCls (A : Over S) [GrpObj A] (T : Over S) : AddSubgroup (Pic (A ⊗ T).left) where
  carrier := {c | ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c}
  add_mem' {c d} hc hd Y a a' t := by
    simp only [map_add]
    rw [hc Y a a' t, hd Y a a' t]
    abel
  zero_mem' Y a a' t := by simp only [map_zero, add_zero]
  neg_mem' {c} hc Y a a' t := by
    simp only [map_neg]
    rw [hc Y a a' t]
    abel

variable {A : Over S} [GrpObj A]

theorem fam_iff_mem {T : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) : Fam A N ↔ cls N hN ∈ addCls A T :=
  ⟨fun h ↦ (isAdditive_iff hN).1 h.add, fun h ↦ ⟨hN, (isAdditive_iff hN).2 h⟩⟩

def resCls {T' T : Over S} (u : T' ⟶ T) : addCls A T →+ addCls A T' :=
  ((CechPic.pull (lift (fst A T') (snd A T' ≫ u)).left).comp (addCls A T).subtype).codRestrict _
    fun c Y a a' t ↦ by
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply, ← CechPic.pull_comp,
        ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
      exact c.2 Y a a' (t ≫ u)

variable (A) in

def famFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{1} where
  obj T := CommGrpCat.of (Multiplicative (addCls A T.unop))
  map g := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative (resCls (A := A) g.unop))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T.unop) (snd A T.unop ≫ 𝟙 _)).left _ = _
    rw [Category.comp_id, lift_fst_snd, Over.id_left, CechPic.pull_id]
    rfl
  map_comp {T T' T''} g g' := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop ≫ g.unop)).left _ =
      CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop)).left
        (CechPic.pull (lift (fst A T'.unop) (snd A T'.unop ≫ g.unop)).left _)
    rw [← CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]

section Rep

variable {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P)

include h

def ptCls (T : Over S) (x : T ⟶ B) : addCls A T :=
  ⟨evc h.fam.isLB (fst A T) (snd A T ≫ x), (fam_iff_mem (pull_isLB h.fam.isLB _)).1
    ⟨pull_isLB h.fam.isLB _, fun Y a a' t ↦ by
      refine (cls_eq_iff (pull_isLB (pull_isLB h.fam.isLB _) _)
        (isLB_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _))).1 ?_
      rw [cls_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _)]
      rw [cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _)]
      rw [evc_ev h.fam.isLB, evc_ev h.fam.isLB, evc_ev h.fam.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.fam.isLB).1 h.fam.add Y _ _ _⟩⟩

theorem ptCls_bij (T : Over S) : Function.Bijective (ptCls h T) := by
  have hP := h.fam.isLB
  constructor
  · intro x x' e
    have hN : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hP _
    have fN : Fam A (ev P (fst A T) (snd A T ≫ x)) := (fam_iff_mem hN).2 (ptCls h T x).2
    refine (h.univ T (toUnit T) _ fN).unique ⟨toUnit_unique _ _, (cls_eq_iff hN hN).1 rfl⟩
      ⟨toUnit_unique _ _, (cls_eq_iff hN (pull_isLB hP _)).1 (congrArg Subtype.val e)⟩
  · intro c
    obtain ⟨N, hN, hc⟩ := cls_surj (c : Pic (A ⊗ T).left)
    have fN : Fam A N := (fam_iff_mem hN).2 (hc ▸ c.2)
    obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ T (toUnit T) N fN
    exact ⟨x, Subtype.ext (((cls_eq_iff hN (pull_isLB hP _)).2 hx).symm.trans hc)⟩

theorem ptCls_comp {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ B) :
    ptCls h T' (g ≫ x) = resCls g (ptCls h T x) := by
  refine Subtype.ext ?_
  change evc h.fam.isLB (fst A T') (snd A T' ≫ g ≫ x) =
    CechPic.pull (lift (fst A T') (snd A T' ≫ g)).left (evc h.fam.isLB (fst A T) (snd A T ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

def famRep : (famFunctor A ⋙ forget CommGrpCat.{1}).RepresentableBy B where
  homEquiv {T} := (Equiv.ofBijective _ (ptCls_bij h T)).trans Multiplicative.ofAdd
  homEquiv_comp g x := ptCls_comp h g x

end Rep

end GlobalTheory.DualCon

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S} {P : LB (A ⊗ B).left}

theorem evc_eq_pull_ptCls (h : Rep A (toUnit B) P) {Y : Over S} (a : Y ⟶ A) (x : Y ⟶ B) :
    evc h.fam.isLB a x = CechPic.pull (lift a (𝟙 Y)).left (ptCls h Y x : Pic (A ⊗ Y).left) := by
  change _ = CechPic.pull (lift a (𝟙 Y)).left (evc h.fam.isLB (fst A Y) (snd A Y ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]

theorem rep_isDual : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left),
    Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  intro S A B _ P h
  have hP := h.fam.isLB
  letI inst : CommGrpObj B := CommGrpObj.ofRepresentableBy B _ (famRep h)
  have hmul : ∀ (Y : Over S) (x y : Y ⟶ B), ptCls h Y (x * y) = ptCls h Y x + ptCls h Y y := by
    have hμ : ptCls h (B ⊗ B) μ[B] = ptCls h _ (fst B B) + ptCls h _ (snd B B) :=
      Equiv.ofBijective_apply_symm_apply (ptCls h (B ⊗ B)) (ptCls_bij h _) _
    intro Y x y
    rw [Hom.mul_def, ptCls_comp, hμ, map_add, ← ptCls_comp, ← ptCls_comp, lift_fst, lift_snd]
  have hone : ∀ (Y : Over S), ptCls h Y (1 : Y ⟶ B) = 0 := by
    have hη : ptCls h (𝟙_ (Over S)) η[B] = 0 :=
      Equiv.ofBijective_apply_symm_apply (ptCls h _) (ptCls_bij h _) 0
    intro Y
    rw [Hom.one_def, ptCls_comp, hη, map_zero]
  refine ⟨inferInstance, inferInstance, ⟨hP, h.fam.add, ?_, fun T M hM hA ↦ ?_⟩, ?_⟩
  · rw [triv_ev_iff hP, evc_eq_pull_ptCls h, hone, ZeroMemClass.coe_zero, map_zero]
  · obtain ⟨x, ⟨-, hx⟩, hu⟩ := h.univ T (toUnit T) M ⟨hM, hA⟩
    exact ⟨x, hx, fun y hy ↦ hu y ⟨toUnit_unique _ _, hy⟩⟩
  · have hs : (swap P).IsLB := pull_isLB hP _
    refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
    rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_eq_pull_ptCls h, evc_eq_pull_ptCls h,
      evc_eq_pull_ptCls h, hmul, AddSubgroup.coe_add, map_add]

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem cls_eq_evc_id {S : Scheme.{0}} {A T : Over S} {M : LB (A ⊗ T).left} (hM : M.IsLB) :
    cls M hM = evc hM (fst A T) (snd A T ≫ 𝟙 T) := by
  rw [Category.comp_id, evc, lift_fst_snd, Over.id_left, pull_id]

theorem cls_trans {S : Scheme.{0}} {A B B' B'' : Over S} {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left}
    {Q : LB (A ⊗ B'').left} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (x : B ⟶ B') (y : B' ⟶ B'')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) (hy : LBIso P' (ev Q (fst A B') (snd A B' ≫ y))) :
    LBIso P (ev Q (fst A B) (snd A B ≫ x ≫ y)) := by
  refine (cls_eq_iff hP (pull_isLB hQ _)).1 ?_
  rw [(cls_eq_iff hP (pull_isLB hP' _)).2 hx, cls_ev hP', cls_ev hQ, evc,
    (cls_eq_iff hP' (pull_isLB hQ _)).2 hy, cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

theorem rep_unique (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (h : Rep A b P) (h' : Rep A b' P') :
    ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  have hP := h.fam.isLB
  have hP' := h'.fam.isLB
  obtain ⟨x, ⟨hxb, hxP⟩, -⟩ := h'.univ B b P h.fam
  obtain ⟨y, ⟨hyb, hyP⟩, -⟩ := h.univ B' b' P' h'.fam
  have idB : LBIso P (ev P (fst A B) (snd A B ≫ 𝟙 B)) :=
    (cls_eq_iff hP (pull_isLB hP _)).1 (cls_eq_evc_id hP)
  have idB' : LBIso P' (ev P' (fst A B') (snd A B' ≫ 𝟙 B')) :=
    (cls_eq_iff hP' (pull_isLB hP' _)).1 (cls_eq_evc_id hP')
  have hxy : x ≫ y = 𝟙 B :=
    (h.univ B b P h.fam).unique ⟨by rw [Category.assoc, hyb, hxb], cls_trans hP hP' hP x y hxP hyP⟩
      ⟨Category.id_comp _, idB⟩
  have hyx : y ≫ x = 𝟙 B' :=
    (h'.univ B' b' P' h'.fam).unique ⟨by rw [Category.assoc, hxb, hyb], cls_trans hP' hP hP' y x hyP hxP⟩
      ⟨Category.id_comp _, idB'⟩
  exact ⟨⟨x, y, hxy, hyx⟩, hxb, (same_id_iff hP hP' x).2 hxP⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_le_one_of_dim_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  first | exact @GlobalTheory.SUVol.Degenerate.riemHaar_le_one | exact GlobalTheory.SUVol.Degenerate.riemHaar_le_one | (intros; apply GlobalTheory.SUVol.Degenerate.riemHaar_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  first | exact @GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | exact GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | (intros; apply GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published.AbelianDeRham

theorem rigid_of_free_of_crystallineDeRham : GlobalTheory.Published.AbelianDeRham.Free →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro H H' R _ A _ g hA hg I κ hκ R₀ _ π hπ hI A₀ _ i h
  have := hA.smooth
  have := hA.proper
  obtain ⟨h₁, -⟩ := H' R I κ hκ R₀ π hπ hI _ _ (A.hom ≫ 𝟙 _) A₀.hom i inferInstance inferInstance
    inferInstance (by rw [Category.comp_id]; exact h.1) (liftMor κ h).isMor
  have hP := (H R A g hA hg).1
  refine ⟨fun c d e ↦ Subtype.ext (h₁.1 ?_), fun c ↦ ?_⟩
  · have := congrArg Subtype.val e
    simpa only [GrpMor.coe_pull] using this
  · obtain ⟨c', hc'⟩ := h₁.2 c.1
    have hm : c' ∈ prim (dp0 R) (𝟙 _) A := by
      rw [show prim (dp0 R) (𝟙 _) A = ⊤ from hP]; trivial
    exact ⟨⟨c', hm⟩, Subtype.ext (by rw [GrpMor.coe_pull]; exact hc')⟩

end GlobalTheory.Published.AbelianDeRham
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGeneratedStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_lattice_finitely_generated : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, (latAll p.R.toRealDat i).FG := by
  first | exact @GlobalTheory.CovTop.latAll_fg_at | exact GlobalTheory.CovTop.latAll_fg_at | (intros; apply GlobalTheory.CovTop.latAll_fg_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanVal.value_tangent | exact GlobalTheory.MBLow.TanVal.value_tangent | (intros; apply GlobalTheory.MBLow.TanVal.value_tangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classifyingMap_unique : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' → SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  first | exact @GlobalTheory.SiegUniq.eq_of_siegPB | exact GlobalTheory.SiegUniq.eq_of_siegPB | (intros; apply GlobalTheory.SiegUniq.eq_of_siegPB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_tangentBound_nonconstant : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.SiegelTangentBound.main | exact GlobalTheory.SiegelTangentBound.main | (intros; apply GlobalTheory.SiegelTangentBound.main <;> assumption)
end

