import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.LocalToGlobal.Columns.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovAtBaseRoot
section
namespace GlobalTheory.AdTh.CoverRoot

section Core

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdTh.CoverVal

theorem rdU_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (k : U.Comp) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) {b : Frame (U.X k).Ψ r} (hb : b ∈ Bor (U.X k).Ψ r) :
    rdU U f k (rmul (lact γ x) b) = rdU U f k x := by
  have hs := hU.2.2.2.2.1 0 0 ⟨fun τ _ _ _ => le_rfl, Even.zero⟩ f hf k
  rw [show laU U 0 0 k = 0 from GlobalTheory.Reg.IdemCusp.laU_zero (Formalism.L2.PjFree.Unf.ofPj U) k] at hs
  rw [hs.2.1 _ (dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)) b hb, hs.2.2 γ hγ x hx, GlobalTheory.Reg.IdemCusp.chi_zero _ hγ]
  simp [bchar]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

set_option maxHeartbeats 1000000 in

theorem covAt_mem (hR : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (c0 : ℂ) (h0 : GlobalTheory.PtId.CovAt O c0) :
    c0 ∈ (inC O.c').range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  obtain ⟨c1, hm, hc⟩ := hO.cxi
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  obtain ⟨hlev, hA, -⟩ := hO.cov ()
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hX₀, hon₀, -, hp₀, hrk, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    hs0 (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ ()).c₂ ((inC O.c').comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  obtain ⟨hroot, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hxi : ∀ x, R.xi A.μ0 x = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0)
  have hf : (O.dδ ()).cδ ∈ sec (O.dδ ()).Xo₂ (O.dδ ()).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c1 := fun h => by
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 h
    obtain ⟨x, hx⟩ := hroot (γ' * h)
    have hv := hval h γ' ⟨hγ', h2, h3⟩
    rw [(hO.tuple ()).xi _ _ hx, hxi, Circle.coe_one, _root_.mul_one] at hv
    exact hv
  have key : ∀ h, (O.dict₂ () h).2 ∈ ((O.U₂ ()).X (O.dict₂ () h).1).dom ∧
      rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨hon, γ, ⟨hγ, hl, hfr⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ ()) hσ hU h1 hA R.θ (Wc D i)
      (rank_Wc i) (O.dict₂ ()) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt h
    obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ _ _ _ (O.dδ ()).c₂ _ _ Wt.g 0 ((O.U₂ ()).X (O.dict₂ () h).1) 0 Wt.e hσ hU.1
      (hU.2.1 _).1 (hU.2.1 _).2 hsd ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon
    have hA' := uw_anFib _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1 Dc.bas Dc.idx
      Dc.sympl hper hty ⟨_, hd'⟩ hu'
    obtain ⟨x, hx⟩ := hroot (γ * h)
    have h3 := h0 () _ Wt.g Dc.bas Dc.idx Wt.e (γ * h) x (Wt.mark (O.dict₂ () h).1) (hmod _) (hU.2.1 _).1 Dc.sympl
      ⟨hper, hty⟩ hl hx hmark hma
    rw [← hfr, hxi, Circle.coe_one, _root_.mul_one] at h3
    obtain ⟨A', hA'', -⟩ := hA'
    exact ⟨hd', (dif_pos hd').trans (h3 _ A' hA'')⟩
  obtain rfl : c0 = c1 := (key 1).2.symm.trans (hv 1)
  refine ⟨?_, hm⟩
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ (inR i) O.s0 (hs0 ▸ T.toCore.good_σ₀) (Wc D i) O.hV
    (rank_Wc i)
  have hpq := hrk ▸ h1
  obtain ⟨a, ha⟩ := GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range _ _ _ _ _ _ _ _ (O.U₂ ()) hσ hU hpq _ hf c0 fun k x hx => by
    obtain ⟨h, γ, hγ, b, hb, e⟩ := GlobalTheory.CoverIndep.dict_onto (Wc D i) (rank_Wc i) (O.U₂ ()) (O.dict₂ ()) (iotaW T i) e' F' ik φ
      th _ hσ hA hpq hU hW hD hio hth hx₀ (fun h => (key h).1) k x hx
    have h4 := hv h
    rw [e] at h4
    exact (rdU_move (O.U₂ ()) hU hf k hx hγ hb).symm.trans h4
  exact ⟨_, ha⟩

end Core

section Top

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem covAt_base_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ c0 : ℂ, GlobalTheory.PtId.CovAt (O i) c0 → c0 ∈ D.what₂.embLL.range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O _ hC i hOP c0 h0
  obtain ⟨⟨a, rfl⟩, hm⟩ := covAt_mem hC ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩ (O i) hOP.2 c0 h0
  refine ⟨?_, hm⟩
  obtain ⟨b, hb⟩ := hOP.1.le a.2
  exact ⟨b, hb⟩

end Top

end GlobalTheory.AdTh.CoverRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnity
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefRoot

theorem coef_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  intro D G _ _ Pl0 T m A cR cL lR lL B pl S Qt tauL lamR lamL gramR gramR' c0R c0R' c0L c0L' h h' i
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (lamL i)) with hs | hs
  · exact ⟨1, ⟨1, one_ne_zero, one_pow _⟩, fun F => by rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]⟩
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL i A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h'.coefL i A.μ0
  let g : Module.End D.what₂.LL (VV D.what₂.LL (lamL i)) := (e₂.symm.trans e).toLinearMap
  have hcg : ∀ v, c0L' i v = c0L i (g v) := fun v => by
    have h1 := hco₂ (e₂.symm v)
    rw [e₂.apply_symm_apply] at h1
    rw [← h1, hco]
    rfl
  have hinj : Function.Injective (c0L i) :=
    GlobalTheory.GalLift.rescale_inj (bVV D.what₂.LL (lamL i)) D.what₂.embLL (c0L i) (h.mapL i).2.1
  have hcomm : ∀ (γ : GQ (D.sp.V ((i : ℕ) + 1))) (γE : GL (Fin (D.sp.V ((i : ℕ) + 1)).rank) D.host.E),
      Bridge.IsRatMat _ γ γE → ∀ v, g (rhoVr tauL (lamL i) γE v) = rhoVr tauL (lamL i) γE (g v) := by
    intro γ γE hγ v
    apply hinj
    rw [← hcg, (h'.mapL i).1 γ γE hγ, hcg, (h.mapL i).1 γ γE hγ]
  obtain ⟨a, ha⟩ := GlobalTheory.T.coefficientSpace_endomorphism_scalar_schur D.what₂.LL (lamL i) g (GlobalTheory.T.commutes_all_of_commutes_rationalUnitaryPoints D _ tauL h.tauL_ok (lamL i) g hcomm)
  have hea : ∀ x, e x = a • e₂ x := fun x => by
    have h1 := ha (e₂ x)
    simpa [g] using h1
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (A.MtCSD i A.μ0).bV.index_nonempty
  have hx0 := (A.MtCSD i A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((A.MtCSD i A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    GlobalTheory.CoefUniq.mem_of_coords _ (bVV D.what₂.LL (lamL i)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hst : star a * a = 1 := by
    have hinj' := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (B.L i A.μ0).pres.coef_li
    have hp0 := GlobalTheory.CoefUniq.pair_ne_zero D.what₂.embLL _ hinj' _ (B.L i A.μ0).pres.coef_pair hx0
    refine GlobalTheory.CoefUniq.star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((B.L i A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice tauL (lamL i) _
      (GlobalTheory.RepsCompare.isLattice_hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl))
    refine GlobalTheory.CoefUniq.isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · have h1 := hL.span_eq_top
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := GlobalTheory.CoefUniq.pow_eq_one_of_cmMax hm hst hi
  exact ⟨a, ⟨n, hn, han⟩, fun F => by rw [hcg, ha, LinearMap.map_smulₛₗ]⟩

end GlobalTheory.CoefRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostDiagUniq

theorem eq_smul_diagInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ κ _ l hl hinv μ hμ
  exact GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ l hl hinv μ hμ

end GlobalTheory.HostDiagUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  first | exact @GlobalTheory.DilFlat.isSBHalf_dilFlat | exact GlobalTheory.DilFlat.isSBHalf_dilFlat | (intros; apply GlobalTheory.DilFlat.isSBHalf_dilFlat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIKStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 → content v (detPow C i k) = (κ : EReal) := by
  first | exact @GlobalTheory.detPow_content_const | exact GlobalTheory.detPow_content_const | (intros; apply GlobalTheory.detPow_content_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivariance
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem udat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R}
    {p q : UD σ J} (hp : p ∈ UDAt σ J ev) (hq : q ∈ UDAt σ J ev) : p * q ∈ UDAt σ J ev := by
  intro u hu
  have e : ((((p * q : UD σ J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))) - 1 =
      ((((p : UD σ J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) *
        (((q : UD σ J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) +
      ((((q : UD σ J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) := by
    simp [sub_mul]
  rw [e, smul_add, ← Matrix.smul_mul, hp u hu, hq u hu, Matrix.zero_mul, add_zero]

theorem udat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R} :
    (1 : UD σ J) ∈ UDAt σ J ev := by
  intro u _
  simp

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_hasSig (h.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero]

theorem mulLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (dd : DblCo σ X W) (omd : DblRep σ (n := n) W),
    IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → LocOps omd v →
    ∀ ιd, IsLinD ψ dd t b c ιd → ∀ cd, IsShapeD omd t c ιd cd →
    cd 1 = 1 ∧ ∀ p ∈ UDAt σ W.J (evFin F v), ∀ q ∈ UDAt σ W.J (evFin F v), cd (p * q) = cd p * cd q := by
  intro F E _ _ _ _ _ σ ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨φ0, hφ0, hne⟩ : ∃ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ιd φ ≠ 0 := by
    have hmem : (intM (Fv F v) (Fin n) (Fin d ⊕ Fin d)).indicator (1 : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ) ∈
        SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) := indicator_intM_mem_SB
    obtain ⟨φ, hφ, he⟩ := hI.bij.surjOn hmem
    refine ⟨φ, hφ, fun h => ?_⟩
    have h0 := congrFun he 0
    rw [h, Set.indicator_of_mem (fun i j => by simp)] at h0
    simp at h0
  obtain ⟨Z, hZ⟩ : ∃ Z, ιd φ0 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have comp : ∀ p q : UD σ W.J, ∀ φ φ₁ φ₂ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ,
      Acts (evFin F v) (omd q) φ φ₁ → Acts (evFin F v) (omd p) φ₁ φ₂ → Acts (evFin F v) (omd (p * q)) φ φ₂ := by
    intro p q φ φ₁ φ₂ hq hp r hr
    have h1 := hq r hr
    have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, h1 ▸ hS.pres q _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1, hp r hr1]
  refine ⟨?_, ?_⟩
  · have hA : Acts (evFin F v) (omd 1) φ0 φ0 := fun r _ => by rw [map_one, Module.End.one_apply]
    have e := congrFun (hD 1 udat_one φ0 hφ0 φ0 hφ0 hA) Z
    simp only [map_one, Units.val_one, Matrix.mul_one, Pi.smul_apply, smul_eq_mul] at e
    exact (mul_eq_right₀ hZ).mp e.symm
  · intro p hp q hq
    obtain ⟨φ₁, hφ₁, h1⟩ := hL q hq φ0 hφ0
    obtain ⟨φ₂, hφ₂, h2⟩ := hL p hp φ₁ hφ₁
    have e1 := hD q hq φ0 hφ0 φ₁ hφ₁ h1
    have e2 := hD p hp φ₁ hφ₁ φ₂ hφ₂ h2
    have e3 := hD (p * q) (udat_mul hp hq) φ0 hφ0 φ₂ hφ₂ (comp p q φ0 φ₁ φ₂ h1 h2)
    have hG : GlobalTheory.SplitFlip.invT (locMatD t c (p * q)) =
        GlobalTheory.SplitFlip.invT (locMatD t c p) * GlobalTheory.SplitFlip.invT (locMatD t c q) := by
      rw [map_mul, map_mul]
    set G := GlobalTheory.SplitFlip.invT (locMatD t c (p * q))
    have hY := congrFun (e3.symm.trans e2) (Z * (G⁻¹).val)
    rw [e1] at hY
    simp only [Pi.smul_apply, smul_eq_mul] at hY
    have k1 : Z * (G⁻¹).val * G.val = Z := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Z * (G⁻¹).val * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val * (GlobalTheory.SplitFlip.invT (locMatD t c q)).val = Z := by
      rw [Matrix.mul_assoc, ← Units.val_mul, ← hG, k1]
    rw [k1, k2, ← mul_assoc] at hY
    exact mul_right_cancel₀ hZ hY

end GlobalTheory.DblScalDet

open GlobalTheory.DblScalDet in

theorem GlobalTheory.DblScal.scalar_factors_through_det : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨h1, hmul⟩ := mulLaw F E σ B.ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  have hJ : W.J.det ≠ 0 := det_ne_zero_of_skew hP.skew
  have hinj := GlobalTheory.T.local_matrix_map_injective F E σ hP.base.cm d W.J hJ v t c
  have hsurj := GlobalTheory.T.local_matrix_map_surjective F E σ hP.base.cm d W.J hJ hP.skew.skew v t c
  have hex : ∀ A : GL (Fin d ⊕ Fin d) (Fv F v), ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = A :=
    fun A => hsurj (Set.mem_univ A)
  choose sec hsU hs using hex
  have hsm : ∀ A A', sec (A * A') = sec A * sec A' := fun A A' =>
    hinj (hsU _) (udat_mul (hsU A) (hsU A')) (by rw [hs, map_mul, hs, hs])
  have hs1 : sec 1 = 1 := hinj (hsU 1) udat_one (by rw [hs, map_one])
  let f : GL (Fin d ⊕ Fin d) (Fv F v) →* ℂˣ :=
    { toFun := fun A => ⟨cd (sec A), cd (sec A⁻¹),
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, mul_inv_cancel, hs1, h1],
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, inv_mul_cancel, hs1, h1]⟩
      map_one' := Units.ext (by simp only [hs1, h1, Units.val_one])
      map_mul' := fun A A' => Units.ext (by simp only [Units.val_mul]; rw [hsm, hmul _ (hsU _) _ (hsU _)]) }
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) := finSumFinEquiv
  let rr : GL (Fin (d + d)) (Fv F v) →* GL (Fin d ⊕ Fin d) (Fv F v) :=
    Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e.symm).toMonoidHom
  have h2 : (2 : Fv F v) ≠ 0 := fun h => two_ne_zero (α := F) ((algebraMap F (Fv F v)).injective (by rw [map_ofNat, h, map_zero]))
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (k := Fv F v) h2 (f.comp rr)
  refine ⟨fun x => (χ x : ℂ), fun p hp => ?_⟩
  have hp' : sec (GlobalTheory.DblScal.locMatD t c p) = p := hinj (hsU _) hp (hs _)
  set A := GlobalTheory.DblScal.locMatD t c p
  let A' : GL (Fin (d + d)) (Fv F v) := Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e).toMonoidHom A
  have hA : rr A' = A := Units.ext (by ext i j; simp [rr, A'])
  have hdet : Matrix.GeneralLinearGroup.det A' = GlobalTheory.SplitFlip.gdet A :=
    Units.ext (by simp [A', GlobalTheory.SplitFlip.gdet, Matrix.det_reindex_self])
  have hf := hχ A'
  rw [MonoidHom.comp_apply, hA, hdet] at hf
  calc cd p = cd (sec A) := by rw [hp']
    _ = ((f A : ℂˣ) : ℂ) := rfl
    _ = _ := by rw [hf]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentityStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  first | exact @GlobalTheory.DblShape.shape_dbl | exact GlobalTheory.DblShape.shape_dbl | (intros; apply GlobalTheory.DblShape.shape_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalVanishingStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_vanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  first | exact @GlobalTheory.DblSiegelScal.scalar_siegel | exact GlobalTheory.DblSiegelScal.scalar_siegel | (intros; apply GlobalTheory.DblSiegelScal.scalar_siegel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EV0MemGoodFRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eV0_mem_goodF_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), eV0 p t y ∈ (p.P.A3.A.fam.R t).goodF p.P.A3.A.fam.X := by
  first | exact @GlobalTheory.BigTop.Fun.eV0_mem_goodF | exact GlobalTheory.BigTop.Fun.eV0_mem_goodF | (intros; apply GlobalTheory.BigTop.Fun.eV0_mem_goodF <;> assumption)
end

