import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransition
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

theorem mem_prime_dual_iff {K : Type} [Field K] (p : Ideal (DualNumber K)) [hp : p.IsPrime] (x : DualNumber K) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra h
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  · intro h
    have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext h rfl
    have h2 : x * x = 0 := by rw [hx, TrivSqZeroExt.inr_mul_inr]
    exact (hp.mem_or_mem (h2 ▸ p.zero_mem)).elim id id

theorem dual_pt_eq {K : Type} [Field K] (p q : Sp (DualNumber K)) : p = q := by
  apply PrimeSpectrum.ext
  ext x
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hq : q.asIdeal.IsPrime := q.isPrime
  exact (mem_prime_dual_iff (K := K) p.asIdeal x).trans (mem_prime_dual_iff (K := K) q.asIdeal x).symm

theorem top_le_of_red {K : Type} [Field K] {T : Scheme.{0}} (φ : DualNumber K →+* K) (w : Sp (DualNumber K) ⟶ T)
    {V : T.Opens} (h : ⊤ ≤ (spMap φ ≫ w) ⁻¹ᵁ V) : ⊤ ≤ w ⁻¹ᵁ V := by
  intro p _
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e : p = spMap φ q := dual_pt_eq _ _
  have hq := h (Set.mem_univ q)
  rw [e]
  exact hq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem ev_resU {T : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ T) {U V : T.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ z ⁻¹ᵁ V) (hU : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(T, U)ˣ) :
    GlobalTheory.FlagMod.ev z V hV (res e u).val = GlobalTheory.FlagMod.ev z U hU u.val :=
  GlobalTheory.FlagMod.ev_res z e hV hU u.val

theorem tAt_congr {K : Type} [CommRing K] (k k' : X.F.J) {w w' : Sp K ⟶ X.YY} (e : w = w')
    (h : ⊤ ≤ w ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) (h' : ⊤ ≤ w' ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    X.F.TAt k k' w h = X.F.TAt k k' w' h' := by
  subst e; rfl

open Classical in

theorem ev_div_g (i i' : M.K.bundle.ι) (k k' : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X)
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k')))
    (hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i')) (hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k)
                 (i', flagIdx M _ k')).val =
      GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
        (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val := by
  set e := exOf Dw (FlagTan.kap Dw) 0
  have hL : ⊤ ≤ z ⁻¹ᵁ (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) ⊓
      ((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k')) := fun p hp => ⟨(hg hp).1.2, (hg hp).2.2⟩
  have hh1 : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ ((L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k PUnit.unit) ⊓
      (L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k' PUnit.unit)) := fun p hp => ⟨mem_pIdx.2 (hh hp).1, mem_pIdx.2 (hh hp).2⟩
  have hh2 : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := fun p hp => hh hp
  have eL : GlobalTheory.FlagMod.ev z _ hL (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).g (flagIdx M _ k) (flagIdx M _ k')).val =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix)).val := by
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ z hL hh1]
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ (z ≫ M.σ) hh1 hh2]
    refine (X.F.ev_LL_g e k k' _ hh2).trans ?_
    rw [tAt_congr k k' (Category.assoc _ _ _) hh2 hh]
  have ei : ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix) : Kˣ) : K)⁻¹ =
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ e ix : Kˣ) : K) := by
    rw [← Units.val_inv_eq_inv_val, ← Finset.prod_inv_distrib]
    simp only [zpow_neg, inv_inv]
  dsimp only [LB.div]
  refine ((GlobalTheory.FlagMod.ev z _ hg).map_mul _ _).trans (congrArg₂ (· * ·) (ev_resU z _ hg hK _)
    ((map_units_inv (GlobalTheory.FlagMod.ev z _ hg) _).trans ?_))
  refine (congrArg Inv.inv (ev_resU z _ hg hL _)).trans ?_
  rw [eL, ei]

theorem red_comp_eq {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P : FrPt Xo c K}
    (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) :
    spMap (FlagTan.red c K).toRingHom ≫ zw = z := by
  have hx : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun p hp => by
    have := ho hp
    rw [M.off_eq] at this
    exact this
  have h1 : (spMap (FlagTan.red c K).toRingHom ≫ zw) ≫ M.σ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z)]
    simp only [Category.assoc]
    have e1 : zw ≫ M.σ ≫ inc₀ X Z = X.ptY w := hl
    have e2 : z ≫ M.σ ≫ inc₀ X Z = X.ptY P := hP
    rw [e1, e2]
    exact X.ptY_frMap hw
  exact (M.existsUnique_lift (z ≫ M.σ) hx).unique h1 rfl

theorem top_le_of_isDef {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {P : FrPt Xo c K} (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) {V : M.X.Opens} (hV : ⊤ ≤ z ⁻¹ᵁ V) :
    ⊤ ≤ zw ⁻¹ᵁ V :=
  top_le_of_red _ zw (by rw [red_comp_eq M z ho hP hw zw hl]; exact hV)

open Classical in

theorem ksRel_of_ksRel {i i' : M.K.bundle.ι} {k k' : X.F.J} {K : Type} [Field K] {z : Sp K ⟶ M.X}
    (hs : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) (hs' : ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k')
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) {x' : K}
    (hx' : KSRel M i' k' z x') :
    KSRel M i k z (GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g
      (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x') := by
  intro _ P Q t v zv O hO g hz hzv hk hQ ht hv hl
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun p hp => (hs hp).1
  have hi' : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i' := fun p hp => (hs' hp).2.1
  have hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i') := fun p hp => ⟨(hs hp).2.1, (hs' hp).2.1⟩
  have hk' : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k' := fun p hp => mem_pIdx.1 (mem_pIdx.1 (hs' hp).2.2)
  have hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := GlobalTheory.FlagMod.le_preimage_inf hk hk'
  have hlies := hQ.lies
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd Q) hlies.1 k' hk'
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  have hB := hQ.frBor hQ' hh
  have ht' := g1 _ _ _ _ _ (g2 _ _ _ hB) ht
  have hP : z ≫ toFlag M = X.ptY P := FlagCover.eq_ptY (hlies.frBor ht)
  have hzv' : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := fun b =>
    GlobalTheory.FlagMod.le_preimage_inf (hzv b) (top_le_of_isDef M z ho hP (hv.isDef b) (zv b) (hl b) hi')
  have hz' : ⊤ ≤ z ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := GlobalTheory.FlagMod.le_preimage_inf hz hi'
  have key := hx' P Q' _ v zv (O ⊓ M.K.bundle.U i') inf_le_right (fun a => resG M.X inf_le_left (g a)) hz' hzv' hk'
    hQ' ht' hv hl
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) (O ⊓ M.K.bundle.U i') (hzv' _)
      (resG M.X inf_le_left (g a))).snd) = Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd := by
    ext a b
    simp only [Matrix.of_apply]
    rw [evalPt_res]
  rw [hdet] at key
  have hJ : evalPt z O hz (M.K.jacobian i hO g) = GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) := by
    rw [← evalPt_res z inf_le_left hz hz', CanonLB.resG_jacobian,
      CanonLB.jacobian_change _ i i' (inf_le_left.trans hO) inf_le_right, map_mul]
    congr 1
    exact evalPt_res z _ hK hz' _
  rw [ev_div_g M i i' k k' z hg hK hh, hJ]
  have hu : (∏ ix, ((X.F.TAt k k' (z ≫ toFlag M) hh)⁻¹ * t) ix ^ exOf Dw (FlagTan.kap Dw) 0 ix) =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)⁻¹ *
        ∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ix _ => ?_
    rw [Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow]
  rw [hu, Units.val_mul] at key
  have hTT := Units.mul_inv (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)
  linear_combination (GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K)) * key +
    ((∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K) * GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) * hTT

end GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS in

theorem GlobalTheory.CompHS.ksRel_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i i' k k' K _ z hs hs' hg x x' hx hx'
  exact (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS i k K z hs).1 x _ hx (ksRel_of_ksRel M hs hs' hg hx')
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
section
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.DivisionValues (vw)

namespace GlobalTheory.RhoLowProof

theorem meanVal_lower {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) {c : K} (hc : c ≠ 0) {l : ℕ} (hl : l.Prime)
    {w : Formalism.PairingDivisionLocalBalance.Pl K} (hw : (l : 𝓞 K) ∈ w.asIdeal) {m : ℕ}
    (h : IntAt l ((l : ℂ) ^ m * (σ c * β))) :
    -((m : ℝ) * (vw w (l : K) : ℝ)) ≤ (vw w c : ℝ) + meanVal_vw w p :=
  GlobalTheory.T.meanValuation_ge_of_integral_at_prime σ hp hβ hc hl hw h

theorem classZetaVals_unique {E : Type} [Field E] [NumberField E] {k : ℕ} (hk : 2 ≤ k) {z z' : ClassGroup (OF E) → ℚ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z) (h' : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z') : z = z' :=
  GlobalTheory.T.partialZeta_values_at_neg_int_unique hk h h'

section Twist
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

open Classical in

theorem twist_val {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) :=
  GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter G hL t i j hs

open Classical in

theorem squareTopTwistPlaces_coprime_splitPlaces {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) :=
  GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under G hL t

theorem twist_ram {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (nuH G t i j).UnrAt P :=
  GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place G hL t i j

open Classical in

theorem twist_prime (t : T) {l : ℕ} (hl : l.Prime) {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL} (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQ : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    ∀ q ∈ (GlobalTheory.SqTop.twPl G t).image (fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal :=
  GlobalTheory.T.twist_places_under_prime_not_mem_of_norm_coprime G t hl hlw hQ

end Twist

theorem vw_pow {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {z : K} (hz : z ≠ 0) (n : ℕ) :
    vw w (z ^ n) = n * vw w z := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem over_under {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Over P (P.under (OF E)) := rfl

set_option maxHeartbeats 1000000 in
open Classical in

theorem core (hTD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E) (hab : IsAbelianGalois ℚ D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ halfRank D i j)
    (t : T) (Λ Λ₀ : ℂ → ℂ) (z : D.what₂.LL) (zd : Bool → D.what₂.LL) (g : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℤ) (n : ℕ → ℝ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) (hz : D.what₂.embLL z * Λ₀ s = Λ s)
    (htv : IsTorVal G μ₀ i j s zd g) (hden : IsDenom G i j s n)
    (w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL) (l : ℕ) (hl : l.Prime) (hlw : (l : 𝓞 D.what₂.LL) ∈ w.asIdeal)
    (hQw : (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal) :
    -(n l * (vw w (l : D.what₂.LL) : ℝ)) ≤ ((vw w z + g w : ℤ) : ℝ) := by
  haveI := hcm
  haveI := hab
  obtain ⟨x, hx, hx0, -, Λl, p, hΛl, hp, hg⟩ := htv
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1

  have e0 : x = Λ₀ s := by
    have h := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
      (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
    simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at h
    exact hx.2.unique h

  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hQval := twist_val G hL t i j hs2
  have hQaux := squareTopTwistPlaces_coprime_splitPlaces G hL t
  have hQram := twist_ram G hL t i j
  have hQpr := twist_prime G t hl hlw hQw
  rw [← hQdef] at hQval hQaux hQpr
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (over_under (Pq q)).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)
  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hQval
    hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]
  have hpic : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsPicChar (condQ (condF G.pl) Q) (Lc.xiH t) := by
    obtain ⟨k, hk, hko⟩ := hL.xi_fin t
    refine ⟨fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y, fun u hu => ?_⟩
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hQval u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hx.1 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a

  obtain ⟨zc, hzc, H⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hfd hs1
  have hV := ((H (kap D sc.cGap i j s) (condF G.pl) Λl (nuH G μ₀ i j) hbc hΛl hx.1) l hl Q hQaux hQpr).2
    (Lc.xiH t) (Λ s) hpic (hnu ▸ htor)
  obtain ⟨zc', hzc', hn⟩ := hden
  obtain rfl : zc = zc' := classZetaVals_unique (by omega) hzc hzc'
  set B := GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) zc l with hB
  set N := ⌈B / 12⌉₊ with hN
  have hnl : n l = N := by rw [hn l hl]
  have hInt := hV (12 * N : ℕ) 1 one_pos (by
    push_cast
    have := Nat.le_ceil (B / 12)
    linarith)

  have hv0 : G.pl.v0 ∉ Q := fun h => by
    obtain ⟨P, hP, e⟩ := hex _ h
    have hP' : P ∈ Lc.Q t := by
      simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter, locPl, Finset.mem_union] at hP
      exact hP.1.resolve_left hP.2
    exact G.pl.levelPlace_ne_basePlace t P hP' e
  have hram0 : ¬ (nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
    have h1 := (hQval.2.2.2 G.pl.v0 (G.pl.w G.pl.v0) ((over_under _).trans (congrArg HeightOneSpectrum.asIdeal (G.pl.w_over _ (Finset.mem_insert_self _ _))))).2 hv0
    rw [GlobalTheory.FunObj.SqNum.Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), condExp, if_pos rfl] at h1
    exact h1.not_unrAt one_ne_zero
  have hΛs : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hQval.1
    (GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt hram0) hΛ (by simpa using (by exact_mod_cast hs1 : (1 : ℝ) ≤ s))
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΛs (by rw [← hz, map_zero, zero_mul])

  have hbeta : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl (Λ s) =
      D.what₂.embLL (z ^ 12) * beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x := by
    rw [← hz, ← e0, beta, beta, map_pow]
    ring
  have hβ0 : beta D.host.E D.host.d s (kap D sc.cGap i j s) Λl x ≠ 0 := by
    rw [beta]
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hx0)) (pow_ne_zero _ (latDisc_ne_zero Λl))
    exact_mod_cast (cmValueConst_pos D.host.E (hfd.1.pos) (by omega) _).ne'
  rw [hbeta, pow_one, zpow_natCast] at hInt
  have key := meanVal_lower D.what₂.embLL hp hβ0 (pow_ne_zero 12 hz0) hl hlw hInt
  rw [vw_pow w hz0] at key
  have h2 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ (vw w z : ℝ) + meanVal_vw w p / 12 := by
    push_cast at key ⊢
    linarith
  have h3 := GlobalTheory.FunObj.SqNum.le_add_truncZero h2
  rw [hnl, hg w]
  have h4 : ((-(N * vw w (l : D.what₂.LL)) : ℤ) : ℝ) ≤ ((vw w z + GlobalTheory.LeafRestExamples.truncZero (meanVal_vw w p / 12) : ℤ) : ℝ) := by
    exact_mod_cast h3
  push_cast at h4 ⊢
  linarith

theorem rhoLow_holds : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.RhoLow := by
  intro hTD hF _
  obtain ⟨CF0, hF⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, hab, hfd, hbc, -⟩ := hF C hC D large₂ he hx hR T Lc μ₀ hL G
  intro i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw
  exact core hTD hL G hcm hab hfd hbc i j s hs1 hs2 t Λ Λ₀ z zd g n hΛ hΛ₀ hz htv hden w l hl hlw hQw

end GlobalTheory.RhoLowProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearForm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
end

