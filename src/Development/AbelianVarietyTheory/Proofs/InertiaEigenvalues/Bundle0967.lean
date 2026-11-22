import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstants
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelLiftBaseOfRealisationLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwistLiftW

theorem isLevelLift_base_of_realisation_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  intro D X E Y i j b g κ h
  have P := Y.Z.pin
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hβ := P.frT i j b
  have hP := P.Pg i j b
  have tri : ∀ (PP : Pl D.host.E) (r t : ℕ), r = (Wc D j).rank → ∀ x : GL (Fin (Wc D j).rank) (kP PP),
      x ∈ blockTri (blkOf r t) := fun PP r t hr x => mem_blockTri.2 fun a c hac => by
    have ha : a.val < r := lt_of_lt_of_eq a.2 hr.symm
    have e : blkOf r t a = 0 := if_pos ha
    exact absurd (lt_of_lt_of_eq hac e) (Nat.not_lt_zero _)
  refine ⟨h.1, mem_parLev.2 ⟨parLev_UA h.2.1, ?_, fun PP _ => tri PP _ _ rfl _,
    fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
  · rw [hβ]; exact parLev_St h.2.1
  · funext PP
    obtain ⟨PP, hPP⟩ := PP
    have hPP' : PP ∈ X.R.Pg := hP ▸ hPP
    refine Units.ext (Matrix.ext fun a c => ?_)
    have e1 := P.grp i j b (X.cG (X.R.eG g)) PP hPP hPP' a c
    rw [MulEquiv.symm_apply_apply] at e1
    refine Eq.trans ?_ e1.symm
    rw [← h.2.2, hβ]
    have e2 := upper_block_val_submatrix (le_refl _) (blockTri_blkOf_le _ 1 (tri PP _ 1 rfl (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    have e3 := upper_block_val_submatrix rW.ge (blockTri_blkOf_le _ 1 (tri PP _ 1 rW.symm (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    exact (congrFun (congrFun e2 a) c).trans (congrFun (congrFun e3 (Fin.cast rW a)) (Fin.cast rW c)).symm

end GlobalTheory.TwistLiftW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstantsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → ∃ (ζ : ℂ) (z : G), IsRoot1 ζ ∧ z ∈ Subgroup.center G ∧ ∀ (t : Tp) (h : M.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (M.bad t) J' (M.Lh t) (M.gam t) (M.vol t) → ∀ (y : (R.HV i (tup t)).H) (x : M.Cl' t → VsV D i M.c'.F), Place R i (tup t) h M.c0' y x → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M t x f → ∀ g : GA D (Wc D i), ph i * R.thF i (tup t) y (v₀ i (sg0 D A)) g = ζ * T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 := by
  first | exact @GlobalTheory.SerAll.ser_at_core_constants | exact GlobalTheory.SerAll.ser_at_core_constants | (intros; apply GlobalTheory.SerAll.ser_at_core_constants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Topology
open Filter

namespace GlobalTheory.LatFixMod

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem eventually_keep_cong (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1,
      (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T p.1 p.2 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T p.1 p.2 u = u + N • l := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef
  have hfg := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  obtain ⟨G, hG, hGl, hgen⟩ := hfg
  have hev := GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  have hall := (Filter.eventually_all_finite hG).2 fun u hu =>
    hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN
  filter_upwards [hev.1, hall] with p hk hp
  refine ⟨hk, fun w hw => ?_⟩
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l}
      zero_mem' := ⟨0, L.zero_mem, by
        have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
        rw [zero_smul, zero_smul] at this
        rw [this, smul_zero, add_zero]⟩
      add_mem' := by
        rintro a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩
        refine ⟨la + lb, L.add_mem hla hlb, ?_⟩
        rw [GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]
        abel
      neg_mem' := by
        rintro a ⟨la, hla, ea⟩
        refine ⟨-la, L.neg_mem hla, ?_⟩
        have h0 := GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)
        have hz : actO S T p.1 p.2 (0 : WO S T) = 0 := by
          have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
          rw [zero_smul, zero_smul] at this
          rw [this]
        rw [add_neg_cancel, hz, ea] at h0
        rw [smul_neg]
        have : actO S T p.1 p.2 (-a) = -(a + N • la) := (neg_eq_of_add_eq_zero_right h0.symm).symm
        rw [this, neg_add] }
  refine hgen U (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
  show actO S T p.1 p.2 _ = _
  rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]

def KeepMod (S T : HSp D) (L : AddSubgroup (WO S T)) (N : ℕ) (x : GA D S) : Prop :=
  (∀ u ∈ L, actO S T x 1 u ∈ L) ∧ ∀ u ∈ L, ∃ l ∈ L, actO S T x 1 u = u + N • l

theorem exists_open_keep_cong : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J →
      (∀ u : WO S T, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
        actO S T x 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T x 1 u = u + N • l := by
  intro D S T ΛS ΛT hS hT N hN
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hev := eventually_keep_cong S T ΛS ΛT hS hT N hN
  have t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1
    exact this
  have t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1
    rwa [inv_one, Prod.mk_one_one] at this
  have hx : ∀ᶠ x in 𝓝 (1 : GA D S),
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹ :=
    (t1.eventually hev).and (t2.eventually hev)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k →
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹ := by
    by_contra hne
    have hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧
        ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
          KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹) :=
      fun n => by
        by_contra h
        exact hne ⟨n, fun k hk hc => by
          by_contra h'
          exact h ⟨k, hk, hc, h'⟩⟩
    choose k hk hkc hkne using hne'
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hx).exists
    exact hkne n hn
  obtain ⟨n, hn⟩ := key
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S x := congrArg Subtype.val e
  have hc : GlobalTheory.Member.FinCong S n.factorial x := by
    have := hk'.2
    unfold GlobalTheory.Member.FinCong at this ⊢
    rw [← e']
    exact this
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hn x hxf hc
  refine ⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩
  have e2 := GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u
  rw [inv_one] at e2
  rw [← e2]
  exact h3 _ hu

end GlobalTheory.LatFixMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.RealPtsFock

open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.RealFockAction GlobalTheory.VacuumCharacter

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_vac_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hF.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hF.onbS τ))
  have hT := hF.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hF.onbT τ
    rw [← hsig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta heta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (B.mu * ψ.chi * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hinf τ) (heta.2.2.2 τ) 1) (heta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hF.vac.2.inf
  have hBS := fun τ => onb_posDef (hF.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac_of hF hsig hsigOK heta hinf hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hF.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hF.cartT
      (fun τ => (onb_laws (by have := hF.onbT τ; rwa [← hsig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem mem_UH_of_conj {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hB : IsUnit B.det)
    (hg : B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ) : g ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have h3 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : (B⁻¹ * g * B)ᴴ * (B⁻¹ * g * B) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hg
    rwa [Matrix.star_eq_conjTranspose] at this
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  have hgB : g = B * (B⁻¹ * g * B) * B⁻¹ := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  show gᴴ * G * g = G
  calc gᴴ * G * g = (B⁻¹)ᴴ * ((B⁻¹ * g * B)ᴴ * (Bᴴ * (B⁻¹)ᴴ) * (B⁻¹ * B) * (B⁻¹ * g * B)) * B⁻¹ := by
        conv_lhs => rw [hgB, hG]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h3, h2, Matrix.mul_one, Matrix.mul_one, hU, Matrix.mul_one, ← hG]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem om_ptP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) {ψ : Twist D Circle} {t : T0}
    (ht : IsTupOf R B ψ t) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (B.act u P) := by
  have hL := hC.lev
  have hW := hC.thP.ωP i A.μ0
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  have hsig : ∀ τ, (B.w.p τ, B.w.q τ) = (Wc D i).sig (tauE D τ) := fun τ => by rw [h.p, h.q]
  have heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta := by
    rw [h.eta]
    exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT
      (hev.add_odd (rW ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  have hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    rw [h.mu_mul ht, h.exponent]
    exact (GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hL i t τ).mu
  rw [hpt, hpt]
  exact om_fock_of (GlobalTheory.ConjTwist.Test.frame_good hC h) hsig (D.sp.W_sig _) heta hinf hω hf' hv' hu P

theorem real_points_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D i).rank) (BS : GlobalTheory.ExportSeries.GLR D (Vc D i).rank) (r : ↥(GinfC (Vc D i)) →* GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ (u : ↥(GinfC (Vc D i))) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ωP i t ((u : GA D (Vc D i)), 1) (R.ptP i t P) = R.ptP i t (GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r u) P)) ∧ (∀ (u : ↥(GinfC (Vc D i))) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r u) τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ (∀ g : GlobalTheory.ExportSeries.GLR D (Vc D i).rank, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) → ∃ u, r u = g) ∧ (∀ (τ : D.what₂.Tau) (j : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε τ j = decide ((j : ℕ) < w.p τ)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hC := hG.core
  obtain ⟨B, hb, ht, rfl⟩ : ∃ B : Base (Vc D i) (Wc D i), BaseOf R i B ∧ IsTupOf R B (tupTwist R t) t ∧
      B = baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩ :=
    ⟨_, baseOf_baseAt R hC.models.BV _ _, isTupOf_tupTwist R hC.models.BV t _, rfl⟩
  have hF := GlobalTheory.ConjTwist.Test.frame_good hC hb
  have hθ : IsInfFam R.θ := hF.vac.2.inf
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_posDef (hC.models.BV i τ)
  have eu : ∀ (g : GLR D (Vc D i).rank) τ,
      (inBasis (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS g τ).val = (R.BV i τ)⁻¹ * (g τ).val * R.BV i τ :=
    fun g τ => by
      rw [← hb.BS τ, ← Matrix.coe_units_inv]
      rfl
  refine ⟨liftWeight D i, (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS,
    (realGL R.θ (Vc D i)).comp (GinfC (Vc D i)).subtype, fun u P => om_ptP hC hb ht u.2 P, fun u τ => ?_, fun g hg => ?_,
    fun τ j => hC.models.order i τ j⟩
  · rw [eu]
    exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ (u : GA D (Vc D i)) τ)
  · have hU : ∀ τ, (g τ).val ∈ Formalism.QuantumDeterminants.UH (gramAt D (Vc D i) τ) := fun τ => by
      refine mem_UH_of_conj (hBS τ) ?_ (by rw [← eu]; exact hg τ)
      rw [← hb.BS τ]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    refine ⟨⟨GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) (fun τ => (g τ).val), list_prod_mem fun x hx => ?_⟩, ?_⟩
    · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
      exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
    · funext ρ
      refine Units.ext ?_
      change infMat D.sp.cm.sig (Vc D i).gram (R.θ ρ) (GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) fun τ => (g τ).val) = (g ρ).val
      rw [GlobalTheory.AdelicScalar.realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ _ hU ρ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

end GlobalTheory.RealPtsFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarLinearSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.RealFockSubst

open scoped ComplexOrder

theorem om_ptP_subst : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (t : T), ∀ u ∈ GinfC (Vc D i), ∃ (c : ℂ) (g : GLR D (Vc D i).rank), ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = c • R.ptP i t (fockSubst (pS D i) g P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG i t u hu
  have hC := hG.core
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨c, U, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := pS D i) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf]

end GlobalTheory.RealFockSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  first | exact @GlobalTheory.SupLaw.hkComm_of_ties | exact GlobalTheory.SupLaw.hkComm_of_ties | (intros; apply GlobalTheory.SupLaw.hkComm_of_ties <;> assumption)
end

