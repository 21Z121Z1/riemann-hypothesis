import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
open GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.AdTh

namespace GlobalTheory.Mem.R3.Rw.GeoTies

theorem eq_of_span {H ι X : Type} [AddCommGroup H] [Module ℂ H] {M : ι → Type} [∀ t, AddCommGroup (M t)] [∀ t, Module ℂ (M t)]
    (θ : H →ₗ[ℂ] MultilinearMap ℂ M (X → ℂ)) (v : ∀ t, M t) (a b : X) (c : ℂ) {S : Set H} (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ y ∈ S, θ y v a = c * θ y v b) (y : H) : θ y v a = c * θ y v b := by
  have hy : y ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [map_add, MultilinearMap.add_apply, Pi.add_apply]
    linear_combination h + h'
  | smul a y _ h =>
    simp only [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * h

theorem span_image {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H'] (e : H ≃ₗ[ℂ] H') {S : Set H}
    (hS : Submodule.span ℂ S = ⊤) : Submodule.span ℂ (e '' S) = ⊤ := by
  have := congrArg (Submodule.map (e : H →ₗ[ℂ] H')) hS
  rwa [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def adOver (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c')
    (g : GA D (Wc D i)) : ℂ :=
  cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

theorem adOver_of_isBC (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) {m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c}
    (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) : adOver O cc f g = ∑ k, (as k : ℂ) * O.phi cc (fs k) g := by
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h (O.dict g).1 (O.dict g).2
  refine (congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem adOver_act (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hn : κ.n = (Vc D i).rank)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hE : O.EquivAt κ cc)
    {z : G} {k : GA D (Wc D i)} (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k)
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ cuspOver O κ) (g : GA D (Wc D i)) :
    adOver O cc (actLev O.c' O.lev2 z f) g =
      (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ)) * adOver O cc f (g * k) := by
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC
  rw [adOver_of_isBC O cc h1, adOver_of_isBC O cc hBC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hE z k hk (fs l) (by rw [hn]; exact hfs l)).2 g]
  ring

end One

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m}

def LiftIsSum (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (ζ : ℂ) (y : (R.HV i A.μ0).H) : Prop :=
  ∃ h J x f, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ Place R i A.μ0 h O.c0' y x ∧
    f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
    ∀ q : AutQ (Wc D i), R.thF i A.μ0 y v₀ q.out =
      ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out

set_option maxHeartbeats 2000000 in

theorem oneMapOf_of_span (hR : PreChar R) (hchi : R.grp_chiW) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hU : ∀ k, ‖cE k‖ = 1) (hE : O.EquivAt (κ i) cE) {z : G} (hz : z ∈ Subgroup.center G) {ζ : ℂ}
    (hζL : ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange) (hζ : ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1)
    (hS : Submodule.span ℂ {y | LiftIsSum O (κ i) (v₀ i (sg0 D A)) cE z ζ y} = ⊤) :
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) cE 1 := by
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A T.Q.c.F R hR.lev hR.fam hR.models hR.thP
  have hn := PhaseOne.wt_n hT i
  obtain ⟨cc₀, -, u, -, -, hser, -⟩ := exists_ccIs_equivAt_serOf_tie D G Pl0 T0 A T R κ v₀ hR hT hio i _ _ O hP
  generalize u • cc₀ = cc at hser
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i _ _ O hP ()
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ) :=
    ⟨_, rfl⟩
  have hcc : ∀ c, cc c ≠ 0 := fun c => norm_ne_zero_iff.1 ((hser.1 c).trans_ne one_ne_zero)
  have key : ∀ h J x f y, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) → Place R i A.μ0 h O.c0' y x →
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank → IsSum O () x f → ∀ g,
      ζ * s * adOver O cE (actLev O.c' O.lev2 z f) g = ζ * χ * (cE (O.dict (g * k)).1 / cc (O.dict (g * k)).1) *
        R.thF i A.μ0 y (v₀ i (sg0 D A)) (g * k) := by
    intro h J x f y hr hy hf hx g
    obtain ⟨f₁, hf₁, hx₁⟩ := hex x
    have e : f = f₁ := isSum_unique hP () hf ((mem_cusp _ _ _ _ _ _).1 hf₁).1 hx hx₁
    have h1 := adOver_act O hn hP.act.1 hE hk (e ▸ hf₁ : f ∈ cuspOver O (κ i)) g
    have h2 := (one_mul _).symm.trans (hser.2.2 () h J hr y x hy f hf hx (g * k))
    rw [h1, h2, ← hχ, ← hs, adOver]
    have := hcc (O.dict (g * k)).1
    field_simp
  have all : ∀ y (q : AutQ (Wc D i)), R.thF i A.μ0 y (v₀ i (sg0 D A)) q.out =
      ζ * χ * (cE (O.dict (q.out * k)).1 / cc (O.dict (q.out * k)).1) * R.thF i A.μ0 y (v₀ i (sg0 D A)) (q.out * k) := by
    intro y q
    refine eq_of_span (R.thF i A.μ0) _ _ _ _ hS (fun y hy => ?_) y
    obtain ⟨h, J, x, f, h1, h2, h3, h4, h5⟩ := hy
    rw [h5 q, ← hs]
    exact key h J x f y h1 h2 h3 h4 _
  have hid : GlobalTheory.PhaseRational.IdentityAt O (κ i) cE 1 := by
    obtain ⟨h, J, hr, -, hA, hPl⟩ := (hP.tuple ()).reps
    refine ⟨hU, norm_one, z, hz, fun t => ⟨ζ, hζL, hζ, fun x hx => ⟨hex x, fun f hf hc q => ?_⟩⟩⟩
    obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
    have h1 := (all _ q).trans (key h J x f _ hr hx₀ hf hc q.out).symm
    rw [one_mul, hA _ x hx₀]
    refine h1.trans ?_
    rw [hs, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)]
    rfl
  exact ⟨hE, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, hid⟩,
    GlobalTheory.PhaseRational.phRat_of_identity O (κ i) _ cE 1 () rfl hF hP hT.laws.toLawsM (hT.kap i (D.eTau.symm 1)).2.2 hchi
      hR.thP.thF_mem hR.thP.thG hE hid⟩

set_option maxHeartbeats 2000000 in

theorem lift_of_oneMapOf (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {ι x₀} (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1) :
    ∃ z ∈ Subgroup.center G, ∃ ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∃ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ ∀ y₀ : A.fam.amb.FL i A.μ0, ∃ x f,
        Place R i A.μ0 h O.c0' (jVx R i A.μ0 y₀) x ∧ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
        ∀ q : AutQ (Wc D i), R.thF i A.μ0 (jVx R i A.μ0 y₀) v₀ q.out =
          ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) q.out := by
  obtain ⟨-, ⟨-, -, -, -, -, z, hz, h1⟩, -⟩ := h
  obtain ⟨ζ, hζL, hζ, h1⟩ := h1 ()
  obtain ⟨h, J, hr, hPx, hA, hPl⟩ := (hP.tuple ()).reps
  refine ⟨z, hz, ζ, hζL, hζ, h, J, hr, fun y₀ => ?_⟩
  obtain ⟨x, hx⟩ := hPx y₀
  obtain ⟨⟨f, hf, hc⟩, h2⟩ := h1 x ((hPl x).2 ⟨y₀, hx⟩)
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  refine ⟨x, f, hx, hf', hc, fun q => ?_⟩
  have h3 := h2 f hf' hc q
  rw [one_mul, hA _ x hx, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)] at h3
  exact h3

theorem exists_equiv_lift {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : HMod (Γ → W)} {H' : HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ θ' (e y) v' = θ y v := by
  cases h1; cases h2; cases h3; cases hH
  cases M; cases M'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hM
  dsimp only at a1 a2 a3 a4 a5 a6 a7
  cases a1; cases a2; cases a3; cases a4; cases a5; cases a6; cases a7
  have e1 : θ' = θ := eq_of_heq hθ
  have e2 : v' = v := eq_of_heq hv
  exact ⟨LinearEquiv.refl _ _, fun y => ⟨HEq.rfl, by rw [e1, e2]; rfl⟩⟩

theorem adOver_rulBC {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F) {lev} (hlev : lev = O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (g : GA D (Wc D i)) :
    cc (O.dict g).1 * (O.mu g * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z (GlobalTheory.FieldBC.rulBC hle f)) (O.dict g).1 (O.dict g).2) =
      adOver O cc (actLev O.c' O.lev2 z f) g := by
  subst hlev
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).2 a n z m _ fs _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle h₃ hf h)
  have e1 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1 (O.dict g).1 (O.dict g).2
  have e2 := GlobalTheory.PhaseRational.rdU_of_isBC h₃ (C.U ((i : ℕ) + 1)) (inC c) h2 (O.dict g).1 (O.dict g).2
  exact congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) (e2.trans e1.symm)

end GlobalTheory.Mem.R3.Rw.GeoTies

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameLift
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.FrameLiftAt

open Topology Filter Metric in

theorem exists_selection {X Y : Type} [MetricSpace X] [PseudoMetricSpace Y] (R : X → Y → Prop) (B : Set X)
    (b₀ : X) (x₀ : Y) (hB : B ∈ 𝓝 b₀) (h0 : R b₀ x₀) (hne : ∀ b ∈ B, ∃ x, R b x)
    (hl : ∀ V ∈ 𝓝 x₀, ∀ᶠ b in 𝓝 b₀, ∃ x ∈ V, R b x) :
    ∃ f : X → Y, (∀ b ∈ B, R b (f b)) ∧ ContinuousAt f b₀ := by
  have key : ∀ b, ∃ x, (b ∈ B → R b x ∧ dist x₀ x ≤ infDist x₀ {x | R b x} + dist b b₀) ∧ (b = b₀ → x = x₀) := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact ⟨x₀, fun _ => ⟨h0, by rw [dist_self, dist_self, add_zero]; exact infDist_nonneg⟩, fun _ => rfl⟩
    by_cases hbB : b ∈ B
    · have hp : 0 < dist b b₀ := dist_pos.2 hb
      obtain ⟨x, hx, hd⟩ := (infDist_lt_iff (x := x₀) (s := {x | R b x})
        (r := infDist x₀ {x | R b x} + dist b b₀) (hne b hbB)).1 (by linarith)
      exact ⟨x, fun _ => ⟨hx, hd.le⟩, fun h => absurd h hb⟩
    · exact ⟨x₀, fun h => absurd h hbB, fun _ => rfl⟩
  choose f hf hf0 using key
  refine ⟨f, fun b hb => (hf b hb).1, ?_⟩
  rw [ContinuousAt, hf0 b₀ rfl, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hB, hl _ (ball_mem_nhds x₀ (half_pos hε)), ball_mem_nhds b₀ (half_pos hε)] with b hb hx hbb
  obtain ⟨x, hx, hR⟩ := hx
  have h1 := (hf b hb).2
  have h2 : infDist x₀ {x | R b x} ≤ dist x₀ x := infDist_le_dist_of_mem hR
  rw [mem_ball] at hx hbb
  rw [dist_comm] at hx ⊢
  linarith

open Topology Filter GlobalTheory.GenericFrames in

theorem exists_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → ∀ b₀ ∈ B, ∃ x : (Fin m → ℂ) → (Fin T.m → ℂ), (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b) ∧ ContinuousAt x b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T hσ hM hN m B P hB hP b₀ hb₀
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e (F.Di k) (M.X k) (M.φ k) hσ (F.sig _).1 (F.sig _).2 hM.rank
    (hM.type k).1 (hM.type k).2 (hM.ef k) (fun _ => hN k)
  choose! x₁ hx₁ hr₁ using fun b (hb : b ∈ B) => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B := hB.mem_nhds hb₀
  have hPf : ∀ (x : Frame (M.X k).Ψ r) b,
      (∀ a j, pc (M.X k) x (M.φ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) → T.Pf x = P b := by
    intro x b h
    ext a j
    rw [T.per, hper, h]
  have key := GlobalTheory.PeriodLift.period_lift E r (M.X k) _ (𝓝 b₀) (x₁ b₀) x₁ (hx₁ b₀ hb₀) (hBn.mono hx₁)
    (fun v hv τ i => by
      obtain ⟨a, rfl⟩ : ∃ a, (M.φ k a : Fin r → E) = v := ⟨(M.φ k).symm ⟨v, hv⟩, by simp⟩
      obtain ⟨j, hj⟩ := idx.surjective (τ, i)
      obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
      change Tendsto (fun b => pc (M.X k) (x₁ b) (M.φ k a) _ _) _ (𝓝 (pc (M.X k) (x₁ b₀) (M.φ k a) _ _))
      rw [hr₁ b₀ hb₀]
      have hc : ContinuousAt (fun b => P b a j) b₀ :=
        (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
      exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₁ b hb a j).symm))
  refine exists_selection (fun b x => x ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co x) = P b) B b₀ (T.co.symm (x₁ b₀)) hBn
    ⟨by simpa using hx₁ b₀ hb₀, by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b₀ hb₀)⟩
    (fun b hb => ⟨T.co.symm (x₁ b), by simpa using hx₁ b hb,
      by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b hb)⟩) fun V hV => ?_
  have hV' : T.co.symm ⁻¹' V ∩ (M.X k).dom ∈ 𝓝 (x₁ b₀) :=
    inter_mem (T.co.symm.continuous.continuousAt hV) ((FourierCoefficientDomain.isOpen_dom (M.X k)).mem_nhds (hx₁ b₀ hb₀))
  filter_upwards [hBn, key _ hV'] with b hb hx
  obtain ⟨x, ⟨hxV, hxd⟩, hxx⟩ := hx
  refine ⟨T.co.symm x, hxV, by simpa using hxd, ?_⟩
  rw [T.co.apply_symm_apply]
  exact hPf _ _ fun a j => (hxx _ _ _).trans (hr₁ b hb a j)

end GlobalTheory.FrameLiftAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.GradedDiv

section Diag

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {g h : Mat m K}

theorem diag_mul (hg : Par m O g) (hh : Par m O' h) (τ : ι) (i : Fin (m τ)) :
    (g * h) τ i i = g τ i i * h τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h' | h'
  · rw [(hh τ).2.2.2 l i l.2 h', mul_zero]
  · rw [(hg τ).2.2.2 i l i.2 h', zero_mul]

theorem diag_ne_zero (hg : Par m O g) (τ : ι) (i : Fin (m τ)) : g τ i i ≠ 0 := by
  have := diag_mul hg hg.inv τ i
  rw [Mat.mul_inv hg.det_ne] at this
  exact left_ne_zero_of_mul_eq_one (this.symm.trans (Matrix.one_apply_eq i))

end Diag

theorem exists_div {F : Type} [Field F] {Y : GlobalTheory.ProjVar.Var F} {ι : Type} {m : ι → ℕ} (S : Fr (ratOf Y) m m)
    {A₀ : Mat m Y.Fn} (h₀ : A₀ ∈ S.S (genericPoint Y.X)) :
    ∃ gr : ∀ τ, Fin (m τ) → Y.Dv, ∀ y : Y.X, ∃ A ∈ S.S y, ∃ t : ∀ τ, Fin (m τ) → Y.Fnˣ,
      (∀ τ i, (A₀ * A⁻¹) τ i i = t τ i) ∧ (∀ τ i k, i < k → (A₀ * A⁻¹) τ i k = 0) ∧
        ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  have hP : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y →
      Par m ((ratOf Y).O (genericPoint Y.X)).toSubring (A₀ * A⁻¹) := fun hA =>
    (Fr.mem_iff (Fr.mem_genericPoint hA)).1 h₀
  let t : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y → ∀ τ, Fin (m τ) → Y.Fnˣ := fun hA τ i =>
    Units.mk0 _ (diag_ne_zero (hP hA) τ i)
  have hreg : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      RegAt y ((t hA' τ i : Y.Fn) / t hA τ i) := fun {y A A'} hA hA' τ i => by
    have hg := (Fr.mem_iff hA').1 hA
    have e := diag_mul (hP hA) hg τ i
    rw [← mul_assoc, mul_assoc A₀, Mat.inv_mul (Fr.det_ne hA), mul_one] at e
    have e' : (t hA' τ i : Y.Fn) / t hA τ i = (A * A'⁻¹) τ i i := by
      rw [div_eq_iff (t hA τ i).ne_zero, mul_comm]
      exact e
    rw [e']
    exact mem_O_ratOf.1 ((hg τ).1 i i)
  have hgerm : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      germOf y (t hA τ i) = germOf y (t hA' τ i) := fun {y A A'} hA hA' τ i => by
    rw [germOf_eq_iff, unitAt_iff (div_ne_zero (t hA' τ i).ne_zero (t hA τ i).ne_zero), inv_div]
    exact ⟨hreg hA hA' τ i, hreg hA' hA τ i⟩
  choose A hA using fun y : Y.X => S.nonempty y
  refine ⟨fun τ i => show cartierGroup Y.X from ⟨fun y => germOf y (t (hA y) τ i), fun y => ?_⟩,
    fun y => ⟨A y, hA y, t (hA y), fun _ _ => rfl, fun τ i k hik => (hP (hA y) τ).2.2.2 i k i.2 hik,
      fun _ _ => rfl⟩⟩
  obtain ⟨U, B, hy, hB, hU⟩ := S.loc y
  have hBm : ∀ z ∈ U, B ∈ S.S z := fun z hz => (hU z hz B).2 (by rw [Mat.mul_inv hB]; exact Par.one)
  exact ⟨U, hy, t (hBm y hy) τ i, fun z hz => hgerm (hA z) (hBm z hz) τ i⟩

theorem exists_gr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e Y π f₀ S A₀ hT
  obtain ⟨gr, hgr⟩ := exists_div S hT.1
  refine ⟨gr, fun y => ?_⟩
  obtain ⟨A, hA, t, h1, h2, h3⟩ := hgr y
  obtain ⟨φ, f, hf⟩ := hT.2 y A hA
  exact ⟨φ, f, t, (f.tri_iff _ f₀ t).2 ⟨_, hf, h1, h2⟩, h3⟩

end GlobalTheory.ShFam.GradedDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
section
namespace GlobalTheory.HolArc

theorem isAlgebraic_of_etale (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Algebra.Etale S R] [FaithfulSMul S R] : Algebra.IsAlgebraic S R := by
  let K := FractionRing S
  let L := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : Algebra.FormallyEtale R L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  haveI : Algebra.EssFiniteType R L := .of_isLocalization L (nonZeroDivisors _)
  haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S R L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L
  haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S R L)
    (IsFractionRing.injective R L)

theorem faithfulSMul_of_flat (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Module.Flat S R] : FaithfulSMul S R := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have hreg : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
  have : a • (1 : R) = a • (0 : R) := by simp [Algebra.smul_def, ha]
  exact one_ne_zero (hreg this)

theorem exists_line (m : ℕ) (q : MvPolynomial (Fin m) ℂ) (hq : q ≠ 0) (b₀ : Fin m → ℂ) :
    ∃ (v : Fin m → ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → MvPolynomial.eval (b₀ + u • v) q ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (MvPolynomial.funext fun x => by simpa using h x)
  let v := w - b₀
  let Q : Polynomial ℂ := MvPolynomial.aeval
    (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) q
  have hQ : ∀ u, Q.eval u = MvPolynomial.eval (b₀ + u • v) q := fun u => by
    have : (Polynomial.evalRingHom u).comp
        (MvPolynomial.aeval (R := ℂ) (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) :
          MvPolynomial (Fin m) ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom =
        MvPolynomial.eval (b₀ + u • v) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp <;> ring
    exact congrArg (fun f : MvPolynomial (Fin m) ℂ →+* ℂ => f q) this
  have hQ0 : Q ≠ 0 := fun h => hw (by
    have := hQ 1
    simpa [h, v] using this.symm)
  have hfin : (((Q.roots.toFinset.erase 0 : Finset ℂ) : Set ℂ))ᶜ ∈ nhds (0 : ℂ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.1 hfin
  refine ⟨v, ρ, hρ, fun u hu hu0 h => hb hu ?_⟩
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Set.mem_singleton_iff, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQ, h]
  simpa using hu0

end GlobalTheory.HolArc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.HolArc

theorem exists_holPts_ne_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  intro F A _ _ _ _ hS ψ₀ p hp
  haveI := hS
  haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀
  obtain ⟨g, m, s, hg, het⟩ := SmoothPointFamily.exists_etale_away (R := F) (RingHom.ker ψ₀)
  have hg₀ : ψ₀ g ≠ 0 := hg
  have hgne : g ≠ 0 := fun h => hg₀ (by simp [h])
  let σ : F →+* ℂ := ψ₀.comp (algebraMap F A)
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hgne
  haveI : IsDomain R := IsLocalization.isDomain_localization hle
  have hι : Function.Injective ι := IsLocalization.injective R hle
  let e : R →+* ℂ := IsLocalization.Away.lift g (g := ψ₀) (isUnit_iff_ne_zero.2 hg₀)
  have he : ∀ a, e (ι a) = ψ₀ a := fun a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) F →+* R := MvPolynomial.eval₂Hom (algebraMap F R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap F A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply F A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have heC : ∀ k, e (P (MvPolynomial.C k)) = σ k := fun k => by rw [hPC, he]; rfl

  obtain ⟨c, hc0, hc⟩ : ∃ c : MvPolynomial (Fin m) F, c ≠ 0 ∧ ι p ∣ P c := by
    letI : Algebra (MvPolynomial (Fin m) F) R := P.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin m) F) R := het
    haveI : FaithfulSMul (MvPolynomial (Fin m) F) R := faithfulSMul_of_flat _ _
    haveI := isAlgebraic_of_etale (MvPolynomial (Fin m) F) R
    exact (Algebra.IsAlgebraic.isAlgebraic (ι p)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff ι hι).2 hp))
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m F R P Set.univ (fun _ => σ) 0 e het
      isOpen_univ trivial (fun a => differentiableOn_const _) heC
  obtain ⟨h3, h4⟩ := hrec 0 e heC hO₀
  simp only [hPX, he] at h3 h4
  let b₀ : Fin m → ℂ := fun i => ψ₀ (s i)
  have hq0 : MvPolynomial.map σ c ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ σ.injective)).2 hc0
  obtain ⟨v, ρ, hρ, hline⟩ := exists_line m (MvPolynomial.map σ c) hq0 b₀
  let ℓ : ℂ → (Fin 0 → ℂ) × (Fin m → ℂ) := fun u => (0, b₀ + u • v)
  have hℓd : Differentiable ℂ ℓ :=
    (differentiable_const _).prodMk ((differentiable_const _).add (differentiable_id.smul_const v))
  have hℓ0 : ℓ 0 = (0, b₀) := by simp [ℓ]
  have hNo : ℓ ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (hN.preimage hℓd.continuous).mem_nhds (by simpa only [Set.mem_preimage, hℓ0] using h3)
  obtain ⟨ρ', hρ', hb⟩ := Metric.mem_nhds_iff.1 hNo
  have hsub : ∀ u ∈ Metric.ball (0 : ℂ) (min ρ ρ'), ℓ u ∈ N := fun u hu =>
    hb (Metric.ball_subset_ball (min_le_right _ _) hu)
  refine ⟨fun u => (τ (ℓ u)).comp ι, min ρ ρ', ⟨lt_min hρ hρ', fun a => ?_⟩, ?_, fun u hu => ?_,
    fun u hu hu0 h => ?_⟩
  · exact (hd (ι a)).comp hℓd.differentiableOn hsub
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, hℓ0]
    rw [show ((0 : Fin 0 → ℂ), b₀) = (0, fun i => ψ₀ (s i)) from rfl, h4, he]
  · refine RingHom.ext fun k => ?_
    simp only [RingHom.comp_apply]
    rw [← hPC]
    exact (hτ _ (hsub u hu)).2.1 k
  · have hev : (τ (ℓ u)).comp P = (MvPolynomial.eval (b₀ + u • v)).comp (MvPolynomial.map σ) := by
      refine MvPolynomial.ringHom_ext (fun k => ?_) fun i => ?_
      · simpa using (hτ _ (hsub u hu)).2.1 k
      · simpa [ℓ] using (hτ _ (hsub u hu)).2.2 i
    obtain ⟨d, hd'⟩ := hc
    have h0 : τ (ℓ u) (P c) = 0 := by
      rw [hd', map_mul]
      exact mul_eq_zero_of_left h _
    have h1 := congrArg (fun f : MvPolynomial (Fin m) F →+* ℂ => f c) hev
    simp only [RingHom.comp_apply] at h1
    exact hline u (Metric.ball_subset_ball (min_le_left _ _) hu) hu0 (h1.symm.trans h0)

end GlobalTheory.HolArc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExistsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧ (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧ ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  first | exact @GlobalTheory.BlockTransporter.finite_blockTransporter | exact GlobalTheory.BlockTransporter.finite_blockTransporter | (intros; apply GlobalTheory.BlockTransporter.finite_blockTransporter <;> assumption)
end

