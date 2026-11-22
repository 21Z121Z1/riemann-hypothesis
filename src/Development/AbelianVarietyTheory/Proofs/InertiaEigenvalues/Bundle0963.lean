import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Shift

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ}

set_option maxHeartbeats 4000000 in

theorem shift_central (hP : O.Pins κ v₀ ι x₀) (hn : κ.n = (Vc D i).rank) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0) {ph : ℂ} (hE : O.OneMapOf κ v₀ cE ph)
    (hE0 : O.EquivAt κ c0) (hS : GlobalTheory.AdTh.SerOf O κ v₀ c0 1)
    (hW : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∃ U ∈ R.Wall i (sg0 D A), ∀ h,
      U v₀ h = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cE f h) :
    ∃ (z : G) (ze : ℂ), z ∈ Subgroup.center G ∧ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧
      (∃ k, LiftW R i z k) ∧ ∀ k, LiftW R i z k →
      ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ h, O.phi c0 f h = ze * chiC R i z / ph * O.phi cE f (h * k) := by
  obtain ⟨hEq, ⟨-, hBC, hAct, hcE, hph, z, hz, hrow⟩, -⟩ := hE
  obtain ⟨ze, hzL, ⟨m, hm, hze⟩, hrow⟩ := hrow ()
  have hze0 : ze ≠ 0 := fun h => by
    rw [h, zero_pow hm.ne'] at hze
    exact zero_ne_one hze
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have h0 : ∀ k, c0 k ≠ 0 := fun k h => by simpa [h] using hS.1 k
  have hE0' : ∀ k, cE k ≠ 0 := fun k h => by simpa [h] using hcE k
  have hl : ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hlift : ∀ g, ∃ k, LiftW R i g k := fun g => (hP.lift.lev g).imp fun _ h => h.1
  have hinvW : ∀ U ∈ R.Wall i (sg0 D A), ∀ γ ∈ GQ (Wc D i), ∀ g, U v₀ (γ * g) = U v₀ g := fun U hU =>
    (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ U hU v₀).1
  have hinv : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ γ ∈ GQ (Wc D i), ∀ g, O.phi cE f (γ * g) = O.phi cE f g := by
    intro f hf γ hγ g
    obtain ⟨U, hU, e⟩ := hW f hf
    exact mul_left_cancel₀ hl (by rw [← e, ← e, hinvW U hU γ hγ])
  refine ⟨z, ze, hz, hzL, ⟨m, hm, hze⟩, hlift z, fun k hk => ?_⟩
  have hbase : ∀ y, R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈
      shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k := by
    intro y
    obtain ⟨hh, J', hrep, hPl, hth, hpl⟩ := (hP.tuple ()).reps
    obtain ⟨x, hx⟩ := hPl y
    obtain ⟨⟨f', hf', hcl⟩, hid⟩ := hrow x ((hpl x).2 ⟨y, hx⟩)
    have hs := hS.2.2 () hh J' hrep _ x hx f' hf'.1 hcl
    have hq := hid f' hf'.1 hcl
    have hth' : ∀ q : AutQ (Wc D i), O.thAd () x q = R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out := fun q => congrFun (hth _ x hx) q
    have hf'' : f' ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank := hf'
    have hb := hBC (wtA κ) (Vc D i).rank f' hf''
    obtain ⟨n, as, fs, hfs, hbc⟩ := hb
    have hbc' := hAct _ _ z n as fs f' hf'.1 (fun j => (hfs j).1) hbc
    have hfs' : ∀ j, fs j ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun j => by rw [hn]; exact hfs j
    have r1 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc
    have r2 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc'
    have e1 : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ = ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        inC O.c' (as j)) • O.phi c0 (fs j) := by
      funext g
      have := hs g
      rw [one_mul, r1] at this
      rw [this]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, phi_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmemL : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈ liftSub (LiftW R i) (ratio O cE c0) := by
      rw [e1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (phi_mem_liftSub O h0 hEq hE0 (hfs' j))
    refine ⟨hmemL, fun g => ?_⟩
    have e2 : ∀ q : AutQ (Wc D i), ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (q.out * k) := by
      intro q
      have h3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out = ze * cE (O.dict q.out).1 *
          (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f') (O.dict q.out).1 (O.dict q.out).2) :=
        (congrArg (ph * ·) (hth' q)).symm.trans (hq q)
      rw [h3, r2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := (hEq z k hk (fs j) (hfs' j)).2 q.out
      rw [← chiC_coe, phi_apply] at h2
      linear_combination (ze * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * h2
    have e3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (g * k) := by
      refine eq_of_out (fun g => ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g) (fun g => ze * chiC R i z *
        ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * O.phi cE (fs j) (g * k))
        (fun γ hγ g => congrArg (ph * ·) (hinvW _ (hmem i A.μ0 _) γ hγ g)) (fun γ hγ g => ?_) e2 g
      refine congrArg (ze * chiC R i z * ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [mul_assoc γ, hinv _ (hfs' j) γ hγ]
    exact shift_eq (pE := fun j => O.phi cE (fs j)) hph0 e1 (fun j h => phi_ratio O h0 (fs j) h) (hmemL.1 z k hk g) e3
  let ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun U => U v₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hall : ∀ y, R.thF i A.μ0 y v₀ ∈ shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k :=
    GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hHV i A.μ0).1 (hHV i A.μ0).2.1 (jVx R i A.μ0) (hjV i A.μ0)
      ((shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap (ev ∘ₗ R.thF i A.μ0)) hbase
  have hWall : R.Wall i (sg0 D A) ≤ (shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap ev := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, y, rfl⟩
    obtain ⟨k', hk', e⟩ := exists_liftW_act R i (hlift g)
    have h1 := shiftSub_translate (liftW_mul R i) hz hk (hall y) hk'
    rw [← funext (e (R.thF i A.μ0 y v₀))] at h1
    exact h1
  intro f hf h
  obtain ⟨U, hU, e⟩ := hW f hf
  have h1 : U v₀ h = ze * chiC R i z / ph * ratio O cE c0 h * U v₀ (h * k) := (hWall hU).2 h
  rw [e, e, phi_ratio O h0 f h] at h1
  have hr : ratio O cE c0 h ≠ 0 := div_ne_zero (hE0' _) (h0 _)
  refine mul_left_cancel₀ (mul_ne_zero hl hr) ?_
  linear_combination h1

theorem phi_smul (s : ℂ) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi (s • cc) f h = s * O.phi cc f h := by
  rw [phi_apply, phi_apply, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in

theorem oneMapOf_smul {ph ze : ℂ} (h : O.OneMapOf κ v₀ c0 ph) (hL : ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange)
    {m : ℕ} (hm : 0 < m) (hze : ze ^ m = 1) : O.OneMapOf κ v₀ (ze⁻¹ • c0) ph := by
  have hn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hn
  obtain ⟨hE, ⟨h1, h2, h3, h4, h5, z, hz, h6⟩, h7⟩ := h
  refine ⟨fun g k hk f hf => ⟨(hE g k hk f hf).1, fun x => ?_⟩, ⟨h1, h2, h3, fun k => ?_, h5, z, hz, fun t => ?_⟩, fun x => ?_⟩
  · rw [phi_smul, phi_smul, (hE g k hk f hf).2 x, mul_left_comm]
  · have := h4 k
    show ‖ze⁻¹ * c0 k‖ = 1
    rw [norm_mul, norm_inv, hn, inv_one, one_mul]
    exact this
  · obtain ⟨y, hy, ⟨n, hn0, hyn⟩, h8⟩ := h6 t
    refine ⟨y * ze, mul_mem hy hL, ⟨n * m, Nat.mul_pos hn0 hm, ?_⟩, fun x hx => ⟨(h8 x hx).1, fun f hf hc q => ?_⟩⟩
    · rw [mul_pow, pow_mul, hyn, one_pow, mul_comm n, pow_mul, hze, one_pow, one_mul]
    · refine ((h8 x hx).2 f hf hc q).trans ?_
      have e : ∀ a : ℂ, y * a = y * ze * (ze⁻¹ * a) := fun a => by field_simp
      exact congrArg (fun u => u * _ * _) (e _)
  · obtain ⟨n, a, f, hf⟩ := h7 x
    obtain ⟨y, hy⟩ := hL
    have hy' : D.what₂.embLL y = ze := hy
    refine ⟨n, fun k => a k * y, f, fun g => (hf g).trans (Finset.sum_congr rfl fun k _ => ?_)⟩
    rw [phi_smul, map_mul, hy']
    field_simp

end Shift

section Frame

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

omit iA in
theorem lawsJ_setCE (hL : LawsJ T) {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ}
    (h : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ)) : LawsJ (setCE T c') :=
  ⟨hL.toLawsM, h, hL.muVal, hL.muConj, hL.intAll, hL.modelW, hL.familyUniformisationBasePointOrthogonal, hL.kfHalf, hL.adPin⟩

set_option maxHeartbeats 1000000 in

theorem framePin_smul {c' c'' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
    {hV : T.V ((i : ℕ) + 1) σ = Wc D i} {s : ℂ} (hs : ‖s‖ = 1) (e : c'' ((i : ℕ) + 1) σ = s • c' ((i : ℕ) + 1) σ)
    (h : @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i σ hV) :
    @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c'') iA R i σ hV := by
  have h0 : s ≠ 0 := fun e => by simp [e] at hs
  obtain ⟨ph, b, h1, h2, h3⟩ := h
  refine ⟨ph / s, b, by rw [norm_div, h1, hs, div_one], h2, fun g γ hγ hf hx Wt Y X z hz => ?_⟩
  refine (h3 g γ hγ hf hx Wt Y X z hz).trans ?_
  have e1 : ∀ k (a : ℂ), ph * (c' ((i : ℕ) + 1) σ k * a) = ph / s * (c'' ((i : ℕ) + 1) σ k * a) := fun k a => by
    rw [e, Pi.smul_apply, smul_eq_mul]
    field_simp
  exact congrArg (· * _) (e1 _ _)

set_option maxHeartbeats 2000000 in

theorem exists_shift (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A} (hC : GlobalTheory.Core5 R F)
    (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hJ : JEvExists T R B.κ B.v₀) (i : Fin D.R.m) :
    ∃ (c1 : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (z : G), z ∈ Subgroup.center G ∧
      (B.O i).OneMapOf (B.κ i) (B.v₀ i (sg0 D A)) c1 1 ∧
      (∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, c' ((i : ℕ) + 1) T.σ₀ = c1 → ∀ hV,
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n, ∀ h,
        (B.O i).phi c1 f h = (B.O i).phi (T.cE ((i : ℕ) + 1) (B.O i).s0) (actLev T.Q.c (B.O i).lev2 z f) h := by
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B
  dsimp only at hJ ⊢
  have ht : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hC.lev hC.fam hC.models hC.thP
  obtain ⟨cc, hcc, u, hu, hE0, hS, -⟩ := GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_ofFive GlobalTheory.ChartFree.chartIndep
    D G Pl0 T0 A T R F κ v₀ hC ht hio i _ _ (O i) (pins i).2
  have h1 : (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (u • cc) 1 :=
    GlobalTheory.OneMapPhaseOne.oneMapOf_one_of_serOf D G Pl0 T0 A T R F κ v₀ hC.grp hC.thP ht O i (pins i) (u • cc) hS
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofFive GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC ht i _ _ (O i) (pins i).2 ())
      hE0
  have hrow := phase i hU ⟨_, _, h1⟩
  have hσ : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hg := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV₁ : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f := fun f hf =>
    ⟨_, (baseEmbedding_reading_eval_adelicFunction fw hV₁ (hJ i _ hg hV₁) ⟨f, hf⟩).trans (phiC_congr hσ hV₁ hV _ _)⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hphi : ∀ f h, phiC T hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h :=
    fun f h => phiC_apply hV _ f h
  obtain ⟨z, ze, hz, hzL, ⟨m, hm, hze⟩, ⟨k, hk⟩, hs⟩ := shift_central (O i) (pins i).2 hn hC.models.HV hC.models.jV hC.thP.thF_mem
    (GlobalTheory.ThetaSpanObj.spanAtObj R hP hsz hC.lev hC.fam hC.models hC.thP i A.μ0) hrow hE0 hS fun f hf => by
      obtain ⟨y, hy⟩ := hev f hf
      exact ⟨_, (hC.models.HW i _).2.1.le (LinearMap.mem_range_self _ y), fun h => (congrFun hy h).trans (hphi f h)⟩
  have hzn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hzn
  refine ⟨ze⁻¹ • u • cc, z, hz, oneMapOf_smul (O i) h1 hzL hm hze, fun c'' hc'' hV' => ?_, fun f hf h => ?_⟩
  · obtain ⟨c', hc', hL'⟩ := exists_withConst fw.laws ((i : ℕ) + 1) T.σ₀ cc hcc.1
    have hx0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hσ ▸ fw.x0 i (sg0 D A) hg
    have hpin := @GlobalTheory.FrameConst.framePin_of_ccIs D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV rfl hL' hC.models.inf
      (pins i).2.lift.std hx0 (by subst hc'; exact hcc)
    refine framePin_smul (c' := c') (s := ze⁻¹ * u) (by rw [norm_mul, norm_inv, hzn, hu, inv_one, one_mul]) ?_ hpin
    rw [hc'', hc']
    exact funext fun _ => (mul_assoc _ _ _).symm
  · have h2 := hs k hk f hf h
    have h3 := (hrow.1 z k hk f hf).2 h
    rw [← chiC_coe] at h3
    rw [phi_smul, h2, h3]
    field_simp

end Frame

end GlobalTheory.Unframe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlaces
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUpInt

theorem valuation_lt_one_iff {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    la.valuation K x < 1 ↔ 0 < vLa la x := by
  have h0 : la.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [vLa]
  omega

theorem overLa_comp {K K₂ : Type} [Field K] [NumberField K] [Field K₂] [NumberField K₂] (i : K →+* K₂)
    {la : HeightOneSpectrum (𝓞 K)} {la₂ : HeightOneSpectrum (𝓞 K₂)}
    (h : ∀ x : 𝓞 K, x ∈ la.asIdeal ↔ la₂.valuation K₂ (i x) < 1) {T : CDVR} {io₂ : K₂ →+* T.Fr} {e₂ : ℕ}
    (ho : OverLa la₂ T.V io₂ e₂) : ∃ e, OverLa la T.V (io₂.comp i) e := by
  obtain ⟨N, hN, hp⟩ := GlobalTheory.IntCoefExt.exists_nat_pos ho
  obtain ⟨la', e, ho'⟩ := GlobalTheory.IntCoefExt.exists_overLa (io₂.comp i) hN hp
  obtain rfl : la' = la := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp
    have hx' : (x : K) ≠ 0 := by simpa using hx
    have e1 := ho'.2 (x : K)
    rw [RingHom.comp_apply, ho.2] at e1
    rw [h, valuation_lt_one_iff la₂ ((map_ne_zero i).2 hx'), ← la'.valuation_lt_one_iff_mem (K := K)]
    refine (valuation_lt_one_iff la' hx').trans ?_
    have p1 : (0 : ℤ) < e := by exact_mod_cast ho'.1
    have p2 : (0 : ℤ) < e₂ := by exact_mod_cast ho.1
    rw [← mul_pos_iff_of_pos_left p1, ← e1, mul_pos_iff_of_pos_left p2]
  exact ⟨e, ho'⟩

theorem pull_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, (∀ la ∈ S, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, 0 ≤ v f) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ la₂ ∈ S₂, ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la₂, 0 ≤ v f₂ := by
  intro D T hT j hj σ _ C _ a n _ S S₂ hS f _ hint f₂ _ hP la₂ hla₂ v hv
  obtain ⟨⟨q, T', io₂, e₂, ho, y₂, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨la, hla, hl⟩ := hS la₂ hla₂
  obtain ⟨e, ho'⟩ := overLa_comp C.inc hl ho
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  let io' : C.c'.F →+* T'.Fr := io₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  let io : T.Q.c.F →+* T'.Fr := io₂.comp C.inc
  have hio : ∀ x, io' (incF T.Q.c C.c' C.hle x) = io x := fun _ => rfl
  letI := io₂.toAlgebra
  letI := io'.toAlgebra
  letI := io.toAlgebra
  obtain ⟨y', hy'⟩ := GlobalTheory.CovPull.below_exists C.d hO hK (S := T'.Fr) (fun _ => rfl) y₂.1
  let y : IntFr (T.Q.Xo j) T.Q.c T' io := ⟨y'.res C.hle hio, GlobalTheory.TransferCompare.allTest_framed _ _ _ _,
    (GlobalTheory.IntCoefExt.integral_res_iff C.hle T' io' io hio _).1
      (GlobalTheory.CoverDown.integral_below C.d T' io' io₂ (fun _ => rfl) y' y₂.1 hy' y₂.2.2)⟩
  have e1 : evI y₂ f₂ = evI y f := hP T'.Fr hio (fun _ => rfl) y₂.1 y' hy'
  have key := hint la hla _ ⟨PtV.mk (PY := Unit) (lies := fun _ _ _ _ => True) la ho' y hy () trivial, rfl⟩
  refine (GlobalTheory.IntCoefExt.nval_nonneg_iff ho.1 _).2 ?_
  rw [e1]
  exact (GlobalTheory.IntCoefExt.nval_nonneg_iff ho'.1 _).1 key

end GlobalTheory.CoverUpInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistConjugateTuplesSameRealisationExtensionStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | exact GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj | (intros; apply GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverIsDictionaryFrameCompatible
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem relab_and_goodEmb_of_inc {D : D7} (T : CoreJ D) (j : ℕ) (C : Cover T j T.σ₀) (hinc : C.σ₂.comp C.inc = T.σ₀) :
    (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  have key : ∀ (z : ℂ) (hz : z ∈ T.Q.c.F) (hz2 : z ∈ C.d.c₂.F), C.σ₂ ⟨z, hz2⟩ = z := by
    intro z hz hz2
    have h1 : (⟨z, hz2⟩ : C.d.c₂.F) = C.inc ⟨z, hz⟩ := Subtype.ext rfl
    have h2 : C.σ₂ (C.inc ⟨z, hz⟩) = T.σ₀ ⟨z, hz⟩ := by rw [← RingHom.comp_apply, hinc]
    rw [h1, h2]
    rfl
  refine ⟨fun τ => RingHom.ext fun x => key _ (T.Q.c.conj τ x) _, ?_⟩
  have hz : T.Q.H.rt0 ∈ T.Q.c.F := GlobalTheory.coe_baseKA_rho T.Q.l ▸ T.Q.c.le (baseKA T.Q.l).ρ.2
  have hz2 : T.Q.H.rt0 ∈ C.d.c₂.F := GlobalTheory.coe_baseKA_rho C.d.l₂ ▸ C.d.c₂.le (baseKA C.d.l₂).ρ.2
  have e : (IntermediateField.inclusion C.d.c₂.le) (baseKA C.d.l₂).ρ = ⟨T.Q.H.rt0, hz2⟩ :=
    Subtype.ext (GlobalTheory.coe_baseKA_rho C.d.l₂)
  unfold GoodEmb
  rw [RingHom.comp_apply]
  erw [e]
  exact key _ hz hz2

theorem isDict_cover_of_isUnif {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (W : HSp D)
    (hV : T.V j T.σ₀ = W) (hr : W.rank = D.R.r) (C : Cover T j T.σ₀) (hC : C.IsUnif) (hGE : GoodEmb C.d.c₂ C.σ₂) :
    IsDict C.U₂ W hr (castDict hV C.dict₂) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j)
        (T.x₀ j T.σ₀) := by
  subst hV
  obtain ⟨-, -, -, hU, -, hr', g, e, F, ik, φ, th, hMW, hth, hDL⟩ := hC
  have hP := hL.pins
  have hg := T.toCore.good_σ₀
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hio := GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj _ hg _ rfl hr
  refine ⟨hU, hio.1, fun k => ⟨hMW k, fun τ => ?_, ?_⟩, fun k τ hτ => ?_, g, e, F, ik, φ, th, hth, hDL⟩
  · rw [(hU.2.1 k).2 τ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : (C.U₂.X k).κ0 = 2 * (C.U₂.X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hGE) hU' hr1 w k).1
    rw [h1, (hMW k).2, mul_neg]
  · rw [(hMW k).1, (hU.2.1 k).1]
    exact hio.2 τ (((hU.2.1 k).2 τ).1 hτ)

set_option maxHeartbeats 1000000 in

theorem cover_dict_frameTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → IsDict C.U₂ (Wc D i) (rank_Wc i) (castDict hV C.dict₂) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ FrameTie C.U₂ (Wc D i) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) ∧ (∀ τ, relab C.d.c₂ C.σ₂ τ = τ) ∧ GoodEmb C.d.c₂ C.σ₂ := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL _ _ _ hmod _ hT i _ hV C hC
  have hj := inR i
  have hinc : C.σ₂.comp C.inc = T.σ₀ := hC.2.2.1
  obtain ⟨hrel, hGE⟩ := relab_and_goodEmb_of_inc T _ C hinc
  have hD := isDict_cover_of_isUnif T hL _ hj _ hV (rank_Wc i) C hC hGE
  have hU := hD.1
  have hP := hL.pins
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hmod.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  refine ⟨hD, fun k => ⟨isInvOf_cart _ _ _ hx (by have := hU.1; have := (hU.2.1 k).1; omega) hε,
    fun hq => isBasOf_onb _ _ _ hx hq hε⟩, hrel, hGE⟩

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TupDil

theorem card_mem {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ((Nat.card (𝓞 E ⧸ PP.asIdeal) : ℕ) : 𝓞 E) ∈ PP.asIdeal := by
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem card_ne_zero {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ PP.asIdeal) ≠ 0 := by
  have := (Ideal.absNorm_eq_zero_iff (I := PP.asIdeal)).not.2 PP.ne_bot
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this

theorem om_model_eq_unit_smul_dilate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∃ κ : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) κ ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ, IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hz
  refine GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ (GlobalTheory.OnCmp.kerDat_tuple hC.lev hC.thP t)
    ⟨t, subset_rfl⟩ _ ?_ ?_ eg eQ fg heg heQ hfg ϖ (by exact_mod_cast hϖ0) hϖ z hz
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_ne_zero PP
  · intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hPP)
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_mem PP)

end GlobalTheory.TupDil
end

