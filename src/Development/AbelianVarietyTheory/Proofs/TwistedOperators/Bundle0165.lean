import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSumSelfDualExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  haveI := hL.1
  haveI := hL'.1
  refine ⟨isLattice_sumLat L L', fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdResidueFunctionsHalfSumIdempotents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.StepVec

theorem frMapO_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (c : AE D) (t : WO S T) :
    frMapO S T βS βT (c • t) = toEAf D c • frMapO S T βS βT t := by
  have hm : ((c • t : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) =
      toEAf D c • (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) := by
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp only [frMapO]
  rw [hm, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_locFn_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D),
    (∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP) →
    ∀ (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) (t : WO S T),
      IsHalf (∑ PP ∈ s, es PP) t →
      (open Classical in (if IsIntM (frMapO S T βS βT t) then ∏ PP ∈ s, ω PP (redM PP (frMapO S T βS βT t)) else 0)) =
        ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t) := by
  intro D S T βS βT s es hid ω t hhalf
  classical
  have hint : ∀ PP ∈ s, ∃ h : toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP), h⟩ = 1 :=
    fun PP hPP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hid PP hPP)
  have hhalfPP : ∀ PP ∈ s, IsHalf (es PP) (es PP • t) := by
    intro PP hPP i j
    have he : es PP * es PP = es PP := (hid PP hPP).1.1
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
  simp only [locFn]
  split_ifs with hN
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    obtain ⟨hi, h1⟩ := hint PP hPP
    have hN' : IsIntM (frMapO S T βS βT (es PP • t)) := by
      intro i j
      rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem hi (hN i j)
    rw [if_pos ⟨hhalfPP PP hPP, hN'⟩]
    congr 1
    funext i j
    have hmem : (frMapO S T βS βT (es PP • t)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hN' i j
    simp only [redM, dif_pos (hN i j), dif_pos hmem]
    have heq : (⟨(frMapO S T βS βT (es PP • t)) i j, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        ⟨toEAf D (es PP), hi⟩ * ⟨(frMapO S T βS βT t) i j, hN i j⟩ := by
      apply Subtype.ext
      simp only [Subring.coe_mul, frMapO_smul, Matrix.smul_apply, smul_eq_mul]
    rw [heq, map_mul, h1, one_mul]
  · have hex : ∃ PP ∈ s, ¬ IsIntM (frMapO S T βS βT (es PP • t)) := by
      by_contra hc
      push_neg at hc
      apply hN
      intro i j
      have ht : t = (∑ PP ∈ s, es PP) • t := by
        ext k l
        exact (hhalf k l).symm
      have hsum : frMapO S T βS βT t i j = ∑ PP ∈ s, frMapO S T βS βT (es PP • t) i j := by
        conv_lhs => rw [ht, frMapO_smul]
        rw [Matrix.smul_apply, smul_eq_mul, map_sum (toEAf D), Finset.sum_mul]
        refine Finset.sum_congr rfl fun PP _ => ?_
        rw [frMapO_smul, Matrix.smul_apply, smul_eq_mul]
      rw [hsum]
      exact Subring.sum_mem _ fun PP hPP => hc PP hPP i j
    obtain ⟨PP, hPP, hni⟩ := hex
    symm
    exact Finset.prod_eq_zero hPP (if_neg fun h => hni h.2)

end GlobalTheory.StepVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField.Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mult_inv {V : HSp D} {S : D.what₂.Tau → _} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Φ : MMap M}
    (hΦ : Φ ∈ Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, Φ v (γ * g) = Φ v g := by
  intro γ hγ g
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact (hx.aut v).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy => simp only [_root_.add_apply, Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [_root_.smul_apply, Pi.smul_apply, hx]

theorem eq_of_out {W : HSp D} {Φ Ψ : GA D W → ℂ} (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) : Φ = Ψ := by
  funext g
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h q]

theorem ev_sum {L H Y : Type} [Field L] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module L Y] {σ : L →+* ℂ}
    (j : Y →ₛₗ[σ] H) {V : HSp D} {S : D.what₂.Tau → _} {M : DSModel V S} (e : H →ₗ[ℂ] MMap M) (v : M.Vec) (g : GA D V) {m : ℕ}
    (a : Fin m → L) (y : Fin m → Y) : e (j (∑ l, a l • y l)) v g = ∑ l, σ (a l) * e (j (y l)) v g := by
  rw [map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, map_smul]
  rfl

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ev_base (fw : FWTie T R κ v₀) (hev : fw.Evaluates) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (f : Cu T κ i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = O.s0 :=
    ((congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans
      (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)).trans (sOv_eq T.toCore O.c' O.hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans O.hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have key : ∀ (σ σ' : T.Q.c.F →+* ℂ) (_ : σ' = σ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W)
      (hV' : T.V ((i : ℕ) + 1) σ' = W) (g : GA D W), phiC T hV' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) g := by
    intro σ σ' e W hV hV' g
    subst e
    subst hV
    rfl
  exact (congrFun h1 h).trans (key _ _ e _ O.hV hV h)

set_option maxHeartbeats 1000000 in

theorem exists_comb {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i T0 id) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (t : T0) (y : A.fam.amb.FL i t) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i t (R.jV i t y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 t
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple t).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i t (R.jV i t y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring

set_option maxHeartbeats 1000000 in

theorem ratAt_of_oneMap (fw : FWTie T R κ v₀) {ph : ℂ} {i : Fin D.R.m} (hW : R.models_HW) (hP : R.IsThP) (hU : R.LUnif)
    (hev : fw.Evaluates) (hinj : EvInj T R v₀) (h : OneMapOverL T R κ v₀ ph i) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t := by
  intro x₀
  obtain ⟨O, hF, hpin, hrow⟩ := h
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have aux7 := exists_comb hn O hpin hrow t x₀
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux7
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have ha : ∀ l, ∃ a : D.what₂.LL, sg0 D A a = ze * (as l : ℂ) := fun l => by
    have aux8 := AlgHom.mem_fieldRange.1 (mul_mem hze (hF.le (as l).2))
    obtain ⟨a, ha⟩ := aux8
    exact ⟨a, (RingHom.congr_fun hs a).trans ha⟩
  choose a ha using ha
  have hmem := (hW i (sg0 D A)).2.1.ge (hP.thF_mem i t (R.jV i t x₀))
  obtain ⟨w, hw⟩ := hmem
  have hinv : ∀ u : (R.HW i (sg0 D A)).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      evAt R i _ (v₀ i _) u (γ * g) = evAt R i _ (v₀ i _) u g := fun u =>
    mult_inv R.θ _ _ _ ((hW i _).2.1.le (LinearMap.mem_range_self _ u)) _
  have e0 : (R.HW i (sg0 D A)).e (ph • w) = ph • R.thF i t (R.jV i t x₀) :=
    (map_smul (R.HW i (sg0 D A)).e ph w).trans (congrArg (ph • ·) hw)
  have key : (R.FW i).j (sg0 D A) (∑ l, a l • ((fw.e i (fs l) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) = ph • w := by
    refine hinj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (eq_of_out (hinv _) (hinv _) fun q => ?_)
    have e1 : evAt R i _ (v₀ i _) (ph • w) q.out = ph * R.thF i t (R.jV i t x₀) (v₀ i _) q.out :=
      congrArg (fun Φ : MMap (R.MW i (sg0 D A)) => Φ (v₀ i _) q.out) e0
    refine (ev_sum _ _ _ _ _ _).trans (Eq.trans ?_ ((hq q).symm.trans e1.symm))
    exact Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ha l) (ev_base fw hev O (fs l) q.out)
  have h1 := (congrArg (R.HW i (sg0 D A)).e key).trans e0
  exact ⟨_, h1, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.proj_clause R i ph t hP.thG (hW i _).1 (hU i _).2.2 _ _ h1⟩

theorem rat_of_oneMapOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀) (ph : ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → R.LUnif → fw.Evaluates → EvInj T R v₀ → GlobalTheory.TwistField.OneMapOverL T R κ v₀ ph i → ∀ t : T0, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ fw _ _ _ _ hM hP hU hev hinj h t => ratAt_of_oneMap fw hM.HW hP hU hev hinj h t

end GlobalTheory.TwistField.Read
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.AdSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def RealScal (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (a : GA D T) (z : ℂ) : Prop :=
  ∀ φ : TF S.rank C.g, SW.IsSB φ → om (1, a) (C.Th (C.xB B) φ) = z • C.Th (C.xB (C.mvB a B)) φ

def HolUpTo (C : Ctx S T) (B : C.Bas) (la : Wt C.X.Ψ T.rank) (z φ : GA D T → ℂ) : Prop :=
  ∀ g : GA D T, ∃ Q : Frame C.X.Ψ T.rank → ℂ, DifferentiableOn ℂ Q C.X.dom ∧
    (∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, Q (rmul x b) = bchar la b * Q x) ∧
    ∀ a ∈ GinfC T, φ (g * a) = z a * Q (C.xB (C.mvB a B))

def detPow (θ : InfFam D) (V : HSp D) (m : D.what₂.Tau → ℤ) (a : GA D V) : ℂ :=
  ∏ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V a)).det ^ m ρ

def torAt (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau)
    (t : Fin V.rank → ℝ) : GA D V :=
  atTau θ V ρ (B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹)

def LowKilled (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : Prop :=
  HolRead.SmoothReal θ V φ ∧ ∀ ρ (c d : Fin V.rank), d < c → RderC θ V ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) φ = 0

def revPos {n : ℕ} (p : ℕ) (a : Fin n) : Fin n :=
  if h : (a : ℕ) < p ∧ p ≤ n then ⟨p - 1 - a, by omega⟩ else a

theorem revPos_revPos {n : ℕ} (p : ℕ) (a : Fin n) : revPos p (revPos p a) = a := by
  by_cases h : (a : ℕ) < p ∧ p ≤ n
  · have h' : p - 1 - (a : ℕ) < p ∧ p ≤ n := ⟨by omega, h.2⟩
    ext
    simp only [revPos, dif_pos h, Fin.val_mk, dif_pos h']
    omega
  · simp only [revPos, dif_neg h]

def revB {ι : Type} {n : ℕ} (p : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ).submatrix id (revPos p)

def thetaSet (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (u : WO S T → ℂ)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) : Set (GA D T → ℂ) :=
  {φ | ∃ (h : GA D S) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' ∧
    φ = fun g => om (h, g) (C.fvec B u Q) 0}

def ContT (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun g : GA D T => om (1, g) f w

abbrev reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : HSp D := StdFrame.reframe S b

def frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  S.frame.toMatrix b

def frPinv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  b.toMatrix S.frame

def reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO (reS S b) T) : WO S T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))

def reF (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : (WO S T → ℂ) →ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (reW S T b)

theorem reF_apply (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) (x : WO (reS S b) T) :
    reF S T b f x = f (reW S T b x) := rfl

theorem reF_zero (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) : reF S T b f 0 = f 0 := by
  rw [reF_apply]
  congr 1
  exact Matrix.zero_mul _

end GlobalTheory.AdSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models

theorem rowTest_toCx3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F h
  obtain ⟨n, ψ, hinj, hrat⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0) R.emb0 (ι := T0)
    (X := fun t => A3.A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)).2 h
  exact ⟨n, ψ, hinj, fun t i x => hrat t x i⟩

end GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalConjBaseFacts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  first | exact @GlobalTheory.PlaceTensor.halfWaves_span | exact GlobalTheory.PlaceTensor.halfWaves_span | (intros; apply GlobalTheory.PlaceTensor.halfWaves_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidificationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_has_rigidification : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK → IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  first | exact @GlobalTheory.RigExists.exists_rig | exact GlobalTheory.RigExists.exists_rig | (intros; apply GlobalTheory.RigExists.exists_rig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
section
namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  first | exact @GlobalTheory.TameProd.tameOn_of_tame | exact GlobalTheory.TameProd.tameOn_of_tame | (intros; apply GlobalTheory.TameProd.tameOn_of_tame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNormStatement
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ), (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) * ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  first | exact @GlobalTheory.absE_eq_prod_norm_fstA_sndA | exact GlobalTheory.absE_eq_prod_norm_fstA_sndA | (intros; apply GlobalTheory.absE_eq_prod_norm_fstA_sndA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  first | exact @GlobalTheory.EmbHeight.height_emb_le | exact GlobalTheory.EmbHeight.height_emb_le | (intros; apply GlobalTheory.EmbHeight.height_emb_le <;> assumption)
end

