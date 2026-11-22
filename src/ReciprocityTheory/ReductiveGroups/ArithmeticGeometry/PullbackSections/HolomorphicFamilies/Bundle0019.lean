import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Mathlib
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamHelp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

open Formalism.L2.Pj

section Induce

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

end Induce

theorem vLa_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (p : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hp
  have h2 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) ≠ 0 := by
    rw [Ne, map_eq_zero, map_natCast]
    exact_mod_cast hp0
  have hlog := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at hlog
  unfold vLa
  rw [show ((p : K)) = algebraMap (𝓞 K) K (p : 𝓞 K) from (map_natCast _ _).symm]
  omega

section Host

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

end Host

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NegLogEpStar
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma neg_log_epStar (M f w k0 : ℝ) (hM : 0 < M) (hfw : 0 < f * w + 2) (hk0 : 0 < k0) (hk0' : k0 ≤ 2) :
    -Real.log (epStar M f w k0) ≤ max 0 (Real.log M + Real.log (f * w + 2) + Real.log 2) := by
  unfold epStar
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < M * (f * w + 2) * k0 * Real.log 2 := by positivity
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2)) with hq | hq
  · rw [min_eq_left hq, Real.log_one]; simp
  · rw [min_eq_right hq, Real.log_div Real.pi_pos.ne' hden.ne', Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk0.ne', Real.log_mul hM.ne' hfw.ne']
    have h1 : Real.log k0 ≤ Real.log 2 := Real.log_le_log hk0 hk0'
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith)
    have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have h4 := le_max_right 0 (Real.log M + Real.log (f * w + 2) + Real.log 2)
    linarith

theorem lam1Row (hMD : ModelDataXSt) : Lam1RowSt := by
  intro D T h hGam large₂ j hj w hrows hL hrn hlast σ hσ f hf k z0 hz0 hhalf hpos
  obtain ⟨e, M, wg, hM, hlM, hwg, hsp, htr, hfw, ⟨B, hlB, hB⟩, hk0⟩ := hMD D T h hGam large₂ j hj w hrows hL hrn σ hσ k

  have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  let S : Submodule ℂ (FDSec (T.U j σ).X) :=
    { carrier := {Q | ∀ k, Q k ∈ ((T.U j σ).X k).SS (laU (T.U j σ) (wtA w) w.n k)}
      add_mem' := by
        intro Q R hQ hR k
        refine ⟨BoundedSectionAlgebra.bdd_add _ (hQ k).1 (hR k).1, fun ξ hξ x hx => ?_⟩
        have e1 := BoundedSectionAlgebra.fj_add _ (hQ k).1 (hR k).1 hξ hx 0
        rw [(hQ k).2 ξ hξ x hx, (hR k).2 ξ hξ x hx, add_zero] at e1
        exact e1
      zero_mem' := fun k => ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
      smul_mem' := by
        intro c Q hQ k
        refine ⟨BoundedSectionAlgebra.bdd_smul _ c (hQ k).1, fun ξ hξ x hx => ?_⟩
        have e1 := BoundedSectionAlgebra.fj_smul _ (laU (T.U j σ) (wtA w) w.n k) (Q k) ξ x 0 c
        rw [(hQ k).2 ξ hξ x hx, mul_zero] at e1
        exact e1 }
  have hSS : rdU (T.U j σ) f k ∈ ((T.U j σ).X k).SS (laU (T.U j σ) (wtA w) w.n k) :=
    (Submodule.span_le.2 (fun Q hQ k => hQ k) : holSub _ _ ≤ S) hcusp k
  have hmax := maxBound_holds D.R.r e.toX (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) M wg hSS hM hsp
    hwg htr z0 hz0 hhalf hpos

  have hfw0 : 0 < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  set ep := epStar M (fdeg D.host.E) wg e.k0 with hepdef
  have hep : 0 < ep := by
    rw [hepdef]; unfold epStar
    exact lt_min one_pos (div_pos Real.pi_pos
      (mul_pos (mul_pos (mul_pos hM hfw0) e.minWeight_pos) (Real.log_pos (by norm_num))))
  have hmax' : ∀ v ∈ e.L', v ≠ 0 → ∃ τ : ((T.U j σ).X k).Ψ,
      ep ≤ ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := hmax
  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = e.k0 := fun τ => by
    unfold Data.c; rw [e.ξ0_abs τ]; ring

  have hr : 0 < D.R.r := (PfTies1.dimPos_fr D).2
  have hne : ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 := by
    have hL' : ∃ y ∈ e.L', y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hx0 : (Pi.single (⟨0, hr⟩ : Fin D.R.r) (1 : D.host.E)) ∈ e.L' := by
        refine e.L'_dual _ (fun y hy => ?_)
        rw [hcon y hy]
        simp [herm]
        exact isIntegral_zero
      exact Pi.single_ne_zero_iff.2 one_ne_zero (hcon _ hx0)
    obtain ⟨y, hy, hy0⟩ := hL'
    exact ⟨_, e.NC_sub y hy, smul_ne_zero (Nat.cast_ne_zero.2 e.NC_pos.ne') hy0⟩
  obtain ⟨v0, hv0, hv00⟩ := hne
  have hBpos : 0 < B := by
    obtain ⟨a, ha0, -, hab⟩ := hB v0 hv0 hv00
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero τ).2 ha0)) (hab τ)
  set m := e.k0 * ep / B ^ 2 with hmdef
  have hm : 0 < m := div_pos (mul_pos e.minWeight_pos hep) (pow_pos hBpos 2)
  have hlow : ∀ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 → m ≤ ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨a, ha0, hav, hab⟩ := hB v hv hv0
    obtain ⟨τ0, hτ0'⟩ := hmax' _ hav (smul_ne_zero ha0 hv0)
    have hemb : Data.emb τ0.1 (a • v) = (τ0.1 a) • Data.emb τ0.1 v := by
      funext i; simp [Data.emb]
    rw [hemb, Data.maj_smul ((T.U j σ).X k) (Data.Hf_self ((T.U j σ).X k) hz0 τ0)] at hτ0'
    have hmaj0 := FlagSpanBounds.maj_nonneg ((T.U j σ).X k) hz0 τ0 (Data.emb τ0.1 v)
    have hns : Complex.normSq (τ0.1 a) ≤ B ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hab τ0.1) 2
    have hterm : ∀ τ, 0 ≤ ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := fun τ =>
      mul_nonneg (by rw [hc]; exact e.minWeight_pos.le) (FlagSpanBounds.maj_nonneg ((T.U j σ).X k) hz0 τ _)
    have h1 : ep / B ^ 2 ≤ ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := by
      rw [div_le_iff₀ (pow_pos hBpos 2)]; nlinarith
    calc m = e.k0 * (ep / B ^ 2) := by rw [hmdef]; ring
      _ ≤ e.k0 * ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := mul_le_mul_of_nonneg_left h1 e.minWeight_pos.le
      _ = ((T.U j σ).X k).c τ0 * ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := by rw [hc]
      _ ≤ ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) :=
        Finset.single_le_sum (fun τ _ => hterm τ) (Finset.mem_univ τ0)
  have hle : m ≤ ((T.U j σ).X k).firstMinimumSq z0 :=
    le_csInf ⟨_, v0, hv0, hv00, rfl⟩ (fun t ⟨v, hv, hv0', ht⟩ => ht ▸ hlow v hv hv0')
  refine ⟨lt_of_lt_of_le hm hle, ?_⟩
  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ Real.log (1 / m) :=
    Real.log_le_log (one_div_pos.2 (lt_of_lt_of_le hm hle)) (one_div_le_one_div_of_le hm hle)
  have h2 : Real.log (1 / m) = -Real.log e.k0 - Real.log ep + 2 * Real.log B := by
    rw [hmdef, one_div, Real.log_inv, Real.log_div (mul_pos e.minWeight_pos hep).ne' (pow_pos hBpos 2).ne',
      Real.log_mul e.minWeight_pos.ne' hep.ne', Real.log_pow]
    push_cast; ring
  have h3 := neg_log_epStar M (fdeg D.host.E) wg e.k0 hM hfw0 e.minWeight_pos e.k0_le
  have h4 : -Real.log e.k0 ≤ 3 * large₂.sc.L := by rw [one_div, Real.log_inv] at hk0; linarith
  have h5 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h6 : max 0 (Real.log M + Real.log ((fdeg D.host.E : ℝ) * wg + 2) + Real.log 2) ≤ 32 * large₂.sc.L + 1 :=
    max_le (by linarith) (by linarith)
  rw [← hepdef] at h3
  linarith

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NoBase
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def SaSpanSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → DF w + 2 ≤ qq D →
    ∀ P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n,
      P ∈ Submodule.span T.Q.c.F {Q | Q ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧
        ∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w}

theorem noBase_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end Lin

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NonzeroDivisorOfConnected
section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem nonzero_divisor_of_connected : ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt :=
  nzdOfComp_of_conn fun _ _ _ _ r X => (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaNuPf
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem cast_cancel {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (k : ℕ) {L1 L2 : RigLB G}
    (e : L1 = L2) (θ : LB.Sec (LB.LinComb L2.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) :
    (e ▸ (e.symm ▸ θ : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))) = θ := by
  subst e; rfl

theorem thetaNu : ThetaNuSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ θ θK htie
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  let σ' : LB.Sec (LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))) :=
    P.bundle.symm ▸ θ
  let s : P.U.SecK 1 := TG.secK P.U.toUnifPre σ'
  have hs := TG.secK_rel P.U.toUnifPre σ'
  obtain ⟨Ex, hEx, -⟩ := (P.U.expand 1 le_rfl).1 s
  have hnu := expansion_nonneg_regular V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U 1 rfl σ' s hs Ex hEx
  refine ⟨s, Ex, fun Z r zp hzp z J J' hJ hJ' => ?_, hEx, hnu⟩
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) 1 P.bundle s σ' hs
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst, cast_cancel 1 P.bundle θ] at e1
  exact e1.symm.trans (htie Z r zp hzp z J J' hJ hJ')

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem l2_norm_fundamental_domain (T : PT E) (s : (Fin 1 → Vsp T.dim) → ℂ) (hs : s ∈ T.Sec 1 1) {g : ℕ}
    (L : (Fin g → ℂ) ≃ₗ[ℝ] Vsp T.dim) (Λg : AddSubgroup (Fin g → ℂ)) (hΛ : ∀ γ, γ ∈ T.L ↔ L.symm γ ∈ Λg)
    (Fd : Set (Fin g → ℂ)) (hFd : IsAddFundamentalDomain Λg Fd volume) (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ z, ‖s (fun _ => L z)‖ = ‖θ z‖) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ z, (hermForm Hm z z).re = ‖L z‖ ^ 2)
    (hc9 : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1) :
    T.l2 1 s = 1 := by
  set F : Vsp T.dim → ℂ := fun v => s (fun _ => v) with hFdef
  set G : Vsp T.dim → ℝ := (PfSupSec.toGT T).ptN2 1 F with hGdef
  have hint : ∀ z, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = G (L z) := by
    intro z
    rw [← hθ z, hH, hGdef]
    simp [GT.ptN2, hFdef]
  simp only [hint] at hc9

  let e : (Fin g → ℂ) ≃L[ℝ] Vsp T.dim := L.toContinuousLinearEquiv
  let em : (Fin g → ℂ) ≃ᵐ Vsp T.dim := e.toHomeomorph.toMeasurableEquiv
  have hem : ∀ z, em z = L z := fun z => rfl
  set μ : Measure (Vsp T.dim) := Measure.map em volume with hμdef
  have : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hμ : μ = Measure.addHaarScalarFactor μ volume • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  set c := Measure.addHaarScalarFactor μ volume with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  set Fd' : Set (Vsp T.dim) := em.symm ⁻¹' Fd with hFd'def
  have hpre : em ⁻¹' Fd' = Fd := by rw [hFd'def]; exact em.preimage_symm_preimage Fd
  have I1 : ∫ z in Fd, G (L z) = (c : ℝ) * ∫ v in Fd', G v := by
    have h1 := setIntegral_map_equiv em G Fd' (μ := volume)
    rw [hpre] at h1
    simp only [hem] at h1
    rw [← h1, ← hμdef, hμ, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have V1 : (volume Fd).toReal = (c : ℝ) * (volume Fd').toReal := by
    have h1 : μ Fd' = volume Fd := by rw [hμdef, MeasurableEquiv.map_apply, hpre]
    rw [← h1, hμ, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]

  let eq : ↥(lat T.b) ≃ ↥Λg :=
    { toFun := fun γ => ⟨L.symm γ, (hΛ γ).1 γ.2⟩
      invFun := fun p => ⟨L p, (hΛ (L p)).2 (by simpa using p.2)⟩
      left_inv := fun γ => by ext1; simp
      right_inv := fun p => by ext1; simp }
  have hqmp : Measure.QuasiMeasurePreserving em.symm volume volume := by
    refine ⟨em.symm.measurable, ?_⟩
    have : (Measure.map em.symm (volume : Measure (Vsp T.dim))).IsAddHaarMeasure :=
      e.symm.isAddHaarMeasure_map volume
    rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.map em.symm (volume : Measure (Vsp T.dim))) volume]
    exact Measure.smul_absolutelyContinuous
  have hFd2 : IsAddFundamentalDomain ↥(lat T.b) (em.toEquiv '' Fd) volume :=
    hFd.image_of_equiv em.toEquiv hqmp eq (fun γ z => by
      show L (L.symm γ + z) = (γ : Vsp T.dim) + L z
      rw [map_add, LinearEquiv.apply_symm_apply])
  have himg : em.toEquiv '' Fd = Fd' := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      show em.symm (em z) ∈ Fd
      simpa using hz
    · intro hv
      exact ⟨em.symm v, hv, by simp⟩
  rw [himg] at hFd2
  haveI : VAddInvariantMeasure ↥(lat T.b) (Vsp T.dim) volume :=
    ⟨fun γ s _ => measure_preimage_add volume (γ : Vsp T.dim) s⟩
  have hstd : IsAddFundamentalDomain ↥(lat T.b) (ZSpan.fundamentalDomain T.b) volume :=
    ZSpan.isAddFundamentalDomain T.b volume
  have hper : ∀ (γ : ↥(lat T.b)) (v : Vsp T.dim), G (γ +ᵥ v) = G v := fun γ v =>
    ReciprocityTheory.ChartRestriction.G.I2.lemS_periodic (PfSupSec.toGT T) 1 (PfSupSec.sec_mem T hs) γ.2 v
  have hI : ∫ v in Fd', G v = ∫ v in ZSpan.fundamentalDomain T.b, G v := hFd2.setIntegral_eq hstd hper
  have hV : volume Fd' = volume (ZSpan.fundamentalDomain T.b) := hFd2.measure_eq hstd
  rw [PfSupSec.symmetricMeasure_l2Norm_eq_resolutionL2]
  show ⨍ v in ZSpan.fundamentalDomain T.b, G v = 1
  rw [setAverage_eq, measureReal_def, ← hV, ← hI]
  rw [I1, V1] at hc9
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  by_cases h0 : (volume Fd').toReal = 0
  · rw [h0, mul_zero, div_zero] at hc9; exact absurd hc9 zero_ne_one
  rw [mul_div_mul_left _ _ hc'.ne'] at hc9
  rw [smul_eq_mul, ← hc9]
  field_simp

def conjL (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' := fun r z => by ext i; simp
  left_inv := star_star
  right_inv := star_star

lemma card_idx {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (A : TorusAt X x) :
    Fintype.card (Idx A.T.dim) = X.Ψ.card * r := by
  classical
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := by
    intro σ
    first
      | exact star_star σ
      | exact RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_add_sum_compl X.Ψ]
  have h1 : ∑ τ ∈ X.Ψ, A.T.dim τ = X.Ψ.card * X.p0 := by
    rw [Finset.sum_congr rfl fun τ hτ => A.dim_pos ⟨τ, hτ⟩, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ τ ∈ X.Ψᶜ, A.T.dim τ = X.Ψ.card * (r - X.p0) := by
    have h3 : ∑ τ ∈ X.Ψᶜ, A.T.dim τ = ∑ τ ∈ X.Ψ, A.T.dim (ComplexEmbedding.conjugate τ) := by
      refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
      · intro τ hτ
        rw [Finset.mem_compl] at hτ
        exact (X.cmType _).2 (by rwa [hcc])
      · intro τ hτ
        rw [Finset.mem_compl]
        exact (X.cmType τ).1 hτ
      · intro τ _; exact hcc τ
      · intro τ _; exact hcc τ
      · intro τ _; rw [hcc]
    rw [h3, Finset.sum_congr rfl fun τ hτ => A.dim_neg ⟨τ, hτ⟩, Finset.sum_const, smul_eq_mul]
  rw [h1, h2, ← mul_add, Nat.add_sub_cancel' X.p0_le]

lemma finrank_eq (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f]
  have hn : D.R.n = D.R.ord := rfl
  rw [hn]
  ring

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD in
theorem torusFrame (hTM : TorusMatchSt) (hHm : UnitHmSt) : TorusFrameSt := by
  intro D T h j hj σ hσ k xf hort
  obtain ⟨W, Wu, A, L, hpins⟩ := hTM D T h j hj σ hσ k xf hort
  have hφ := hpins.1
  have hH := hpins.2.1
  have hθ := hpins.2.2.1
  simp only [LinearEquiv.coe_coe] at hφ hH hθ
  refine ⟨W, Wu, A, L.toLinearMap, hpins, ?_, ?_, ?_⟩
  · let L' : (Fin W.g → ℂ) ≃ₗ[ℝ] Vsp A.T.dim := (conjL W.g).trans (L.restrictScalars ℝ)
    have hL' : ∀ z, L' z = L (star z) := fun z => rfl
    refine l2_norm_fundamental_domain A.T A.s A.s_mem L' W.Pm.range ?_ Wu.Fd Wu.c8 Wu.θ ?_ Wu.Hm ?_ Wu.c9
    · intro γ
      rw [A.lat γ]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(W.φ k).symm ⟨v, hv⟩, ?_⟩
        have e1 : A.φ v = L' (W.Pm ((W.φ k).symm ⟨v, hv⟩)) := by
          rw [hL', ← hφ]; simp
        rw [e1, LinearEquiv.symm_apply_apply]
      · rintro ⟨a, ha⟩
        refine ⟨_, (W.φ k a).2, ?_⟩
        rw [hφ a, ← hL', ha, LinearEquiv.apply_symm_apply]
    · intro z
      rw [hL', hθ, star_star, norm_star]
    · intro z
      rw [hL']
      have h1 := ChA.re_Hf (L (star z)) (L (star z))
      rw [hH, star_star, real_inner_self_eq_norm_sq] at h1
      rw [← h1]
      simp
  · intro i
    have h1 := hHm D T h j hj σ hσ k xf hort W Wu i
    have h2 := ChA.re_Hf (L (Pi.single i 1)) (L (Pi.single i 1))
    have hs : star (Pi.single i (1 : ℂ) : Fin W.g → ℂ) = Pi.single i 1 := by
      ext j'
      by_cases hij : j' = i <;> simp [hij]
    rw [hH, hs, real_inner_self_eq_norm_sq] at h2
    have h3 : ‖L (Pi.single i 1)‖ ^ 2 ≤ 1 := by rw [← h2]; simpa using h1
    show ‖L (Pi.single i 1)‖ ≤ 1
    nlinarith [norm_nonneg (L (Pi.single i 1))]
  · rw [card_idx]
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j σ).X k).cmType
    rw [finrank_eq D] at h2c
    have : ((T.U j σ).X k).Ψ.card = D.R.f := by omega
    rw [this]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame
end
end

