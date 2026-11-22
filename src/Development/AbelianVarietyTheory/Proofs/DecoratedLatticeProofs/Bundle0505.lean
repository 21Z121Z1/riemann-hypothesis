import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBaseTermUnfoldingCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem integral_base_term_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 hlay hfin
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank vb vU
  haveI : IsFiniteMeasure (vb.μ.restrict vb.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vb.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hψ1 : ∀ x, star (ψ x) * ψ x = 1 := fun x => by
    rw [Complex.star_def, Complex.conj_mul', hω.std.1.2.1 x]; norm_num
  have hq0 : d.qS W 0 (rat x₀) = 0 := by
    simp [HypDec.qS, symplOH, symplO, hO]
  set F : flagN d × GA D W → ℂ := fun p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ with hFdef
  have hFm : Measurable F := by
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hint : Integrable F ((vN.ν.restrict 𝓐).prod (vW.μ.restrict 𝓑)) := by
    rw [Measure.prod_restrict]
    exact ⟨hFm.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hpm : Measurable (Function.uncurry fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) :=
    (d.continuous_nB.measurable.comp measurable_snd).mul
      ((d.continuous_levi.comp continuous_subtype_val).measurable.comp measurable_fst)
  have hfib : ∀ h, Integrable (fun n => F (n, h)) (vN.ν.restrict 𝓐) →
      ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
    intro h hih
    classical
    have hΨ := hω.om_pres (1, h) Φ hΦ
    set f : GA D V → ℂ := (flagN d : Set (GA D V)).piecewise
      (fun g => Th g * G h * term ψ d W vS (om (g, h) Φ) x₀) 0 with hfdef
    have hfm : Measurable f := by
      refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)).measurableSet
      refine ((continuousOn_iff_continuous_restrict.2 hTh.cont).mul continuousOn_const).mul ?_
      exact (((hTL Φ hΦ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).continuousOn
    have hfF : ∀ n : flagN d, f n.1 = F (n, h) := fun n => Set.piecewise_eq_of_mem _ _ _ n.2
    have hcen : ∀ (c : skewA D ρ) (n : GA D V), n ∈ flagN d →
        term ψ d W vS (om (d.nC c * n, h) Φ) x₀ = ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀ := by
      intro c n hn
      have hΨ' := hω.om_pres (n, h) Φ hΦ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      rw [t1]
      simp [term]
    have hfinv : ∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)),
        f (t n) = f n := by
      rintro t ⟨c, rfl⟩ n hn
      have hm : d.nC c * n ∈ (flagN d : Set (GA D V)) := mul_mem (d.nC_mem_NFlag c) hn
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, Set.piecewise_eq_of_mem _ _ _ hn, hTh.cen c n hn, hcen c n hn]
      calc star (ψ (d.qS W c (rat x₀))) * Th n * G h * (ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀)
          = (star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x₀))) * (Th n * G h * term ψ d W vS (om (n, h) Φ) x₀) := by
            ring
        _ = _ := by rw [hψ1, one_mul]
    have hcoord : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        f (d.nB b * d.levi u.1) = G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b := by
      intro u b
      have hm : d.nB b * d.levi u.1 ∈ (flagN d : Set (GA D V)) := mul_mem (d.nB_mem_NFlag b) (d.levi_mem_NFlag u.2)
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul, hq0, AddChar.map_zero_eq_one, one_mul] at t1
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, hsplit, t1, flFun]
      ring
    have hlay' : ∀ g : GA D V → ENNReal, Measurable g →
        (∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)), g (t n) = g n) →
        ∫⁻ x, g (Subtype.val x) ∂(vN.ν.restrict 𝓐) =
          ∫⁻ u, ∫⁻ y, g ((fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) u y) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν :=
      fun g hg hinv => hlay g hg fun c n hn => hinv _ ⟨c, rfl⟩ n hn
    have hih' : Integrable (fun x : flagN d => f x.1) (vN.ν.restrict 𝓐) := by
      refine hih.congr (ae_of_all _ fun n => (hfF n).symm)
    obtain ⟨-, heq⟩ := GlobalTheory.T.lowerIntegral_to_integral_coordinates (flagN d) (UX D ρ) (Mx D ρ V₀.rank) (GA D V) (vN.ν.restrict 𝓐) vU.ν
      (vb.μ.restrict vb.𝓕) Subtype.val (fun u b => d.nB b * d.levi u.1) (fun t => ∃ c, t = (d.nC c * ·))
      measurable_subtype_coe hpm (flagN d) hlay' f hfm hfinv hih'
    calc ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = ∫ x, f x.1 ∂(vN.ν.restrict 𝓐) :=
          integral_congr_ae (ae_of_all _ fun n => (hfF n).symm)
      _ = ∫ u, ∫ b, f (d.nB b * d.levi u.1) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := heq
      _ = ∫ u, ∫ b, G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          exact integral_congr_ae (ae_of_all _ fun b => hcoord u b)
      _ = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
          simp only [integral_const_mul]; rfl
  have hae := hint.prod_left_ae
  have hI := hint.integral_prod_right
  have hEq : (fun h => ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐)) =ᵐ[vW.μ.restrict 𝓑]
      fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := hae.mono fun h hh => hfib h hh
  refine ⟨hI.congr hEq, ?_⟩
  rw [← Measure.prod_restrict, integral_prod_symm F hint]
  exact integral_congr_ae hEq

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have h1 : (d.pX ⬝ d.jX) i i = 1 := by rw [d.pX_jX]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : Pl D) (hL : MonoAt d L M v)
    (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSmallPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def ker {A S X : HSp D} (oma : Om A S) (omX : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omX (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

theorem biLift_eq {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ C h₂ = ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ := rfl

section

variable {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omX : Om S X}

theorem ker_sum {n : ℕ} (C : Fin n → WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX (∑ i, C i) h₀ h₁ h₂ = ∑ i, ker oma omX (C i) h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (∑ i, C i) u v) 0) = ∑ i, fun v => oma (h₀, h₁) (fun u => C i u v) 0 := by
    funext v
    have e : (fun u => (∑ i, C i) u v) = ∑ i, fun u => C i u v := by
      funext u; simp only [Finset.sum_apply]
    rw [e, map_sum]; simp only [Finset.sum_apply]
  rw [e1, map_sum]; simp only [Finset.sum_apply]

theorem ker_cont (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) :
    Continuous fun x : GA D A × GA D S × GA D X => ker oma omX C x.1 x.2.1 x.2.2 := by
  have := (hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).2.2.2
  exact this.comp (by fun_prop : Continuous fun x : GA D A × GA D S × GA D X =>
    ((x.1, x.2.1), (x.2.1, x.2.2), ((0 : WO A S), (0 : WO S X))))

theorem ker_left (hwa : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    {γ : GA D A} (hγ : γ ∈ GQ A) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX C (γ * h₀) h₁ h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (γ * h₀, h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((γ * h₀, h₁) : GA D A × GA D S) = (γ, 1) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut γ hγ 1 (one_mem _) _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  rw [e1]

theorem ker_mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {γ : GA D S} (hγ : γ ∈ GQ S) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ (γ * h₁) h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, γ * h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((h₀, γ * h₁) : GA D A × GA D S) = (1, γ) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut 1 (one_mem _) γ hγ _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((γ * h₁, h₂) : GA D S × GA D X) = (γ, 1) * (h₁, h₂) := by simp
  rw [e1, e, map_mul, Module.End.mul_apply, hwX.om_aut γ hγ 1 (one_mem _) _ (hwX.om_pres _ _ hth)]

theorem ker_right (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {δ : GA D X} (hδ : δ ∈ GQ X) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ h₁ (δ * h₂) = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((h₁, δ * h₂) : GA D S × GA D X) = (1, δ) * (h₁, h₂) := by simp
  rw [e, map_mul, Module.End.mul_apply, hwX.om_aut 1 (one_mem _) δ hδ _ (hwX.om_pres _ _ hth)]

theorem inner (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (vA : Vol A) {φ : GA D A → ℂ}
    (hφ : IsContAut A φ) :
    (∀ h₁ h₂, IntegrableOn (fun h₀ => φ h₀ * ker oma omX C h₀ h₁ h₂) vA.𝓕 vA.μ) ∧
      Continuous fun p : GA D S × GA D X => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ p.1 p.2 ∂vA.μ := by
  have hc : Continuous (Function.uncurry fun (g : GA D A) (p : GA D S × GA D X) => φ g * ker oma omX C g p.1 p.2) := by
    show Continuous fun q : GA D A × (GA D S × GA D X) => φ q.1 * ker oma omX C q.1 q.2.1 q.2.2
    exact (hφ.2.comp continuous_fst).mul ((ker_cont hB hwa hwX hC).comp
      (by fun_prop : Continuous fun q : GA D A × (GA D S × GA D X) => (q.1, q.2.1, q.2.2)))
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA (GA D S × GA D X) (fun g p => φ g * ker oma omX C g p.1 p.2) hc
    (fun γ hγ g p => by rw [hφ.1 γ hγ g, ker_left hwa hC hγ])
  exact ⟨fun h₁ h₂ => H.1 (h₁, h₂), H.2.1⟩

theorem mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    (∀ h₂, IntegrableOn (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) vS.𝓕 vS.μ) ∧
      Continuous fun h₂ => biLift oma omX vA vS φ C h₂ := by
  have H := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D X) (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ)
    (inner hB hwa hwX hC hA vA hφ).2 (fun γ hγ g p => by simp only [ker_mid hB hwa hwX hC hγ])
  exact ⟨H.1, H.2.1⟩

theorem outer (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) {T L'' : HSp D} (hT : CoCpt T)
    (vA : Vol A) (vS : Vol S) (vT : Vol T) (o'' : OrthDec X T L'') {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {F : GA D T → ℂ} (hF : IsContAut T F) :
    IntegrableOn (fun h' => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1))) vT.𝓕 vT.μ := by
  have hc := (mid hB hwa hwX hC hA hS vA vS hφ).2
  have hc' : Continuous fun h' : GA D T => biLift oma omX vA vS φ C (o''.emb (h', 1)) :=
    hc.comp (o''.continuous_emb.comp (by fun_prop : Continuous fun h' : GA D T => ((h', 1) : GA D T × GA D L'')))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D T hT vT Unit (fun h' _ => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1)))
    ((hF.2.mul hc').comp continuous_fst) (fun γ hγ g _ => ?_)).1 ()
  have e : ((γ * g, 1) : GA D T × GA D L'') = (γ, 1) * (g, 1) := by simp
  have hδ : o''.emb (γ, 1) ∈ GQ X := o''.emb_mem_GQ hγ (one_mem _)
  rw [hF.1 γ hγ g, e, map_mul, biLift_eq, biLift_eq]
  simp only [ker_right hB hwa hwX hC hδ]

theorem biLift_sum (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ) {n : ℕ}
    (C : Fin n → WO A S → WO S X → ℂ) (hC : ∀ i, IsBiTheta ψ A S X (C i)) (h₂ : GA D X) :
    biLift oma omX vA vS φ (∑ i, C i) h₂ = ∑ i, biLift oma omX vA vS φ (C i) h₂ := by
  have e1 : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (∑ i, C i) h₀ h₁ h₂ ∂vA.μ =
      ∑ i, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (C i) h₀ h₁ h₂ ∂vA.μ := by
    intro h₁
    simp only [ker_sum, Finset.mul_sum]
    exact integral_finset_sum _ fun i _ => (inner hB hwa hwX (hC i) hA vA hφ).1 h₁ h₂
  rw [biLift_eq]
  simp only [e1]
  rw [integral_finset_sum _ fun i _ => (mid hB hwa hwX (hC i) hA hS vA vS hφ).1 h₂]
  rfl

end

theorem seeSmall : ∀ D : D7, SeeSmall D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ hA hS hT χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hTw hz''
    vA vS vT N Ξ Φ₂ hΞΦ φ F hφ hF
  have hB : BiAct D := GlobalTheory.T.seeSawWeilBiAction_commutes D
  have hSL := GlobalTheory.T.lastSeeSaw_thetaIdentity D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX
    hTw hz''
  have hC : ∀ i, IsBiTheta ψ A S X (lastBi o o'' τ (Ξ i) (Φ₂ i)) := fun i =>
    GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction D ψ h₁.std V₀ A L S X T L'' o o'' τ hτ (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2
  have e0 : (o.resS S).symm (0, 0) = 0 := by rw [← Prod.zero_eq_mk, map_zero]
  have hpt : ∀ i h', biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) =
      ∫ h in vS.𝓕, omT (h, h') (Φ₂ i) 0 * liftA o om₁ vA φ (Ξ i) h 0 ∂vS.μ := by
    intro i h'
    rw [biLift_eq]
    congr 1
    funext h
    simp only [liftA, e0]
    rw [← integral_const_mul]
    congr 1
    funext h₀
    have key : oma (h₀, h) (fun u' => omX (h, o''.emb (h', 1)) (lastBi o o'' τ (Ξ i) (Φ₂ i) u') 0) 0 =
        omT (h, h') (Φ₂ i) 0 * om₁ (o.emb (h₀, 1), h) (Ξ i) 0 :=
      ((hSL (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2).2 h₀ h h').symm
    have hk := (hB ψ A S X χA χS χS' (χT * χz⁻¹) oma omX ha hX _ (hC i)).2.2.1 (h₀, h) (h, o''.emb (h', 1)) 0 0
    simp only [ker]
    rw [hk, key]
    ring
  have hsum : ∀ h₂, biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ =
      ∑ i, biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ := fun h₂ =>
    biLift_sum hB ha hX hA hS vA vS hφ (fun i => lastBi o o'' τ (Ξ i) (Φ₂ i)) hC h₂
  simp only [hsum, Finset.mul_sum]
  rw [integral_finset_sum _ fun i _ => outer hB ha hX (hC i) hA hS hT vA vS vT o'' hφ hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smallPair, hpt]

end GlobalTheory.SeeSmallPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

open AddMonoidAlgebra in
theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (aconv (e :: l)) : AddMonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (aconv l) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

theorem aconv_nil {G : Type} [AddMonoid G] :
    (AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) : AddMonoidAlgebra ℂ G) = 1 := rfl

theorem aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) :
    (AddMonoidAlgebra.ofCoeff (aconv [c, d]) : AddMonoidAlgebra ℂ G) =
      AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d := by
  rw [aconv_cons, aconv_cons, aconv_nil, mul_one]

theorem aconv_pair_cons {G : Type} [AddMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (aconv [c, d] :: l) = aconv (c :: d :: l) := by
  apply (AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G))
  rw [aconv_cons, aconv_pair, aconv_cons, aconv_cons, mul_assoc]

theorem mem_support_aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) {u : G} (hu : u ∈ (aconv [c, d]).support) :
    ∃ a ∈ c.support, ∃ b ∈ d.support, a + b = u := by
  classical
  have h : (AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d : AddMonoidAlgebra ℂ G).coeff u ≠ 0 := by
    rw [← aconv_pair]; exact Finsupp.mem_support_iff.1 hu
  rw [AddMonoidAlgebra.coeff_mul] at h
  simp only [AddMonoidAlgebra.coeff_ofCoeff] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hab : a + b = u
  · exact ⟨a, ha, b, hb, hab⟩
  · exact absurd (if_neg hab) h2

open MonoidAlgebra in
theorem conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (conv (e :: l)) : MonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (conv l) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
  simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_ofCoeff]
  rfl

theorem conv_nil {G : Type} [Monoid G] :
    (MonoidAlgebra.ofCoeff (conv ([] : List (G →₀ ℂ))) : MonoidAlgebra ℂ G) = 1 := rfl

theorem mul_comm_of_support {G : Type} [Monoid G] (a b : MonoidAlgebra ℂ G)
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, x * y = y * x) : a * b = b * a := by
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.mul_def]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  dsimp only
  rw [h x hx y hy, mul_comm (a.coeff x)]

theorem comm_conv {G : Type} [Monoid G] (E : G →₀ ℂ) (l : List (G →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) :
    (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff (conv l) =
      MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E := by
  induction l with
  | nil => rw [conv_nil, mul_one, one_mul]
  | cons e l ih =>
    have h1 : (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff e =
        MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff E :=
      mul_comm_of_support _ _ fun x hx y hy => h x hx e List.mem_cons_self y hy
    rw [conv_cons, ← mul_assoc, h1, mul_assoc, ih fun x hx e' he' y hy => h x hx e' (List.mem_cons_of_mem _ he') y hy,
      mul_assoc]

section Trc
variable {D : D7} {V : HSp D}

theorem trc_eq_sum (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_single (g : GA D V) (a : ℂ) (f : GA D V → ℂ) : trc (Finsupp.single g a) f = a • rTrans g f := by
  rw [trc_eq_sum, Finsupp.sum_single_index]
  exact zero_smul _ _

theorem trc_zero (f : GA D V → ℂ) : trc (0 : GA D V →₀ ℂ) f = 0 := by
  simp [trc]

theorem trc_add (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (e + e') f = trc e f + trc e' f := by
  simp only [trc_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem trc_apply (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) : trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, Finset.sum_apply, rTrans]

theorem trc_add_right (e : GA D V →₀ ℂ) (f f' : GA D V → ℂ) : trc e (f + f') = trc e f + trc e f' := by
  funext x
  simp only [trc_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem trc_zero_right (e : GA D V →₀ ℂ) : trc e (0 : GA D V → ℂ) = 0 := by
  funext x
  simp [trc_apply]

theorem trc_mul (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc (MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff e' : MonoidAlgebra ℂ (GA D V)).coeff f = trc e (trc e' f) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [MonoidAlgebra.ofCoeff_zero, zero_mul, MonoidAlgebra.coeff_zero, trc_zero, trc_zero]
  | add x y hx hy =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add, trc_add, trc_add, hx, hy]
  | single g a =>
    induction e' using Finsupp.induction_linear with
    | zero => rw [MonoidAlgebra.ofCoeff_zero, mul_zero, MonoidAlgebra.coeff_zero, trc_zero, trc_zero_right]
    | add x y hx hy =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, MonoidAlgebra.coeff_add, trc_add, hx, hy, trc_add, trc_add_right]
    | single h b =>
      rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.coeff_single, trc_single, trc_single, trc_single]
      funext x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem contAut_trc (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ x => ?_, ?_⟩
  · simp only [trc_apply, mul_assoc, hf.1 γ hγ]
  · have : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := funext (trc_apply e f)
    rw [this]
    exact continuous_finset_sum _ fun g _ => (GlobalTheory.Core.Mi.BotPin.isContAut_rTrans g hf).2.const_smul (e g)

end Trc

end GlobalTheory.QValOuter
end
end

