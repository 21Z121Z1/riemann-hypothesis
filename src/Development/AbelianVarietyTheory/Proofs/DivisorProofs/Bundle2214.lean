import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0047
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesNearbyFramesOfDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
section
noncomputable section

namespace GlobalTheory.KeyArchNorm

section Value

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth

theorem norm_rule_of_coord {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) (x : KeyIn ℂ) {g : ℕ}
    (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {θ : (Fin g → ℂ) → ℂ} {Fd : Set (Fin g → ℂ)} {ξ : ℝ} (hξ : 0 < ξ) (p : Fin x.P.g ≃ Fin g)
    (hA : u.IsAH Hm χ) (hR : u.IsRig x.rig) (hF : u.IsFn x.th θ) (hD : ∀ i, u.IsDiff (Pi.single (p i) 1) (x.v i))
    (hFd : IsAddFundamentalDomain u.Λ Fd volume)
    (hN : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1)
    (hH : Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    ‖(κ ℂ x : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  subst hg
  obtain ⟨⟨Ef, hE, hb⟩, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  have := u.discrete
  have hv := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 hE hb hFd
  have hd : Hm.det.re = (2 * ξ) ^ x.P.g := by
    rw [hH, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  let W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => Pi.single (p i) 1
  have hW : ‖W.det‖ = 1 := by
    have e : W = (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ).submatrix p id := by
      ext i j
      simp [W, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [e, Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have key := hκ x u Hm W χ θ Fd 1 _ hA hR hF hD hFd hN.symm rfl
  rw [hd] at hv
  rw [hW, eq_inv_of_mul_eq_one_left hv] at key
  have hπ := Real.pi_pos
  simp only [mul_one, one_pow] at key
  rw [← key]
  simp only [mul_pow, pow_mul']
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem norm_rule_of_isOrtho {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (h0 : 0 < ξ)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ)
    (hx : (U.X k).IsOrtho x.1) (Φ : FibKey Xo ℂ (U.un k x).x)
    (hΦ : Tied (S := ℂ) e (U.un k x).s (U.un k x).u Φ) :
    ‖(κ ℂ Φ.key : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  obtain ⟨ht, hg, hv⟩ := hΦ
  subst hg
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have key := norm_rule_of_coord hκ Φ.key hg u h0 (e.trans W.e.symm) hA hR hF (fun i => by
    obtain ⟨w, hw, hd⟩ := hD _ _ ((U.un k x).tan (e i).1 (e i).2) (W.der (e i).1 (e i).2)
    have hwv : w = Φ.v i :=
      Over.OverMorphism.ext (Φ.m.cart.1.hom_ext (hw.trans (hv i).symm) ((Over.w w).trans (Over.w (Φ.v i)).symm))
    rw [hwv] at hd
    exact hd) hFd Wu.c9 hH
  rw [hg] at key
  exact key

end Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 (-4)).1 (τ, i) = 4 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
    rw [wtOf_big _ _ ⟨τ, h⟩ i hp]
    simp
  · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
    have e := wtOf_small (Dw := Dw) 0 (-4) ⟨conjEmb τ, conj_mem h⟩ i hq
    simp only [conjEmb_conjEmb] at e
    rw [e]
    simp

theorem exZ_wtOf : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact wtOf_fst τ i i.2

theorem lieFacZ_mul {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {x : ℝ} (hx : 0 < x) :
    lieFacZ Dw x (wtOf Dw 0 (-4)) * (2 * Real.pi * x) ^ (2 * g) = 1 := by
  have hg : ∑ τ : E →+* ℂ, Dw.mult τ = g := by
    have := Fintype.card_congr e
    simpa using this.symm
  have hs : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), ((wtOf Dw 0 (-4)).1 (τ, i) : ℝ)) = 4 * g := by
    rw [← hg, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl fun (i : Fin (Dw.mult τ)) _ => by rw [wtOf_fst τ i i.2]]
    simp [mul_comm]
  have hπ : 0 < 2 * Real.pi * x := by positivity
  rw [lieFacZ, hs, ← Real.exp_log (pow_pos hπ (2 * g)), ← Real.exp_add, Real.log_pow, Real.exp_eq_one_iff]
  push_cast
  ring

end Weight

theorem homN_key_const : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  intro κ _ _ hκ E _ _ _ H Dw l Xo c g e σ r U x K hσ hU hx hS hpq hK hval
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ (2 * g), by positivity, ?_, fun k y hy => ?_⟩
  · rw [abs_of_nonneg (Real.log_nonneg (one_le_pow₀ hπ)), Real.log_pow]
    push_cast
    exact le_rfl
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r U hS hσ hU hpq (wtOf Dw 0 (-4)) (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_fst τ j hj, wtOf_fst τ i (hij.trans_lt hj)]) K (exZ_wtOf (Dw := Dw) ▸ hK) k
  have hb := FrameDegreeData.bOf_mem (U.X k) hy
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) hy hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) hy
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 y hy _ hb
  generalize rmul y (FrameDegreeData.bOf (U.X k) y) = z at hz ho hp
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : 0 < x := hx k τ₀ ▸ norm_pos_iff.2 ((map_ne_zero τ₀).2 (U.X k).ξ0_ne)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : FibKey Xo ℂ (U.un k ⟨z, hz⟩).x, Tied (S := ℂ) e (U.un k ⟨z, hz⟩).s (U.un k ⟨z, hz⟩).u Φ :=
    @GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) hpq
  have hv : rdU U (K : Rul Xo c) k z = (κ ℂ Φ.key : ℂ) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact @hval ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) Φ hΦ
  have hn : (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) z = ‖(κ ℂ Φ.key : ℂ)‖ := by
    simp [Data.pnorm, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho, hv]
  show lieFacZ Dw x _ * (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) y = _
  rw [← hp, hn, norm_rule_of_isOrtho hκ e h0 hσ hU k ⟨z, hz⟩ (hx k) ho Φ hΦ, mul_left_comm, lieFacZ_mul e h0, mul_one]

end GlobalTheory.KeyArchNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaLow
open GlobalTheory.ThetaBound GlobalTheory.PlaceInt

theorem finite_vLa_ne_zero {K : Type} [Field K] [NumberField K] (x : K) :
    {w : HeightOneSpectrum (𝓞 K) | vLa w x ≠ 0}.Finite := by
  by_cases hx : x = 0
  · subst hx
    convert Set.finite_empty
    ext w
    simp [vLa]
  · refine (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 x hx)).subset fun w hw h1 => hw ?_
    simp only [Units.val_mk0] at h1
    simp [vLa, h1]

theorem vLa_natCast_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g p : ℕ}
    (hg : ((g : ℕ) : 𝓞 K) ∈ w.asIdeal) (hc : Nat.Coprime g p) : vLa w ((p : ℕ) : K) = 0 := by
  have hp : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hp
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg) (Ideal.mul_mem_left _ _ hp)
  have h1 : w.valuation K ((p : ℕ) : K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hp
  simp [vLa, h1]

theorem thetaRule_bounded_below : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (g g' : ℕ) (π π' : 𝓞 D.host.E), HalfSplit l g g' π π' → Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ m : HeightOneSpectrum (𝓞 c.F) → ℝ, (Function.support m).Finite ∧ (∀ f ∈ thGen Xo c nab a n, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) ∧ ∀ w : HeightOneSpectrum (𝓞 c.F), (((g : ℕ) : 𝓞 c.F) ∈ w.asIdeal ∨ ((g' : ℕ) : 𝓞 c.F) ∈ w.asIdeal) → m w = -((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ) := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro nab hnab g g' π π' hs hcop a n
  have hstar : ∀ x : 𝓞 D.host.E, star x = H.bar x := hnab.1
  obtain ⟨hg, hg', hne, hM, hπ, hπ', hMb, -, -⟩ := hs
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ
    exact hg.ne_zero (by exact_mod_cast hπ.symm)
  have hπ0' : π' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ'
    exact hg'.ne_zero (by exact_mod_cast hπ'.symm)
  have hb0 : star π * star π' ≠ 0 := by
    rw [hstar, hstar]
    refine mul_ne_zero (fun h => hπ0 ?_) (fun h => hπ0' ?_)
    · rw [← TorsFac.bar_bar (H := H) π, h, map_zero]
    · rw [← TorsFac.bar_bar (H := H) π', h, map_zero]
  let ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ p ∈ D.host.condN.primeFactors, ((vLa w ((p : ℕ) : c.F) : ℤ) : ℝ) *
      D.host.vdH p * (Formalism.L2.Pj.DF Dw a : ℝ) / 2
  refine ⟨fun w => -(ρ w + ((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ)), ?_, ?_, ?_⟩
  ·
    have hfin : ((⋃ p ∈ D.host.condN.primeFactors,
        {w : HeightOneSpectrum (𝓞 c.F) | vLa w ((p : ℕ) : c.F) ≠ 0}) ∪
        {w | vLa w (nrm Dw c a (star π * star π')) ≠ 0}).Finite :=
      (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => finite_vLa_ne_zero _).union (finite_vLa_ne_zero _)
    refine hfin.subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hn
    apply hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by rw [hn.1 p hp]; simp
    simp [h0, hn.2]
  · intro f hf w v hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨T, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
    have hv : vAtV y f = nval T.V e (evI yI f) := by
      show y.1.1 f = _
      rw [hq]
      rfl
    rw [hv]
    refine bound_of_chBound Xo c (star π * star π') hb0 ?_ nab hnab w a n (ρ w) ?_ T io e ho yI hy f hf
    · intro ℓ hp hd
      rw [hM] at hd ⊢
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg').1 h1
        refine ⟨fun h2 => hne ?_, star π', star π, _root_.mul_comm _ _, ?_, ?_⟩
        · rw [pow_two] at h2
          exact ((Nat.prime_dvd_prime_iff_eq hg' hg).1 (Nat.dvd_of_mul_dvd_mul_left hg'.pos h2)).symm
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ'
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro_left _ rfl
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg).1 h1
        refine ⟨fun h2 => hne ?_, star π, star π', rfl, ?_, ?_⟩
        · rw [pow_two] at h2
          exact (Nat.prime_dvd_prime_iff_eq hg hg').1 (Nat.dvd_of_mul_dvd_mul_right hg.pos h2)
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro _ rfl
    · intro T' io' y' C' e' ho'
      have hc := HostChart.chBound_host D H Dw l Xo c hstar T' io' y' C' e' ho'.1 a n
        (Formalism.L2.Pj.DF Dw a) le_rfl
      convert hc using 1
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 := ho'.2 ((p : ℕ) : c.F)
      rw [map_natCast] at h1
      have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
      rw [h1]
      push_cast
      rw [mul_div_cancel_left₀ _ he]
  · intro w hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by
      have hcp : Nat.Coprime (g * g') p := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) hcop
      rcases hw with hw | hw
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_right g g') hcp)]; simp
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_left g' g) hcp)]; simp
    show -(ρ w + _) = _
    rw [h0, zero_add]
end GlobalTheory.ThetaLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

theorem toNat_floor_cast {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem eQ_succ (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) : DV.eQ D ((i : ℕ) + 1) t = (D.hc t).e i := by
  unfold DV.eQ
  rw [dif_pos ⟨Nat.le_add_left _ _, i.2⟩]
  rfl

theorem lamAt_eq (D : D7) (t : D.what₂.Tau) (n : ℕ) : Formalism.L2.NTheta.lamAt (D.hc t) n = DV.sigPar D t n := rfl

theorem aPl_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) t n : ℚ) =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k : ℚ) + i) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have e : DV.aPlusQ D ((i : ℕ) + 1) t n =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [DV.aPlusQ_eq, eQ_succ]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aPlusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t ⟨n, hn⟩
  have h2 := DV.aPlusQ_int D ((i : ℕ) + 1) t n
  unfold aPl
  rw [if_pos hn, lamAt_eq, ← e, toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem aMi_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (c : ℕ) (hc : (i : ℕ) + 1 + c < D.R.m) :
    (aMi D i (D.R.k + i) (D.R.m - ((i : ℕ) + 1)) t (D.R.m - ((i : ℕ) + 1) - 1 - c) : ℚ) =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have e0 : D.R.m - ((i : ℕ) + 1) - (D.R.m - ((i : ℕ) + 1) - 1 - c) = c + 1 := by omega
  have e1 : DV.sigPar D t (D.R.k + i + c) = -(D.hc t).b ⟨(i : ℕ) + 1 + c, hc⟩ := by
    unfold DV.sigPar
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 3
    omega
  have e : DV.aMinusQ D ((i : ℕ) + 1) t c =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
    unfold DV.aMinusQ
    rw [dif_pos hc, eQ_succ, e1]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aMinusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) t c hc
  have h2 := DV.aMinusQ_int D ((i : ℕ) + 1) t c
  unfold aMi
  rw [if_pos (by omega), e0, lamAt_eq, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, ← e,
    toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem nV_half (R : Ranks) : ((R.nV / 2 : ℕ) : ℚ) = ((R.r : ℚ) + R.t) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hm := R.two_le_m
  have h1 : R.r + R.t = 2 * (R.nV / 2) := by unfold Ranks.nV Ranks.r; omega
  have h2 : (R.r : ℚ) + R.t = 2 * ((R.nV / 2 : ℕ) : ℚ) := by exact_mod_cast h1
  linarith

def ent (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℚ :=
  DV.sigPar D t n + (D.hc t).e i + n - ((D.R.k : ℚ) + i) + ((D.R.r : ℚ) + 1) / 2 - if n < D.R.k + i then 0 else (D.R.r : ℚ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem inR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

theorem dat_p : (dat p i).p = D.R.k + i := (p.fw.laws.pins.2.2.2 _ (inR i)).1

theorem dat_q : (dat p i).q = D.R.m - ((i : ℕ) + 1) := (p.fw.laws.pins.2.2.2 _ (inR i)).2.1

theorem dat_rank : (dat p i).p + (dat p i).q = D.R.r := by
  have := i.2
  rw [dat_p, dat_q]; unfold Ranks.r; omega

theorem exists_tau (τ : Psi p.T.Q.H) : ∃ t, τ.1 = DV.tauEmb D t :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q p.fw.laws.pins.1 τ.1 τ.2

theorem card_psi : Nat.card (Psi p.T.Q.H) = D.R.f := by
  have hp := p.fw.laws.pins.1
  have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hp.2.2.2 t⟩ : Psi p.T.Q.H)) :=
    ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => by
      obtain ⟨t, ht⟩ := exists_tau p τ
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]

theorem dim_eq : dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  unfold dimFlag Formalism.DegreeFormula.dimFl
  rw [dat_rank, ← Nat.card_eq_fintype_card, card_psi, Nat.choose_two_right]

theorem cols_eq : (p.κ i).n = D.R.nV := by
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega)
  obtain ⟨t⟩ := hne
  exact (p.fw.kap i t).2.2

theorem unit_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem laOf_read (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℚ) = ent D i t n := by
  have hp := p.fw.laws.pins.1
  have hs : (Wc D i).sig (TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨k1, k2, -⟩ := p.fw.kap i t
  rw [hs] at k1 k2
  have s1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have s2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hn := n.2
  have e1 := dat_p p i
  have e2 := dat_q p i
  have hh := nV_half D.R
  unfold laOf weightOf ent
  rw [cols_eq, ht]
  beta_reduce
  by_cases h : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h, GlobalTheory.WeightExponents.wtA_tauEmb hp, ext0, dif_pos (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), k1]
    have := aPl_cast D i t n h
    simp only [Int.cast_add, Int.cast_natCast, s1]
    rw [this, hh]; ring
  · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + c := ⟨n - (D.R.k + i), by omega⟩
    have e3 : (dat p i).q - 1 - ((n : ℕ) - (dat p i).p) = D.R.m - ((i : ℕ) + 1) - 1 - c := by omega
    rw [if_neg (by omega), if_neg h, e3, conjEmb, GlobalTheory.WeightExponents.conjEmb_eq, GlobalTheory.WeightExponents.wtA_conj hp, ext0,
      dif_pos (show D.R.m - ((i : ℕ) + 1) - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 by omega), k2]
    have := aMi_cast D i t c (by omega)
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, s1, s2]
    rw [this, hh, hc]; push_cast; ring

end GlobalTheory.CovTop.WtShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesNearbyFramesOfDenseStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transporter_moves_nearby_frames_of_dense : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → (closure {z | ∃ hz : z ∈ ((uAt r v i).X k).dom, MovesAt p r i v γ k k' a hm z hz} ∈ nhds x → ∃ N ∈ nhds x, ∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ N → MovesAt p r i v γ k k' a hm z hz) ∧ ∃ (k'' : (uAt r v i).Comp) (c : GL (Fin D.R.r) D.host.E) (hc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c), ∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hc z hz := by
  first | exact @GlobalTheory.ShareOn.movesAt_nhds_of_dense | exact GlobalTheory.ShareOn.movesAt_nhds_of_dense | (intros; apply GlobalTheory.ShareOn.movesAt_nhds_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandard
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistClassScalar

set_option maxHeartbeats 800000

theorem twist_class_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy
  have hz := GlobalTheory.ClassScalarValue.zCard_eq Λ N D.R.r hLev.2.2
  have hm : Λ.mIdx N D.R.r ≠ 0 := GlobalTheory.ClassScalarValue.mIdx_ne_zero Λ D.R.r (fun h0 => by
    obtain ⟨k, hk⟩ := hLev.1
    omega)
  by_cases hK0 : Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0
  · obtain ⟨a, ha⟩ := GlobalTheory.TwistScalarField.twist_scalar_mem_range D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy hK0
    refine ⟨a, ?_, GlobalTheory.T.twisted_kernel_class_scalar_integral D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hs hy hK0 a ha⟩
    rw [ha, hz]
    have hc : (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hs2 : ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) ^ 2 = ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℂ) ^ D.R.r) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast; rfl
    have hmC : ((Λ.mIdx N D.R.r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm
    push_cast
    rw [GenLat.Ln] at *
    field_simp
    rw [hs2]
  · refine ⟨0, ?_, fun lam _ => ⟨1, fun h1 => lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using isIntegral_zero⟩⟩
    rw [not_not] at hK0
    rw [hK0]
    simp

end GlobalTheory.TwistClassScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductEqFinprodStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) = ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) := by
  first | exact @GlobalTheory.BCT.twOrb_globFn_eq_finprod | exact GlobalTheory.BCT.twOrb_globFn_eq_finprod | (intros; apply GlobalTheory.BCT.twOrb_globFn_eq_finprod <;> assumption)
end

