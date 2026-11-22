import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition : ∀ (D : D7) (S S₀ : HSp D) (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)), μ.IsHaarMeasure → (Measure.map d.emb0 μ).IsHaarMeasure := by
  first | exact @GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure | exact GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure | (intros; apply GlobalTheory.HaarEmb.map_wittEmbedding_zero_rank_isHaarMeasure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixCoeffRightTranslateDefiniteFormScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealCoef

open scoped ComplexConjugate ComplexOrder

theorem petersson_conj {D : D7} {V : HSp D} (m : Measure (GA D V)) (φ ψ : GA D V → ℂ) :
    GlobalTheory.Cusp.petersson V m φ ψ = conj (GlobalTheory.Cusp.petersson V m ψ φ) := by
  simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
  rw [← integral_conj]
  congr 1
  funext q
  simp [mul_comm]

theorem rcoef_of_fun {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (m : Measure (GA D V)) (hm : m.IsHaarMeasure)
    (Y : GA D V → c.W) (hYc : Continuous Y) (hYi : ∀ γ ∈ GQ V, ∀ h, Y (γ * h) = Y h) {K : Set (GA D V)}
    (hK : IsCompact K) (hKc : ∀ h, ∃ γ ∈ GQ V, ∃ k ∈ K, h = γ * k)
    (hsh : ∀ b ∈ GinfC V, ∀ g, Y (g * b) = c.ρ b⁻¹ (Y g)) :
    ∃ z : ℂ, (∀ w : c.W, ∀ b ∈ GinfC V,
      GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, Y g⟫_ℂ) (fun g => ⟪w, Y g⟫_ℂ) b = z * ⟪c.ρ b w, w⟫_ℂ) ∧ (Y ≠ 0 → z ≠ 0) := by
  haveI := hm
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds V m hm
  let φ : c.W → GA D V → ℂ := fun x g => ⟪x, Y g⟫_ℂ
  have hφL : ∀ x, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (φ x) := fun x γ hγ g => by
    simp only [φ, hYi γ hγ g]
  have hφc : ∀ x, Continuous (φ x) := fun x => continuous_const.inner hYc
  have hφ2 : ∀ x, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) m (φ x) := fun x => by
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hφc x).continuousOn
    refine GlobalTheory.Cusp.memL2_of_bounded_continuous_invariant (hφL x) (hφc x) (C := C) fun h => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc h
    rw [e, hφL x γ hγ k]
    exact hCb k hk
  have hshift : ∀ b ∈ GinfC V, ∀ x, rTr V b (φ x) = φ (c.ρ b x) := by
    intro b hb x
    funext g
    show ⟪x, Y (g * b)⟫_ℂ = ⟪c.ρ b x, Y g⟫_ℂ
    rw [hsh b hb g, ← hc.2.1 b x (c.ρ b⁻¹ (Y g)), GlobalTheory.DefiniteEnd.rho_inv_cancel]
  have hadd : ∀ x x', φ (x + x') = φ x + φ x' := fun x x' => funext fun g => inner_add_left _ _ _
  have hsmul : ∀ (a : ℂ) x, φ (a • x) = (starRingEnd ℂ a) • φ x := fun a x => funext fun g => inner_smul_left _ _ _
  let B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x x' => GlobalTheory.Cusp.petersson V m (φ x) (φ x'))
    (fun x x' y => by rw [hadd]; exact GlobalTheory.Cusp.petersson_add_left (hφ2 x) (hφ2 x') (hφ2 y))
    (fun a x y => by rw [hsmul]; exact GlobalTheory.Cusp.petersson_smul_left _ _ _)
    (fun x y y' => by
      rw [petersson_conj m (φ x) (φ (y + y')), hadd, GlobalTheory.Cusp.petersson_add_left (hφ2 y) (hφ2 y') (hφ2 x), map_add,
        ← petersson_conj m (φ x) (φ y), ← petersson_conj m (φ x) (φ y')])
    (fun a x y => by
      rw [petersson_conj m (φ x) (φ (a • y)), hsmul, GlobalTheory.Cusp.petersson_smul_left, map_mul,
        ← petersson_conj m (φ x) (φ y), Complex.conj_conj, RingHom.id_apply, smul_eq_mul])
  have hB : ∀ x x', B x x' = GlobalTheory.Cusp.petersson V m (φ x) (φ x') := fun _ _ => rfl
  have hinv : ∀ u ∈ GinfC V, ∀ x x', B (c.ρ u x) (c.ρ u x') = B x x' := by
    intro u hu x x'
    rw [hB, hB, ← hshift u hu, ← hshift u hu]
    exact GlobalTheory.Cusp.petersson_rTr (hφ2 x) (hφ2 x') u
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D V c hc B hinv
  refine ⟨z, fun w b hb => ?_, fun hY hz0 => ?_⟩
  · show GlobalTheory.Cusp.petersson V m (rTr V b (φ w)) (φ w) = _
    rw [hshift b hb, ← hB]
    exact hz _ _
  · apply hY
    have h0 : ∀ x, φ x = 0 := by
      intro x
      by_contra hne
      have hpos := GlobalTheory.Cusp.petersson_self_pos (hφ2 x) (hφc x) hne
      have h1 : GlobalTheory.Cusp.petersson V m (φ x) (φ x) = 0 := by
        rw [← hB, hz x x, hz0, zero_mul]
      rw [h1, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    funext g
    exact inner_self_eq_zero.1 (congrFun (h0 (Y g)) g)

set_option maxHeartbeats 1000000 in

theorem rcoef_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (m : Measure (GA D (Vc D i))), m.IsHaarMeasure → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, R.extV i t y g⟫_ℂ) (fun g => ⟪w, R.extV i t y g⟫_ℂ) b = z * ⟪(R.cV i).ρ b w, w⟫_ℂ) ∧ (y ≠ 0 → z ≠ 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t y m hm
  have hmod := hC.models
  have hc : (R.cV i).Is := hmod.cV i
  have hx := (hmod.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hp : (Vc D i).IsPosDef := hmod.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hYc : Continuous (R.extV i t y) := GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) hc (R.βV i) (R.datVt i t) hx
  have hYi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h := GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hsh : ∀ b ∈ GinfC (Vc D i), ∀ g, R.extV i t y (g * b) = (R.cV i).ρ b⁻¹ (R.extV i t y g) :=
    fun b hb g => GlobalTheory.DownLift.DefiniteComp.extV_mul_inf R i t y hb g
  have key := rcoef_of_fun (R.cV i) hc m hm (R.extV i t y) hYc hYi hK hKc hsh
  refine ⟨key.choose, key.choose_spec.1, fun hy => key.choose_spec.2 fun hY0 => hy ?_⟩
  have hf0 : (R.HV i t).e y = 0 := by
    funext k
    obtain ⟨g, rfl⟩ := (finHom (Vc D i)).rangeRestrict_surjective k
    have e : (R.cV i).ρ g⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict g)) = 0 := congrFun hY0 g
    have e2 := congrArg ((R.cV i).ρ g) e
    rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at e2
    exact e2.trans (LinearMap.map_zero _)
  exact (hmod.HV i t).1 (hf0.trans ((R.HV i t).e.map_zero).symm)

end GlobalTheory.Core.Rk.RealCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSuppImp

theorem mxAt_of_isHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {m n : ℕ} (x : Mx D m n), IsHalf (q.e + cA D q.e) x → MxAt (· = q.v) x := by
  intro D k _ _ _ _ q m n x hx
  exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q m n x hx

end GlobalTheory.FinPl.SplitHalfSuppImp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegerIffOfEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Filter Topology

namespace GlobalTheory.PlaceSplitPt

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
  (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem mem_integer_iff_of_equiv (σ : K ≃+* K') (h1 : Continuous σ) (h2 : Continuous σ.symm) (a : K) :
    a ∈ 𝒪[K] ↔ σ a ∈ 𝒪[K'] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  constructor
  · intro h
    refine le_one_of_map σ.symm.toRingHom h2 ?_
    change valuation K (σ.symm (σ a)) ≤ 1
    rwa [σ.symm_apply_apply]
  · exact le_one_of_map σ.toRingHom h1

end Val

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]

theorem ι_one (p : Place D k) : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]

section Chart

variable {v : Pl D} (p : Place D k) (he : SplitAt D v p.e)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def toFv : k ≃+* Fv D.host.F v where
  toFun a := comp he (p.ι a)
  invFun b := p.π (sec D v p.e b)
  left_inv a := by
    change p.π (sec D v p.e (comp he (p.ι a))) = a
    rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι, p.π_ι]
  right_inv b := by
    change comp he (p.ι (p.π (sec D v p.e b))) = b
    rw [p.ι_π, map_mul, comp_self, one_mul, GlobalTheory.LocMod.SplitCompl.comp_sec]
  map_mul' x y := by
    change comp he (p.ι (x * y)) = comp he (p.ι x) * comp he (p.ι y)
    rw [ι_mul, map_mul]
  map_add' x y := by
    change comp he (p.ι (x + y)) = comp he (p.ι x) + comp he (p.ι y)
    rw [map_add, map_add]

theorem continuous_toFv : Continuous (toFv p he) := (continuous_comp he).comp p.cont_ι

theorem continuous_toFv_symm : Continuous (toFv p he).symm := p.cont_π.comp continuous_sec

include he in
theorem int_iff (a : k) : a ∈ 𝒪[k] ↔ finPart D (p.ι a) ∈ intAE D := by
  rw [mem_integer_iff_of_equiv (toFv p he) (continuous_toFv p he) (continuous_toFv_symm p he) a,
    GlobalTheory.LocMod.SplitCompl.int_iff_sec he]
  change finPart D (sec D v p.e (comp he (p.ι a))) ∈ intAE D ↔ _
  rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι]

end Chart

theorem exists_splitPt : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k), ∃ q : GlobalTheory.FinPl.SplitPt D k, GlobalTheory.LocMod.Place.ofSplitPt q = p := by
  intro D k _ _ _ _ p
  obtain ⟨-, -, v, ε, hε, hs⟩ := p.split
  have he : SplitAt D v p.e := splitAt_of p.split hε hs
  exact ⟨⟨v, p.e, p.split, ⟨ε, hε, hs⟩, p.π, p.ι, p.π_ι, p.ι_π, p.cont_π, p.cont_ι, int_iff p he⟩, rfl⟩

end GlobalTheory.PlaceSplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabMove

variable {D : D7}

def IntG (V : HSp D) (g : GA D V) : Prop := ∀ i j, finPart D (Formalism.L2.Theta.mt V g i j) ∈ intAE D

theorem IntG.inv {V : HSp D} (hV : V.gram = 1) {g : GA D V} (h : IntG V g) : IntG V g⁻¹ := by
  have e : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at e
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have e3 : Formalism.L2.Theta.mt V g⁻¹ = ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ := by
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V g⁻¹), ← e, Matrix.mul_assoc, e2, Matrix.mul_one]
  intro i j
  rw [e3, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MovedIdem.finPart_cA]
  exact GlobalTheory.MovedIdem.sigR_mem_intAE (h j i)

theorem intG_of_moves {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V}
    (h : GlobalTheory.AdForm.Moves V hn k (Formalism.L2.Col.stdLat D.host.E n)) : IntG V k⁻¹ := by
  subst hn
  intro i j
  have h1 := (h (Pi.single j 1)).1 (fun a _ => by
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _) i
  refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
  have e : (fun a => eToEAf D ((Pi.single j 1 : Fin V.rank → D.host.E) a)) = Pi.single j 1 := by
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [e, Matrix.mulVec_single_one] at h1
  exact h1

theorem mem_hatV_iff {n : ℕ} (u : Fin n → GlobalTheory.Ker.AfE D) :
    u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) ↔ ∀ i, u i ∈ intAE D := by
  constructor
  · intro hu i
    induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (GlobalTheory.SW.Base.mem_stdL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hu
    rw [← Finset.univ_sum_single u]
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, (Pi.single i z : Fin n → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (GlobalTheory.SW.Base.mem_stdL _).2 fun b => ?_, ?_⟩
        · rw [Pi.single_apply]
          split_ifs
          · exact x.2
          · exact isIntegral_zero
        · funext b
          rw [Pi.single_apply, Pi.single_apply]
          split_ifs
          · rfl
          · rw [TensorProduct.tmul_zero]
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
      | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy
    exact key _ (hu i)

theorem isMov_of_intG {V : HSp D} {k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) (GlobalTheory.SW.stdL D.host.E V.rank) (GlobalTheory.SW.stdL D.host.E V.rank) := by
  have key : ∀ g, IntG V g → ∀ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank),
      GlobalTheory.Ker.fmt V g *ᵥ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank) := fun g hg u hu =>
    (mem_hatV_iff _).2 fun i => sum_mem (t := Finset.univ) fun j _ => GlobalTheory.GeoActCompare.TameConj.mul_mem_intAE (hg i j) ((mem_hatV_iff _).1 hu j)
  intro u
  refine ⟨fun hu => ⟨_, key _ h' u hu, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_mulVec, GlobalTheory.Ker.fmt, GlobalTheory.Ker.fmt, ← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel,
      GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    exact key _ h u₀ h0

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]

theorem moves_of_mul {V : HSp D} {n : ℕ} (hn : V.rank = n) {g k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) {N}
    (hN : GlobalTheory.AdForm.Moves V hn (g * k) N) : GlobalTheory.AdForm.Moves V hn g N := by
  have key : ∀ a, IntG V a → ∀ u : Fin n → EF D, (∀ i, u i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ i, (finM V hn a *ᵥ u) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha u hu i =>
    sum_mem (t := Finset.univ) fun j _ => mul_mem
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (ha ((finCongr hn).symm i) ((finCongr hn).symm j))) (hu j)
  intro x
  rw [hN x]
  constructor
  · intro hx
    have := key k h _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  · intro hx
    have := key _ h' _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, ← _root_.mul_inv_rev] at this

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem unramAt_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c χ hc v ε hv.1 fun P hP => hu P fun k hk => ?_
  obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
  exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem coe_stdL (n : ℕ) : (GlobalTheory.SW.stdL D.host.E n : Set (Fin n → D.host.E)) = intVec D n :=
  Set.ext fun x => GlobalTheory.SW.Base.mem_stdL x

theorem om_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {μ : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T μ μ om)
    (hu : ∀ v ε, GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.UnramAt ε μ) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f) {k : GA D S} {k' : GA D T}
    (hk : k ∈ GfC S) (hk' : k' ∈ GfC T) (a : IntG S k) (a' : IntG T k') :
    ∃ x y, IsDetRoot S k x ∧ IsDetRoot T k' y ∧ om (k, k') f = (((μ x)⁻¹ * μ y : Circle) : ℂ) • f := by
  have m := isMov_of_intG a (a.inv hP.gS)
  have m' := isMov_of_intG a' (a'.inv hP.gT)
  have sS := GlobalTheory.Ker.Base.selfDualC_stdL hP.gS
  have sT := GlobalTheory.Ker.Base.selfDualC_stdL hP.gT
  obtain ⟨x, hx, rx⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D S _ sS k hk m
  obtain ⟨y, hy, ry⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T _ sT k' hk' m'
  have hc : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hV]
      simp
    rw [this]
    exact GlobalTheory.AdTh.isCartanInv_one_splitStab _
  refine ⟨x, y, rx, ry, GlobalTheory.FinVac.om_vacuum_finite D S T ψ θ hP.inf hP.sigS hP.sigT μ μ om hW
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) (fun v ε hv => ⟨hu v ε hv, hu v ε hv⟩) (fun _ => 1) (fun _ => 1)
    (hc S hP.gS) (hc T hP.gT) _ _ sS sT f ?_ k hk k' hk' m m' x y hx hy rx ry⟩
  rwa [coe_stdL, coe_stdL]

theorem xiN_smul (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ) (c : ℂ)
    (f : WO S T → ℂ) : xiN θ S T hS hT δ sc (c • f) = fun z => c * xiN θ S T hS hT δ sc f z := by
  funext z
  simp only [xiN, Pi.smul_apply, smul_eq_mul]
  ring

theorem moveAt_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat B.fields.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat B.fields.E _) → A.MoveAt θ i hi c₀ (g * k) (h * k') := by
  intro B X I l Z w u A ψ θ hA i hi c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdSteps.stdPair_steps I l Z w u A ψ θ hA i hi).1
  have hW := hA.om i hi
  have b := intG_of_moves _ mk
  have b' := intG_of_moves _ mk'
  have a := b.inv hP.gS
  have a' := b'.inv hP.gT
  rw [inv_inv] at a a'
  obtain ⟨x₁, y₁, rx, ry, e⟩ := om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq (hA.chr ⟨i, hi⟩) (I.C.isMu0 ⟨i, hi⟩).unr hv) (hA.vac i hi) hk hk' a a'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (moves_of_mul _ a b hN) (moves_of_mul _ a' b' hN') x₀ y₀ sx sy
  have ex := root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (xiN_smul _ _ _ _ _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  simp only [ColDat.xiS] at e1
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalLevelFixesFockVectorsFiniteDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  first | exact @GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | exact GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | (intros; apply GlobalTheory.PrincipalLevelFock.levW_fix_ptAt <;> assumption)
end

