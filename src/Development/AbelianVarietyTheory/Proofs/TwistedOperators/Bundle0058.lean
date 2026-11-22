import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTrace
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.SmGL.ContraTrace

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype

theorem res_apply (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = (l.1 : Module.Dual ℂ V) v.1 := rfl

theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]

theorem res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)

theorem isAdmissible_contra [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩

theorem smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]

theorem contra_admissible_trace : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1

end GlobalTheory.SmGL.ContraTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
section
namespace GlobalTheory.FlagEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem eq_of_flag_of_hermForm : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  intro α m g e Hm hpos h h' hH bv s hs hh hh'
  have key : ∀ τ, ∀ i : Fin (m τ), h (Pi.single (e.symm ⟨τ, i⟩) 1) = h' (Pi.single (e.symm ⟨τ, i⟩) 1) := by
    intro τ
    let ev : Fin (m τ) → (Fin g → ℂ) := fun j => Pi.single (e.symm ⟨τ, j⟩) 1
    let E : Fin (m τ) → Submodule ℂ (Fin g → ℂ) := fun i => Submodule.span ℂ (ev '' {j | j < i})
    have ha : ∀ i, Submodule.span ℂ (bv τ '' {j | j < i}) ≤ (E i).map h'.toLinearMap := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj : j < i := hj
        have h1 : h' (ev j) ∈ (E i).map h'.toLinearMap :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, hj, rfl⟩)
        have h2 : h' (ev j) - s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := ih j hj (hh' τ j)
          exact Submodule.map_mono (Submodule.span_mono
            (Set.image_mono (fun k (hk : k < j) => (lt_trans hk hj : k < i)))) this
        have h3 : s • bv τ j ∈ (E i).map h'.toLinearMap := by
          have := Submodule.sub_mem _ h1 h2
          simpa using this
        have := Submodule.smul_mem _ s⁻¹ h3
        rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
        exact this
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hon : Set.EqOn h.toLinearMap h'.toLinearMap (E i) := by
        apply LinearMap.eqOn_span'
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj
      set u := h (ev i) - h' (ev i) with hu
      have hu' : u = (h (ev i) - s • bv τ i) - (h' (ev i) - s • bv τ i) := by
        rw [hu]; abel
      have huB : u ∈ Submodule.span ℂ (bv τ '' {j | j < i}) := by
        rw [hu']; exact Submodule.sub_mem _ (hh τ i) (hh' τ i)
      obtain ⟨v, hvE, hv⟩ := ha i huB
      have hv' : h' v = u := hv
      have hhv : h v = u := by
        rw [← hv']; exact hon hvE
      have hx : h (ev i) = h' (ev i) + u := by rw [hu]; abel
      have hE := hH (ev i) v
      rw [hhv, hv', hx] at hE
      have h0 : hermForm Hm u u = 0 := by
        unfold hermForm at hE ⊢
        rw [add_dotProduct] at hE
        simpa using hE
      by_contra hne
      have hne' : u ≠ 0 := by
        intro h0'; apply hne; rw [hu] at h0'; exact sub_eq_zero.mp h0'
      have := hpos u hne'
      rw [h0] at this
      simp at this
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin g)).ext
  intro n
  rw [Pi.basisFun_apply]
  have := key (e n).1 (e n).2
  simpa using this

end GlobalTheory.FlagEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  first | exact @GlobalTheory.AdaptedExp.exists_adapted_exponent | exact GlobalTheory.AdaptedExp.exists_adapted_exponent | (intros; apply GlobalTheory.AdaptedExp.exists_adapted_exponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolution
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

noncomputable section

namespace GlobalTheory.Twist.EuclidCoord

open GlobalTheory.RealWeil.UnitaryOsc

open scoped MatrixOrder in

theorem exists_coord : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  intro ι _ _ H s hH hs hpos
  have hP0 : (0 : Matrix ι ι ℂ) ≤ H * s := hpos.posSemidef.nonneg
  set R : Matrix ι ι ℂ := CFC.sqrt (H * s)
  have hR0 : (0 : Matrix ι ι ℂ) ≤ R := CFC.sqrt_nonneg _
  have hRh : Rᴴ = R := hR0.posSemidef.isHermitian.eq
  have hRR : R * R = H * s := CFC.sqrt_mul_sqrt_self _ hP0
  have hdet : R.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hRR
    rw [det_mul, h0, zero_mul] at e
    exact (hpos.det_pos.ne') (by rw [← e])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hdet.isUnit
  set s₀ : Matrix ι ι ℂ := u.1 * s * (u⁻¹).1 with hs₀
  have hs₀2 : s₀ * s₀ = 1 := by
    simp only [hs₀, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc s, hs, one_mul, Units.mul_inv]

  have hRRs : u.1ᴴ * u.1 * s = H := by
    rw [hu, hRh, hRR, mul_assoc, hs, mul_one]
  have hform : (u⁻¹).1ᴴ * H * (u⁻¹).1 = s₀ := by
    rw [← hRRs]
    calc _ = (u.1 * (u⁻¹).1)ᴴ * (u.1 * s * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = s₀ := by simp [hs₀]
  have hs₀h : s₀ᴴ = s₀ := by
    rw [← hform, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, mul_assoc]
  let E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) :=
    (crd ι).trans (ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1) (fun v => by simp) fun v => by simp)
  have hE : ∀ x, E x = (u⁻¹).1 *ᵥ crd ι x := fun _ => rfl
  refine ⟨E, cplx s₀ hs₀h hs₀2, cplx_cplx s₀ hs₀h hs₀2, fun x => ?_, fun x y => ?_⟩
  · rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec]
    congr 2
    rw [hs₀, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  · rw [omJ_cplx, hE, hE, form_mulVec, hform]

end GlobalTheory.Twist.EuclidCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericLevelOfFrameStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericLevelOfFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  first | exact @GlobalTheory.GenericLevel.exists_isGenericLevel | exact GlobalTheory.GenericLevel.exists_isGenericLevel | (intros; apply GlobalTheory.GenericLevel.exists_isGenericLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevelStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isSymmetricPositionLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by
  first | exact @GlobalTheory.SymLevelExists.exists_isSymLevel | exact GlobalTheory.SymLevelExists.exists_isSymLevel | (intros; apply GlobalTheory.SymLevelExists.exists_isSymLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsParabolicDoubleCosetFunctionEqOneStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicDoubleCosetFunction_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), (∀ g ∈ prX (Cgrp J h), deltaR c g = 1) → ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  first | exact @GlobalTheory.CosetFn.exists_isCosetFn | exact GlobalTheory.CosetFn.exists_isCosetFn | (intros; apply GlobalTheory.CosetFn.exists_isCosetFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepthStatement
section
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  first | exact @GlobalTheory.TensorExpansion.exists_sum_pureTensor | exact GlobalTheory.TensorExpansion.exists_sum_pureTensor | (intros; apply GlobalTheory.TensorExpansion.exists_sum_pureTensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBoxStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ), {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  first | exact @GlobalTheory.BoxCosets.finite_cosets | exact GlobalTheory.BoxCosets.finite_cosets | (intros; apply GlobalTheory.BoxCosets.finite_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrameStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin (s + 1))), ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k, u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX (s + 1) γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) → ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((typeChain t ϖ P μ hμ).lev 0 c H).J 1) : Set (GL (XIx (Fin κ) t 0) k)) = colGroup k κ t ∧ (∀ γ ∈ colGroup k κ t, ∃ hm : embX c γ ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = colChar ψ ϖ γ) ∧ ∀ u ∈ N k (XIx (Fin κ) t 0) c 1, ∀ hm : u ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  first | exact @GlobalTheory.FirstVertexFrame.firstVertex_typeChain | exact GlobalTheory.FirstVertexFrame.firstVertex_typeChain | (intros; apply GlobalTheory.FirstVertexFrame.firstVertex_typeChain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwistStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstVertex_parahoricLevelChain_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  first | exact @GlobalTheory.TwistVertex.firstVertex_twist | exact GlobalTheory.TwistVertex.firstVertex_twist | (intros; apply GlobalTheory.TwistVertex.firstVertex_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinearStatement
section
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
end

