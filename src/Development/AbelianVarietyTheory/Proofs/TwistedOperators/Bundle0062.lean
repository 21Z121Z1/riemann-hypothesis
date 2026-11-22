import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTraceStatement
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  first | exact @GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | exact GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | (intros; apply GlobalTheory.SmGL.ContraTrace.contra_admissible_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreservingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_flag_of_hermForm_preserving : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  first | exact @GlobalTheory.FlagEq.eq_of_flag_of_hermForm | exact GlobalTheory.FlagEq.eq_of_flag_of_hermForm | (intros; apply GlobalTheory.FlagEq.eq_of_flag_of_hermForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolutionStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  first | exact @GlobalTheory.Twist.EuclidCoord.exists_coord | exact GlobalTheory.Twist.EuclidCoord.exists_coord | (intros; apply GlobalTheory.Twist.EuclidCoord.exists_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLatticeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family : ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | exact GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicatorStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_indicator_Cgrp_translate_eq_deltaR_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k), IsCO (prX (Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * ((volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1))).toReal * (m (prX (Cgrp J h))).toReal) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.StepAvg.integral_translate_indicator | exact GlobalTheory.StepAvg.integral_translate_indicator | (intros; apply GlobalTheory.StepAvg.integral_translate_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrpStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCO_prX_Cgrp_and_det_valuation_deltaR_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k, IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  first | exact @GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | exact GlobalTheory.PrCompactOpen.isCO_prX_Cgrp | (intros; apply GlobalTheory.PrCompactOpen.isCO_prX_Cgrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFnStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuotInt_cosetFn_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  first | exact @GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | exact GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | (intros; apply GlobalTheory.CosetQuotInt.isQuotInt_cosetFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeClasses
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem normal_one (c : ℕ) (h : 0 + c = s) : IsNormalRep T ϖ 0 c h 1 := by
  refine ⟨0, 0, fun i => by simp, fun i => zero_mem _, ?_⟩
  rw [lat_bas hb]
  ext y
  simp [mem_normal, mem_latOf_one, mem_pow_zero]

include hϖ hψ hb hs hp hJ

theorem exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by
  induction j with
  | zero =>
    intro c h g hg
    rw [hA.zero] at hg
    obtain rfl : g = 1 := hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h g' hg'
    obtain ⟨g, hg, a, ha, hf⟩ := Set.mem_iUnion₂.1 ((hA.bij j c h).mapsTo hg')
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih _ _ g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c ψ ν _ _ g a hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ hψ he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) a) (hl ▸ om_per hϖ (hp _ _ _) (r * g) a) h0
    obtain ⟨r₃, hr₃, hl₃⟩ := lat_of_coset (hJ _ _ _) ha
    refine ⟨r₂ * r₃⁻¹, mul_mem hr₂ (inv_mem hr₃), e, z, he, hz, ?_⟩
    rw [lat_bas hb, latOf_mul_congr _ hl₃, ← hl₂]
    congr 1
    group

end GlobalTheory.LatClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTripleStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_preimage_embX_mul_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  first | exact @GlobalTheory.RootEx.ProperTriple.proper_triple | exact GlobalTheory.RootEx.ProperTriple.proper_triple | (intros; apply GlobalTheory.RootEx.ProperTriple.proper_triple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUnique
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.QuotIntFJ
open GlobalTheory.QuotInt

open MeasureTheory ValuativeRel Matrix in
set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.QuotIntFJ.quotIntFJ_unique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG _ f z z' hz hz'
  obtain ⟨F₁, hF₁, hf₁, rfl⟩ := hz
  obtain ⟨F₂, hF₂, hf₂, rfl⟩ := hz'
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  have hA := _root_.GlobalTheory.SplitWeil.volGL_haar k n ν
  have hB := _root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  haveI := hA.1; haveI := hA.2.1; haveI := hB.1; haveI := hB.2.1
  set U := _root_.GlobalTheory.RootEx.N k n c (ρ + 1)
  set μU := _root_.GlobalTheory.RootEx.volN ν n c (ρ + 1)
  haveI : μU.IsHaarMeasure := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (ρ + 1)
  haveI : SFinite μU := by
    show SFinite (_root_.GlobalTheory.RootEx.volN ν n c (ρ + 1))
    rw [_root_.GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  set emb := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set col := _root_.GlobalTheory.RootEx.colE (k := k) (n := n) c (ρ + 1)
  let m : GL n k × (U × (n → k)) → GL (n ⊕ Fin c) k := fun p => emb p.1 * ↑p.2.1 * col p.2.2
  have hm : Continuous m := by
    refine (_root_.GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)) |>.mul
      ((_root_.GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp
        (continuous_snd.comp continuous_snd))
  have hSB : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Continuous φ ∧ HasCompactSupport φ :=
    fun φ hφ => ⟨hφ.1.continuous, hφ.2⟩
  have hcs : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∃ D : Set (GL n k × (U × (n → k))),
      IsCompact D ∧ ∀ p, φ (m p) ≠ 0 → p ∈ D := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := _root_.GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hρ hρc (tsupport φ) (hSB φ hφ).2
    exact ⟨D, hD, fun p hp => hDm p (subset_tsupport _ hp)⟩
  set μP := μX.prod (μU.prod (Measure.pi fun _ : n => ν))
  have hint : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      Integrable (fun p => φ (m p)) μP := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp hm).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro hD (fun p hp => by by_contra h; exact hp (hDm p h))
  have hint2 : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∀ g : GL n k,
      Integrable (fun y : U × (n → k) => φ (m (g, y))) (μU.prod (Measure.pi fun _ : n => ν)) := by
    intro φ hφ g
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp (hm.comp (Continuous.prodMk_right g))).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (hD.image continuous_snd)
      (fun y hy => by by_contra h; exact hy ⟨(g, y), hDm _ h, rfl⟩)
  set Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ := fun φ => ∫ (g : GL n k), ∫ (u : U),
      ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU ∂μX with hΛ
  have hΛP : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ φ = ∫ p, φ (m p) ∂μP := by
    intro φ hφ
    rw [integral_prod _ (hint φ hφ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_prod _ (hint2 φ hφ g)).symm
  set R := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ k n c ρ
  have hmR : ∀ p, m p ∈ R := by
    intro p
    have h1 : emb p.1 ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_left : emb.range ≤ _) ⟨p.1, rfl⟩)
    have h2 : (p.2.1 : GL (n ⊕ Fin c) k) ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_right : U ≤ _) p.2.1.2)
    have h3 : col p.2.2 ∈ R := (le_sup_left : _root_.GlobalTheory.RootEx.R k n c ρ ≤ R)
      ((le_sup_right : _root_.GlobalTheory.RootEx.N k n c ρ ≤ _)
        (_root_.GlobalTheory.RootEx.Radical.colE_mem _ (Nat.lt_succ_self ρ)))
    exact R.mul_mem (R.mul_mem h1 h2) h3
  have hadd : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      ∀ ψ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ (φ + ψ) = Λ φ + Λ ψ := by
    intro φ hφ ψ hψ
    rw [hΛP _ (add_mem hφ hψ), hΛP _ hφ, hΛP _ hψ, ← integral_add (hint φ hφ) (hint ψ hψ)]
    rfl
  have hsmul : ∀ (a : ℂ) (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ a * φ g) = a * Λ φ := by
    intro a φ
    simp only [hΛ]
    rw [← integral_const_mul]; congr 1; funext g
    rw [← integral_const_mul]; congr 1; funext u
    rw [← integral_const_mul]
  have hloc : ∀ (φ ψ : GL (n ⊕ Fin c) k → ℂ), (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ := by
    intro φ ψ h
    simp only [hΛ]
    congr 1; funext g; congr 1; funext u; congr 1; funext β
    exact h _ (hmR (g, u, β))
  have hpos : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), (∀ g, φ g = 0 ∨ φ g = 1) →
      (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0 := by
    intro φ hφ h01 ⟨r, hr, hr1⟩
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    have hre : ∀ p, φ (m p) = ((φ (m p)).re : ℂ) := by
      intro p
      rcases h01 (m p) with h | h <;> simp [h]
    rw [hΛP φ hφ, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal]
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μP)
      (x := (x, ⟨u, hu⟩, β)) (Complex.continuous_re.comp ((hSB φ hφ).1.comp hm))
      (HasCompactSupport.intro hD (fun p hp => by
        by_contra h
        exact hp (hDm p (fun h' => h (by simp [h'])))))
      (fun p => by rcases h01 (m p) with h | h <;> simp [h])
      (by show (φ (emb x * u * col β)).re ≠ 0; rw [hr1]; simp)
    exact_mod_cast hpos.ne'
  let H : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∀ φ : GL (n ⊕ Fin c) k → ℂ, (Λ fun g ↦ φ (r * g)) = Λ φ}
      mul_mem' := fun {a b} ha hb φ => by
        have e : (fun g ↦ φ (a * b * g)) = fun g ↦ (fun y ↦ φ (a * y)) (b * g) := by
          funext g; simp only [mul_assoc]
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [e, hb (fun y ↦ φ (a * y)), ha φ]
      one_mem' := fun φ => by simp only [one_mul]
      inv_mem' := fun {a} ha φ => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have := ha (fun y ↦ φ (a⁻¹ * y))
        simp only [inv_mul_cancel_left] at this
        exact this.symm }
  have hembH : ∀ x : GL n k, emb x ∈ H := by
    intro x φ
    simp only [hΛ]
    have e : ∀ (g : GL n k) (u : U) (β : n → k),
        emb x * (emb g * ↑u * col β) = emb (x * g) * ↑u * col β := by
      intro g u β; simp only [map_mul, mul_assoc]
    simp only [e]
    exact integral_mul_left_eq_self (μ := μX)
      (fun g ↦ ∫ (u : U), ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU) x
  have hUH : ∀ v ∈ U, v ∈ H := by
    intro v hv φ
    simp only [hΛ]
    congr 1; funext g
    have hw : (emb g)⁻¹ * v * emb g ∈ U :=
      _root_.GlobalTheory.RootEx.Model.conj_mem hv g
    have e : ∀ (u : U) (β : n → k), v * (emb g * ↑u * col β) =
        emb g * ↑((⟨_, hw⟩ : U) * u) * col β := by
      intro u β; simp only [Subgroup.coe_mul]; group
    simp only [e]
    exact integral_mul_left_eq_self (μ := μU)
      (fun u : U ↦ ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν) (⟨_, hw⟩ : U)
  have hcolH : ∀ γ : n → k, col γ ∈ H := by
    intro γ φ
    simp only [hΛ]
    congr 1; funext g
    set δ : n → k := (↑g⁻¹ : Matrix n n k) *ᵥ γ
    have hconj : emb g⁻¹ * col γ * (emb g⁻¹)⁻¹ = col δ :=
      _root_.GlobalTheory.RootEx.QuotStep.conj_colE (ρ + 1) g⁻¹ γ
    have e : ∀ (u : U) (β : n → k), col γ * (emb g * ↑u * col β) =
        emb g * (col δ * ↑u * (col δ)⁻¹) * col (δ + β) := by
      intro u β
      have hc : col (δ + β) = col δ * col β := (_root_.GlobalTheory.RootEx.FourierJacobiGroup.colE_add (ρ + 1) δ β).symm
      rw [hc, ← hconj]
      simp only [map_inv, inv_inv]
      group
    simp only [e]
    have hβ : ∀ y : GL (n ⊕ Fin c) k,
        ∫ (β : n → k), φ (emb g * y * col (δ + β)) ∂(Measure.pi fun _ ↦ ν) =
        ∫ (β : n → k), φ (emb g * y * col β) ∂(Measure.pi fun _ ↦ ν) := fun y =>
      integral_add_left_eq_self (fun β ↦ φ (emb g * y * col β)) δ
    simp only [hβ]
    exact _root_.GlobalTheory.RootEx.ConjVol.integral_conj_colE k n c ρ hρ hρc ν δ
      (fun y ↦ ∫ (β : n → k), φ (emb g * y * col β) ∂Measure.pi fun _ ↦ ν)
  have hinv : ∀ r ∈ R, ∀ (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ φ (r * g)) = Λ φ := by
    intro r hr
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    exact H.mul_mem (H.mul_mem (hembH x) (hUH u hu)) (hcolH β)
  have hF : (F₁ - F₂) ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) := sub_mem hF₁ hF₂
  have hG : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Integrable φ μG :=
    fun φ hφ => (hSB φ hφ).1.integrable_of_hasCompactSupport (hSB φ hφ).2
  have hΛf : ∀ F ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      (∀ h, f h = ∫ (g : GL n k), ∫ (u : U), ∫ (β : n → k), F (emb g * ↑u * col β * h)
        ∂(Measure.pi fun _ ↦ ν) ∂μU ∂μX) → ∀ h, (Λ fun g ↦ F (g * h)) = f h := by
    intro F _ hf h
    rw [hf h]
  have key := _root_.GlobalTheory.QuotInt.integral_eq_zero_of_avg μG _ hB.2.2.2.2.1 hB.2.2.2.1
    R Λ hadd hsmul hloc hinv hpos hF (fun h => by
      have e : (fun g => (F₁ - F₂) (g * h)) =
          (fun g => F₁ (g * h)) + (fun g => (-1 : ℂ) * F₂ (g * h)) := by
        funext g; simp [sub_eq_add_neg]
      have hneg : (fun g => (-1 : ℂ) * F₂ (g * h)) ∈
          _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) :=
        (_root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)).smul_mem (-1 : ℂ)
          (_root_.GlobalTheory.QuotInt.sb_right hF₂ h)
      rw [e, hadd _ (_root_.GlobalTheory.QuotInt.sb_right hF₁ h) _ hneg,
        hsmul (-1) (fun g => F₂ (g * h)), hΛf F₁ hF₁ hf₁ h, hΛf F₂ hF₂ hf₂ h]
      ring)
  have hsub : ∫ g, (F₁ - F₂) g ∂μG = ∫ g, F₁ g ∂μG - ∫ g, F₂ g ∂μG :=
    integral_sub (hG _ hF₁) (hG _ hF₂)
  rw [hsub] at key
  exact sub_eq_zero.1 key

end GlobalTheory.QuotIntFJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulFrameMulFrameInvApply
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem smul_frame_mul_frame_inv_apply {k : Type} [Field k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (a : k) (b b' : ℕ → kˣ)
    (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r : n ⊕ Fin c) (s : n' ⊕ Fin c') :
    (a • ((frame n c b).val * y * ((frame n' c' b')⁻¹).val)) r s =
      a * Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹) s * y r s := by
  have h1 : (frame n c b).val =
      Matrix.diagonal (Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k))) := by
    rw [← Matrix.fromBlocks_diagonal]; rfl
  have h2 : ((frame n' c' b')⁻¹).val =
      Matrix.diagonal (Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp only [← Units.val_inv_eq_inv_val]
    rfl
  rw [h1, h2, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring

theorem opE_rescale_frame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (α β₀ : kˣ) (b' : ℕ → kˣ) (ν νs : Measure k), (∀ i, 1 ≤ i → i ≤ c → b' i / b' (i + 1) = β₀) → ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ (ψ : AddChar k Circle) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k), opE ψ ν p Ψ x = C * opE (ψ.mulShift (β₀ : k)) νs p (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => Ψ ((α : k) • ((frame n c fun i => α⁻¹ * b' i).val * y * ((frame n' (c + 1) b')⁻¹).val))) (((α⁻¹ : kˣ) : k) • x) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p α β₀ b' ν νs hb hν hνs
  let d : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → kˣ := fun rs =>
    α * Sum.elim (fun _ : n => 1) (fun i : Fin c => α⁻¹ * b' (i.val + 1)) rs.1.1 *
      (Sum.elim (fun _ : n' => 1) (fun i : Fin (c + 1) => b' (i.val + 1)) rs.1.2)⁻¹
  obtain ⟨C, hC, hF⟩ := @GlobalTheory.T.haar_measure_pi_change_constant k _ _ _ _ _ _ _ (@Subtype.fintype _ _ (Classical.decPred _) _) ν νs d hν hνs
  refine ⟨C, hC, fun ψ Ψ x => ?_⟩
  unfold opE
  rw [hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  congr 1
  · congr 1
    ext r q
    rw [smul_frame_mul_frame_inv_apply]
    by_cases h : Free p (r, q)
    · rcases r with r | r <;> rcases q with q | q
      · exact absurd h (by simp [Free])
      · simp [affPt, basePt, h, d]
      · simp [affPt, basePt, h, d]
      · have : r.val ≠ q.val := by simp only [Free] at h; omega
        simp [affPt, basePt, h, d, this]
    · rcases r with r | r <;> rcases q with q | q
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · by_cases h' : r.val = q.val <;> simp [affPt, basePt, h, h']
  · rw [AddChar.mulShift_apply, mul_neg]
    congr 3
    unfold ch
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by simp [Free]
    rw [← hb (i.val + 1) (by omega) (by omega)]
    simp [affPt, basePt, h, d, div_eq_mul_inv]

end GlobalTheory.IdealChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolicStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionLevel_shape_on_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), IsSymLevel ψ ϖ ρ P → ((∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) := by
  first | exact @GlobalTheory.SymShape.sym_shape | exact GlobalTheory.SymShape.sym_shape | (intros; apply GlobalTheory.SymShape.sym_shape <;> assumption)
end

